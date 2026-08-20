//! LLM coded helper, TODO clean it up and make it its own library for
//! testcrates to use

use std::{fs, path::PathBuf, process::ExitCode};

use clap::Parser;

/// The start of the marker comment that precedes each example
const MARKER: &str = "// SYNC";

/// The workspace root, which the defaults are relative to
fn workspace_dir() -> PathBuf {
    let mut res = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    // the manifest directory is `testcrate`
    res.pop();
    res
}

/// Syncs the examples of the examples file into the doc tests scattered
/// through the `triple_arena` sources, so that they only ever have to be
/// edited in one place.
///
/// Every example is preceded by a marker comment
///
///     // SYNC(<file relative to the source directory>, <item name>)
///
/// and the body of the example replaces the contents of the doc test attached
/// to the item of that name in that file. The item name only has to be unique
/// among the items that have doc tests within that one file, so this does not
/// care about doc tests being added or reordered.
///
/// Because `format_code_in_doc_comments` is enabled and the `/// ` prefix eats
/// into the line budget, use `just sync_examples`, which runs `cargo fmt` and
/// the doc tests afterwards.
#[derive(Debug, Parser)]
#[command(verbatim_doc_comment)]
struct Args {
    /// Only report whether anything is out of sync, exiting with a failure code
    /// if it is, instead of rewriting any files
    #[arg(long)]
    check: bool,
    /// The file that the examples and their markers are read from
    #[arg(
        long,
        value_name = "FILE",
        default_value_os_t = workspace_dir().join("testcrate/tests/examples.rs")
    )]
    examples: PathBuf,
    /// The directory that the file of a marker is relative to
    #[arg(
        long,
        value_name = "DIR",
        default_value_os_t = workspace_dir().join("triple_arena/src")
    )]
    src_dir: PathBuf,
    /// `max_width` from `.rustfmt.toml`. Doc comment code is formatted with the
    /// prefix counting against this, so a line that fits in the examples file
    /// does not necessarily fit in the doc test.
    #[arg(long, value_name = "COLUMNS", default_value_t = 100)]
    max_width: usize,
}

/// One example of the examples file and where it goes
struct Example {
    /// The test function name, only used for messages
    name: String,
    /// The target source file, relative to `Args::src_dir`
    file: String,
    /// The name of the item that the target doc test is attached to
    item: String,
    /// The lines of the function body, still indented by the 4 spaces of being
    /// inside the function
    body: Vec<String>,
    /// The line in the examples file that the marker is on, for messages
    marker_line: usize,
}

/// One ```` ``` ````  delimited Rust doc test of a source file
struct DocTest {
    /// Index of the opening fence line
    open: usize,
    /// Index of the closing fence line
    close: usize,
    /// The indentation and doc comment marker, e.g. `    ///`
    prefix: String,
}

/// Splits a doc comment line into everything up to and including the `///` or
/// `//!`, and the content after a single optional space
fn split_doc(line: &str) -> Option<(&str, &str)> {
    let trimmed = line.trim_start();
    let marker = if trimmed.starts_with("///") {
        "///"
    } else if trimmed.starts_with("//!") {
        "//!"
    } else {
        return None;
    };
    let split = line
        .len()
        .wrapping_sub(trimmed.len())
        .wrapping_add(marker.len());
    let (prefix, content) = line.split_at(split);
    Some((prefix, content.strip_prefix(' ').unwrap_or(content)))
}

/// Whether the line opens a raw string literal that continues onto the next
/// line. Note that this only handles the `r#"` form that the examples use.
fn opens_raw_string(line: &str) -> bool {
    match line.rfind("r#\"") {
        Some(i) => !line[i.wrapping_add(3)..].contains("\"#"),
        None => false,
    }
}

fn parse_examples(src: &str) -> Result<Vec<Example>, String> {
    let lines: Vec<&str> = src.lines().collect();
    let mut res: Vec<Example> = vec![];
    let mut i = 0usize;
    while i < lines.len() {
        let Some(rest) = lines[i].strip_prefix(MARKER) else {
            i = i.wrapping_add(1);
            continue;
        };
        let marker_line = i.wrapping_add(1);
        // a line that starts like a marker but does not parse is a typo, not
        // something to skip over
        let syntax_err = || format!("line {marker_line}: expected `{MARKER}(<file>, <item name>)`");
        let Some((file, item)) = rest
            .trim_end()
            .strip_prefix('(')
            .and_then(|rest| rest.strip_suffix(')'))
            .and_then(|fields| fields.split_once(','))
        else {
            return Err(syntax_err());
        };
        let (file, item) = (file.trim(), item.trim());
        if file.is_empty() || item.is_empty() || item.contains(',') {
            return Err(syntax_err());
        }
        // only attributes and doc comments are allowed between the marker and the
        // test function
        let mut j = i.wrapping_add(1);
        loop {
            if j >= lines.len() {
                return Err(format!(
                    "line {marker_line}: reached the end of the file looking for the test function"
                ));
            }
            if lines[j].starts_with("fn ") {
                break;
            }
            let trimmed = lines[j].trim_start();
            if !(trimmed.is_empty() || trimmed.starts_with("#[") || trimmed.starts_with("///")) {
                return Err(format!(
                    "line {marker_line}: the marker is not attached to a test function"
                ));
            }
            j = j.wrapping_add(1);
        }
        let name = lines[j]
            .trim_start_matches("fn ")
            .split('(')
            .next()
            .unwrap_or_default()
            .to_owned();
        // the body ends at the closing brace of the function, which is the only
        // thing at the start of a line
        let mut k = j.wrapping_add(1);
        let mut body = vec![];
        loop {
            if k >= lines.len() {
                return Err(format!(
                    "line {marker_line}: the test function `{name}` is not closed"
                ));
            }
            if lines[k] == "}" {
                break;
            }
            body.push(lines[k].to_owned());
            k = k.wrapping_add(1);
        }
        res.push(Example {
            name,
            file: file.to_owned(),
            item: item.to_owned(),
            body,
            marker_line,
        });
        i = k.wrapping_add(1);
    }
    Ok(res)
}

/// Finds every Rust doc test of a source file, pairing the code fences the same
/// way that Markdown does so that ```` ```text ```` blocks are skipped over
/// rather than confused for one
fn find_doc_tests(lines: &[String]) -> Result<Vec<DocTest>, String> {
    let mut res = vec![];
    // (line, prefix, info string)
    let mut open: Option<(usize, String, String)> = None;
    for (i, line) in lines.iter().enumerate() {
        let Some((prefix, content)) = split_doc(line) else {
            continue;
        };
        let Some(info) = content.trim_end().strip_prefix("```") else {
            continue;
        };
        match open.take() {
            None => open = Some((i, prefix.to_owned(), info.trim().to_owned())),
            Some((start, prefix, info0)) => {
                if !info.trim().is_empty() {
                    return Err(format!(
                        "line {}: expected a closing fence",
                        i.wrapping_add(1)
                    ));
                }
                if info0.is_empty() || (info0 == "rust") {
                    res.push(DocTest {
                        open: start,
                        close: i,
                        prefix,
                    });
                }
            }
        }
    }
    if let Some((start, ..)) = open {
        return Err(format!(
            "line {}: this code fence is never closed",
            start.wrapping_add(1)
        ));
    }
    Ok(res)
}

/// The name of the item that the doc test ending at `close` is attached to.
/// Returns `None` if the following declaration does not declare a name, such as
/// for an `impl` block.
fn owner_name(lines: &[String], close: usize) -> Option<String> {
    fn is_item_keyword(token: &str) -> bool {
        matches!(
            token,
            "fn" | "struct" | "enum" | "trait" | "type" | "const" | "static" | "mod" | "union"
        )
    }
    // skip the rest of the doc comment, any attributes, and blank lines
    let mut i = close.wrapping_add(1);
    while i < lines.len() {
        let trimmed = lines[i].trim_start();
        if trimmed.is_empty() || trimmed.starts_with("//") || trimmed.starts_with("#[") {
            i = i.wrapping_add(1);
        } else {
            break;
        }
    }
    // generic parameter lists can make the declaration span many lines, so join
    // them up to wherever the body or the `;` starts
    let mut decl = String::new();
    for _ in 0..24 {
        if i >= lines.len() {
            break;
        }
        let trimmed = lines[i].trim();
        decl.push(' ');
        decl.push_str(trimmed);
        if trimmed.contains('{') || trimmed.ends_with(';') {
            break;
        }
        i = i.wrapping_add(1);
    }
    // the first identifier after the item keyword, skipping over things like the
    // `fn` of a `const fn`
    let mut after_keyword = false;
    for token in decl
        .split(|c: char| !(c.is_alphanumeric() || (c == '_')))
        .filter(|token| !token.is_empty())
    {
        if after_keyword && !is_item_keyword(token) {
            return Some(token.to_owned());
        }
        after_keyword = is_item_keyword(token);
    }
    None
}

/// Turns the body of an example into the doc comment lines that go between the
/// code fences
fn body_to_doc(body: &[String], prefix: &str) -> Vec<String> {
    let mut res = vec![];
    // the interiors of multi line raw strings are at absolute columns and must
    // not be dedented
    let mut in_raw = false;
    for line in body {
        let code = if in_raw {
            if line.contains("\"#") {
                in_raw = false;
            }
            line.as_str()
        } else {
            let dedented = line.strip_prefix("    ").unwrap_or(line);
            if opens_raw_string(dedented) {
                in_raw = true;
            }
            dedented
        };
        if code.is_empty() {
            res.push(prefix.to_owned());
        } else {
            res.push(format!("{prefix} {code}"));
        }
    }
    res
}

fn run(args: &Args) -> Result<ExitCode, String> {
    let examples_file = args.examples.display();
    let src = fs::read_to_string(&args.examples)
        .map_err(|e| format!("could not read {examples_file}: {e}"))?;
    let examples = parse_examples(&src).map_err(|e| format!("{examples_file}: {e}"))?;
    if examples.is_empty() {
        return Err(format!("no `{MARKER}` markers found in {examples_file}"));
    }
    // group by target file so that files with more than one example are only read
    // and written once, and so that two examples that would silently fight over
    // the same doc test are caught before anything is written
    let mut groups: Vec<(&str, Vec<&Example>)> = vec![];
    for example in &examples {
        match groups.iter_mut().find(|(file, _)| *file == example.file) {
            Some((_, group)) => {
                if let Some(other) = group.iter().find(|other| other.item == example.item) {
                    return Err(format!(
                        "{examples_file}: `{}` on line {} and `{}` on line {} both target `{}` in \
                         `{}`",
                        other.name,
                        other.marker_line,
                        example.name,
                        example.marker_line,
                        example.item,
                        example.file
                    ));
                }
                group.push(example);
            }
            None => groups.push((&example.file, vec![example])),
        }
    }

    let mut out_of_sync = 0usize;
    let mut synced = 0usize;
    let mut warnings = vec![];
    for (file, group) in &groups {
        let path = args.src_dir.join(file);
        let text = fs::read_to_string(&path)
            .map_err(|e| format!("could not read {}: {e}", path.display()))?;
        let ends_with_newline = text.ends_with('\n');
        let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
        let mut changed = false;
        for example in group {
            // the doc tests have to be refound for each example, because splicing in a
            // body of a different length shifts every line index after it
            let doc_tests = find_doc_tests(&lines).map_err(|e| format!("{file}: {e}"))?;
            let mut matches = doc_tests.iter().filter(|doc_test| {
                owner_name(&lines, doc_test.close).as_deref() == Some(&example.item)
            });
            let Some(doc_test) = matches.next() else {
                return Err(format!(
                    "{examples_file} line {}: no doc test attached to an item named `{}` in \
                     `{file}`",
                    example.marker_line, example.item
                ));
            };
            if matches.next().is_some() {
                return Err(format!(
                    "{examples_file} line {}: more than one doc test in `{file}` is attached to \
                     an item named `{}`",
                    example.marker_line, example.item
                ));
            }
            let (open, close, prefix) = (doc_test.open, doc_test.close, doc_test.prefix.clone());
            let new = body_to_doc(&example.body, &prefix);
            for line in &new {
                if line.chars().count() > args.max_width {
                    warnings.push(format!(
                        "`{}` has a line that is {} columns wide as a doc test, over the \
                         `max_width` of {}, so `cargo fmt` may rewrap it and leave it out of \
                         sync. Shorten it in {examples_file}:\n    {}",
                        example.name,
                        line.chars().count(),
                        args.max_width,
                        line.trim()
                    ));
                }
            }
            if lines[open.wrapping_add(1)..close] == new[..] {
                synced = synced.wrapping_add(1);
                continue;
            }
            out_of_sync = out_of_sync.wrapping_add(1);
            if args.check {
                println!("out of sync: `{}` -> {file}", example.name);
            } else {
                println!(
                    "updated: `{}` -> {file} (line {})",
                    example.name,
                    open.wrapping_add(1)
                );
                lines.splice(open.wrapping_add(1)..close, new);
                changed = true;
            }
        }
        if changed {
            let mut text = lines.join("\n");
            if ends_with_newline {
                text.push('\n');
            }
            fs::write(&path, text)
                .map_err(|e| format!("could not write {}: {e}", path.display()))?;
        }
    }

    for warning in &warnings {
        println!("warning: {warning}");
    }
    if args.check {
        if out_of_sync == 0 {
            println!("all {synced} examples are in sync");
            Ok(ExitCode::SUCCESS)
        } else {
            println!(
                "{out_of_sync} of {} examples are out of sync, run `just sync_examples`",
                examples.len()
            );
            Ok(ExitCode::FAILURE)
        }
    } else {
        println!(
            "{out_of_sync} examples updated, {synced} already in sync. Now run `cargo fmt` and \
             `cargo t --doc --all-features`"
        );
        Ok(ExitCode::SUCCESS)
    }
}

fn main() -> ExitCode {
    match run(&Args::parse()) {
        Ok(code) => code,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}

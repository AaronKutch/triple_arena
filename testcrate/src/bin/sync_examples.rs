//! LLM coded helper, TODO if this is widely useful clean it up and make it its
//! own library for testcrates to use

use std::{
    fs,
    ops::Range,
    path::{Path, PathBuf},
    process::ExitCode,
};

use clap::Parser;

/// The marker comment of an example that is the body of the test function that
/// the marker is attached to
const ITEM_MARKER: &str = "// SYNC";
/// The marker comment of an example that is the rest of the file it is in
const REST_MARKER: &str = "//! SYNC";

/// The workspace root, which the defaults are relative to
fn workspace_dir() -> PathBuf {
    let mut res = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    // the manifest directory is `testcrate`
    res.pop();
    res
}

/// Syncs the examples of the examples files into the doc tests and readme code
/// blocks that they are marked for, so that they only ever have to be edited,
/// tested, and formatted in one place without cumbersome editing.
///
/// An example is preceded by one or more marker comments, each of which starts
/// a line, is allowed to be wrapped across the comment lines following it, and
/// is either
///
///     // SYNC(<file relative to the root>, <name>)
///
/// in which case the example is the body of the test function that the markers
/// are attached to, dedented by the one level of being inside the function, or
///
///     //! SYNC(<file relative to the root>, <name>)
///
/// in which case the example is every line after the markers. Leading and
/// trailing blank lines are removed either way.
///
/// Each marker copies the example into
///
///     - a `.rs` file, replacing the interior of the fenced code block of the
///       doc test that is attached to the item named <name>
///     - a `.md` file, replacing the interior of the fenced code block that a
///       `<!-- <name> -->` comment marks
///
/// <name> only has to be unique among the doc tests of that one `.rs` file or
/// the marked code blocks of that one `.md` file, so this does not care about
/// doc tests being added or reordered.
#[derive(Debug, Parser)]
#[command(verbatim_doc_comment)]
struct Args {
    /// Only report whether anything is out of sync, exiting with a failure code
    /// if it is, instead of rewriting any files
    #[arg(long)]
    check: bool,
    /// The file(s) that the examples and their markers are read from
    #[arg(
        long,
        value_name = "FILE",
        num_args = 1..,
        default_values_os_t = [
            workspace_dir().join("testcrate/tests/examples.rs"),
            workspace_dir().join("triple_arena_render/examples/equation.rs"),
        ]
    )]
    examples: Vec<PathBuf>,
    /// The directory that the file of a marker is relative to
    #[arg(long, value_name = "DIR", default_value_os_t = workspace_dir())]
    root: PathBuf,
    /// `max_width` from `.rustfmt.toml`, only applied to doc tests because
    /// their code is formatted with the `/// ` prefix counting against this, so
    /// a line that fits in the examples file does not necessarily fit in the
    /// doc test
    #[arg(long, value_name = "COLUMNS", default_value_t = 100)]
    max_width: usize,
}

/// What a marker attaches to, which is what determines the lines of the example
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    /// A `// SYNC(...)` marker
    Item,
    /// A `//! SYNC(...)` marker
    Rest,
}

/// The kind of file that an example is copied into, which is decided by the
/// extension
#[derive(Clone, Copy)]
enum TargetFile {
    /// A `.rs` file, where the example goes in the doc test of an item
    Rust,
    /// A `.md` file, where the example goes in a marked code block
    Markdown,
}

/// One place that an example is copied to
struct Target {
    /// The target file, relative to `Args::root`
    file: String,
    /// The name of the item that the target doc test is attached to, or the
    /// name in the `<!-- name -->` comment of a markdown file
    name: String,
    /// The line in the examples file that the marker is on, for messages
    line: usize,
}

/// One example and everywhere it is copied to
struct Example {
    /// The examples file that this came from, for messages
    source: String,
    /// The test function name or, for a whole file example, the file name, only
    /// used for messages
    label: String,
    /// Every place this is copied to, in marker order
    targets: Vec<Target>,
    /// The lines of the example, dedented to the outermost level
    body: Vec<String>,
}

/// Every target of one target file, so that a file with more than one is only
/// read and written once
struct Group<'a> {
    /// The target file, relative to `Args::root`
    file: &'a str,
    /// What kind of file it is
    kind: TargetFile,
    /// The examples that are copied into it, and where in it they go
    targets: Vec<(&'a Example, &'a Target)>,
}

/// The lines that an example replaces in a target file
struct Span {
    /// Index of the line before the replaced lines, which is the opening fence
    open: usize,
    /// Index of the line after the replaced lines, which is the closing fence
    close: usize,
    /// The indentation and doc comment marker that each line gets, e.g.
    /// `    ///`, or `None` for a markdown file where the lines go in verbatim
    prefix: Option<String>,
}

impl Span {
    /// The indexes of the lines that the example replaces
    fn body_range(&self) -> Range<usize> {
        self.open.wrapping_add(1)..self.close
    }
}

/// Whether the line starts like a marker comment, whether or not it parses
fn is_marker(line: &str) -> bool {
    line.starts_with(ITEM_MARKER) || line.starts_with(REST_MARKER)
}

/// Parses the marker comment starting on `lines[i]`, returning `Ok(None)` if
/// there is not one there and the index after the marker if there is. A line
/// that starts like a marker but does not parse is a typo, not something to
/// skip over.
///
/// `cargo fmt` wraps a comment that is over the comment width, so a marker is
/// allowed to be broken across the comment lines following it, whose text is
/// joined back together without separators.
fn parse_marker(lines: &[&str], i: usize) -> Result<Option<(Kind, Target, usize)>, String> {
    let (kind, comment, mut text) = if let Some(rest) = lines[i].strip_prefix(REST_MARKER) {
        (Kind::Rest, "//!", rest.trim().to_owned())
    } else if let Some(rest) = lines[i].strip_prefix(ITEM_MARKER) {
        (Kind::Item, "//", rest.trim().to_owned())
    } else {
        return Ok(None);
    };
    let line = i.wrapping_add(1);
    let syntax_err = || {
        format!(
            "line {line}: expected `{ITEM_MARKER}(<file>, <name>)` or `{REST_MARKER}(<file>, \
             <name>)`"
        )
    };
    let mut end = i.wrapping_add(1);
    while !text.contains(')') {
        let Some(continuation) = lines
            .get(end)
            .filter(|line| !is_marker(line))
            .and_then(|line| line.strip_prefix(comment))
        else {
            return Err(syntax_err());
        };
        text.push_str(continuation.trim());
        end = end.wrapping_add(1);
    }
    let Some((file, name)) = text
        .strip_prefix('(')
        .and_then(|text| text.strip_suffix(')'))
        .and_then(|fields| fields.split_once(','))
    else {
        return Err(syntax_err());
    };
    let (file, name) = (file.trim(), name.trim());
    if file.is_empty() || name.is_empty() || name.contains(',') {
        return Err(syntax_err());
    }
    Ok(Some((
        kind,
        Target {
            file: file.to_owned(),
            name: name.to_owned(),
            line,
        },
        end,
    )))
}

/// Whether the line opens a raw string literal that continues onto the next
/// line. Note that this only handles the `r#"` form that the examples use.
fn opens_raw_string(line: &str) -> bool {
    match line.rfind("r#\"") {
        Some(i) => !line[i.wrapping_add(3)..].contains("\"#"),
        None => false,
    }
}

/// Removes the one level of indentation of being inside a test function. The
/// interiors of multi line raw strings are at absolute columns and must not be
/// dedented.
fn dedent(body: &[&str]) -> Vec<String> {
    let mut res = vec![];
    let mut in_raw = false;
    for line in body {
        if in_raw {
            if line.contains("\"#") {
                in_raw = false;
            }
            res.push((*line).to_owned());
        } else {
            let dedented = line.strip_prefix("    ").unwrap_or(line);
            if opens_raw_string(dedented) {
                in_raw = true;
            }
            res.push(dedented.to_owned());
        }
    }
    res
}

/// Removes the leading and trailing blank lines
fn trim_blank_lines(body: Vec<String>) -> Vec<String> {
    let is_blank = |line: &String| line.trim().is_empty();
    let start = body.iter().position(|line| !is_blank(line));
    let Some(start) = start else {
        return vec![];
    };
    let end = body
        .iter()
        .rposition(|line| !is_blank(line))
        .map_or(start, |i| i.wrapping_add(1));
    body[start..end].to_vec()
}

fn parse_examples(source: &str, src: &str) -> Result<Vec<Example>, String> {
    let lines: Vec<&str> = src.lines().collect();
    let mut res: Vec<Example> = vec![];
    let mut i = 0usize;
    while i < lines.len() {
        let Some((kind, target, end)) = parse_marker(&lines, i)? else {
            i = i.wrapping_add(1);
            continue;
        };
        let first = i;
        let mut targets = vec![target];
        i = end;
        // markers on the immediately following lines all apply to the same example
        while i < lines.len() {
            let Some((next_kind, target, end)) = parse_marker(&lines, i)? else {
                break;
            };
            if next_kind != kind {
                return Err(format!(
                    "line {}: this marker is grouped with the one on line {}, so they must both \
                     be `{ITEM_MARKER}` or both be `{REST_MARKER}` markers",
                    i.wrapping_add(1),
                    first.wrapping_add(1)
                ));
            }
            targets.push(target);
            i = end;
        }
        let marker_line = first.wrapping_add(1);
        let (label, body) = match kind {
            Kind::Item => {
                // only attributes and doc comments are allowed between the markers and the
                // test function
                while i < lines.len() {
                    if lines[i].starts_with("fn ") {
                        break;
                    }
                    let trimmed = lines[i].trim_start();
                    if !(trimmed.is_empty()
                        || trimmed.starts_with("#[")
                        || trimmed.starts_with("///"))
                    {
                        return Err(format!(
                            "line {marker_line}: the marker is not attached to a test function"
                        ));
                    }
                    i = i.wrapping_add(1);
                }
                if i >= lines.len() {
                    return Err(format!(
                        "line {marker_line}: reached the end of the file looking for the test \
                         function"
                    ));
                }
                let label = lines[i]
                    .trim_start_matches("fn ")
                    .split('(')
                    .next()
                    .unwrap_or_default()
                    .to_owned();
                // the body ends at the closing brace of the function, which is the only
                // thing at the start of a line
                i = i.wrapping_add(1);
                let start = i;
                while (i < lines.len()) && (lines[i] != "}") {
                    i = i.wrapping_add(1);
                }
                if i >= lines.len() {
                    return Err(format!(
                        "line {marker_line}: the test function `{label}` is not closed"
                    ));
                }
                let body = dedent(&lines[start..i]);
                i = i.wrapping_add(1);
                (label, body)
            }
            Kind::Rest => {
                // a marker after this one would be silently copied along with the example
                if let Some(bad) = lines[i..].iter().position(|line| is_marker(line)) {
                    return Err(format!(
                        "line {}: a `{REST_MARKER}` example is the rest of the file, so no marker \
                         can come after the one on line {marker_line}",
                        i.wrapping_add(bad).wrapping_add(1)
                    ));
                }
                let label = Path::new(source)
                    .file_name()
                    .and_then(|name| name.to_str())
                    .unwrap_or(source)
                    .to_owned();
                let body = lines[i..].iter().map(|line| (*line).to_owned()).collect();
                i = lines.len();
                (label, body)
            }
        };
        res.push(Example {
            source: source.to_owned(),
            label,
            targets,
            body: trim_blank_lines(body),
        });
    }
    Ok(res)
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

/// Finds every Rust doc test of a Rust file, pairing the code fences the same
/// way that Markdown does so that ```` ```text ```` blocks are skipped over
/// rather than confused for one
fn find_doc_tests(lines: &[String]) -> Result<Vec<Span>, String> {
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
                        "expected the code fence on line {} to be a closing fence",
                        i.wrapping_add(1)
                    ));
                }
                if info0.is_empty() || (info0 == "rust") {
                    res.push(Span {
                        open: start,
                        close: i,
                        prefix: Some(prefix),
                    });
                }
            }
        }
    }
    if let Some((start, ..)) = open {
        return Err(format!(
            "the code fence on line {} is never closed",
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

/// The doc test of a Rust file that is attached to an item named `name`
fn find_doc_test(lines: &[String], name: &str) -> Result<Span, String> {
    let doc_tests = find_doc_tests(lines)?;
    let mut matches = doc_tests
        .into_iter()
        .filter(|span| owner_name(lines, span.close).as_deref() == Some(name));
    let Some(span) = matches.next() else {
        return Err(format!("no doc test is attached to an item named `{name}`"));
    };
    if matches.next().is_some() {
        return Err(format!(
            "more than one doc test is attached to an item named `{name}`"
        ));
    }
    Ok(span)
}

/// The code block of a markdown file that a `<!-- name -->` comment marks
fn find_md_block(lines: &[String], name: &str) -> Result<Span, String> {
    let marker = format!("<!-- {name} -->");
    let mut matches = lines
        .iter()
        .enumerate()
        .filter(|(_, line)| line.trim() == marker);
    let Some((marked, _)) = matches.next() else {
        return Err(format!("no code block is marked with `{marker}`"));
    };
    if matches.next().is_some() {
        return Err(format!(
            "more than one code block is marked with `{marker}`"
        ));
    }
    // the fence is allowed to be separated from the comment by blank lines
    let mut open = marked.wrapping_add(1);
    while lines.get(open).is_some_and(|line| line.trim().is_empty()) {
        open = open.wrapping_add(1);
    }
    let Some(info) = lines
        .get(open)
        .and_then(|line| line.trim().strip_prefix("```"))
    else {
        return Err(format!("`{marker}` is not followed by a code fence"));
    };
    let info = info.trim();
    if !(info.is_empty() || (info == "rust")) {
        return Err(format!(
            "the code block marked with `{marker}` is a `{info}` block, but it must be a `rust` \
             block"
        ));
    }
    // the block ends at the next fence, which has to be a closing one, otherwise
    // an unclosed block would swallow everything up to the next one
    let mut close = open.wrapping_add(1);
    loop {
        let never_closed = || format!("the code block marked with `{marker}` is never closed");
        let Some(line) = lines.get(close) else {
            return Err(never_closed());
        };
        if let Some(info) = line.trim().strip_prefix("```") {
            if !info.trim().is_empty() {
                return Err(never_closed());
            }
            break;
        }
        close = close.wrapping_add(1);
    }
    Ok(Span {
        open,
        close,
        prefix: None,
    })
}

/// Turns the lines of an example into the lines that go inside the code block
/// of the target, which for a doc test means prefixing them
fn render(body: &[String], prefix: Option<&str>) -> Vec<String> {
    let Some(prefix) = prefix else {
        return body.to_vec();
    };
    body.iter()
        .map(|line| {
            if line.trim().is_empty() {
                prefix.to_owned()
            } else {
                format!("{prefix} {line}")
            }
        })
        .collect()
}

fn run(args: &Args) -> Result<ExitCode, String> {
    let mut examples: Vec<Example> = vec![];
    for path in &args.examples {
        let source = path.display().to_string();
        let src = fs::read_to_string(path).map_err(|e| format!("could not read {source}: {e}"))?;
        let parsed = parse_examples(&source, &src).map_err(|e| format!("{source}: {e}"))?;
        if parsed.is_empty() {
            return Err(format!(
                "no `{ITEM_MARKER}` or `{REST_MARKER}` markers found in {source}"
            ));
        }
        examples.extend(parsed);
    }

    // group by target file so that files with more than one target are only read
    // and written once, and so that two examples that would silently fight over
    // the same target are caught before anything is written
    let mut groups: Vec<Group> = vec![];
    for example in &examples {
        for target in &example.targets {
            match groups.iter_mut().find(|group| group.file == target.file) {
                Some(group) => {
                    if let Some((other, other_target)) = group
                        .targets
                        .iter()
                        .find(|(_, other)| other.name == target.name)
                    {
                        return Err(format!(
                            "`{}` on line {} of {} and `{}` on line {} of {} both target `{}` in \
                             `{}`",
                            other.label,
                            other_target.line,
                            other.source,
                            example.label,
                            target.line,
                            example.source,
                            target.name,
                            target.file
                        ));
                    }
                    group.targets.push((example, target));
                }
                None => {
                    let kind = match Path::new(&target.file)
                        .extension()
                        .and_then(|extension| extension.to_str())
                    {
                        Some("rs") => TargetFile::Rust,
                        Some("md") => TargetFile::Markdown,
                        _ => {
                            return Err(format!(
                                "{} line {}: `{}` is not a `.rs` or `.md` file, which are the \
                                 only kinds of target file supported",
                                example.source, target.line, target.file
                            ));
                        }
                    };
                    groups.push(Group {
                        file: &target.file,
                        kind,
                        targets: vec![(example, target)],
                    });
                }
            }
        }
    }

    let mut out_of_sync = 0usize;
    let mut synced = 0usize;
    let mut warnings = vec![];
    for group in &groups {
        let file = group.file;
        let path = args.root.join(file);
        let text = fs::read_to_string(&path)
            .map_err(|e| format!("could not read {}: {e}", path.display()))?;
        let ends_with_newline = text.ends_with('\n');
        let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
        let mut changed = false;
        for (example, target) in &group.targets {
            // the target has to be refound for each example, because splicing in a body
            // of a different length shifts every line index after it
            let span = match group.kind {
                TargetFile::Rust => find_doc_test(&lines, &target.name),
                TargetFile::Markdown => find_md_block(&lines, &target.name),
            }
            .map_err(|e| format!("{} line {} -> {file}: {e}", example.source, target.line))?;
            let new = render(&example.body, span.prefix.as_deref());
            if span.prefix.is_some() {
                for line in &new {
                    let width = line.chars().count();
                    if width > args.max_width {
                        warnings.push(format!(
                            "`{}` has a line that is {width} columns wide as a doc test, over the \
                             `max_width` of {}, so `cargo fmt` may rewrap it and leave it out of \
                             sync. Shorten it in {}:\n    {}",
                            example.label,
                            args.max_width,
                            example.source,
                            line.trim()
                        ));
                    }
                }
            }
            let what = format!("`{}` -> `{}` in {file}", example.label, target.name);
            if lines[span.body_range()] == new[..] {
                synced = synced.wrapping_add(1);
                continue;
            }
            out_of_sync = out_of_sync.wrapping_add(1);
            if args.check {
                println!("out of sync: {what}");
            } else {
                println!("updated: {what} (line {})", span.open.wrapping_add(1));
                lines.splice(span.body_range(), new);
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
    let total = out_of_sync.wrapping_add(synced);
    if args.check {
        if out_of_sync == 0 {
            println!("all {total} targets are in sync");
            Ok(ExitCode::SUCCESS)
        } else {
            println!("{out_of_sync} of {total} targets are out of sync, run `just sync_examples`");
            Ok(ExitCode::FAILURE)
        }
    } else {
        println!(
            "{out_of_sync} targets updated, {synced} already in sync. Now run `cargo fmt` and \
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

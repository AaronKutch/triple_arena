use std::{
    fmt::Write,
    fs::{self, File, OpenOptions},
    io,
    path::PathBuf,
};

use internal::{grid_process, RenderGrid};
use triple_arena::Arena;

use crate::*;

/// create the SVG code
pub(crate) fn gen_svg<P: Ptr>(rg: &RenderGrid<P>) -> String {
    // example code for future reference
    //<circle cx="128" cy="128" r="128" fill="orange"/>
    //<rect fill="#f00" x="64" y="64" width="64" height="64"/>
    //<text x="64" y="64" font-size="16" font-family="monospace"
    //<text font-weight="normal">oO0iIlL</text>
    //<!-- L is for line Q is for quadratic C is for cubic -->>
    //<path d="M 0,0 C 100,0 100,100 0,100" stroke="#00f" fill="#000a"/>
    //<!-- grouping element <g> </g> that can apply common modifiers such as
    //<!-- `opacity="0.5"` -->
    //<!--
    //<rect fill="#fff" stroke="#000" x="0" y="0" width="300" height="300"/>
    //<rect x="25" y="25" width="500" height="200" fill="none" stroke-width="4"
    //<rect stroke="pink" />
    //<circle cx="125" cy="125" r="75" fill="orange" />
    //<polyline points="50,150 50,200 200,200 200,100" stroke="red" stroke-width="4"
    //<polyline fill="none" />
    //<line x1="50" y1="50" x2="200" y2="200" stroke="blue" stroke-width="4" />
    //-->

    let mut s = String::new();

    // for debug
    //s += &format!("<circle cx=\"{}\" cy=\"{}\" r=\"4\" fill=\"#f0f\"/>", tmp.0
    // .0, tmp.0 .1);

    // background
    write!(
        s,
        "<rect fill=\"#000\" x=\"0\" y=\"0\" width=\"{}\" height=\"{}\"/>",
        rg.tot_wx, rg.tot_wy
    )
    .unwrap();

    // rectangles and outlines first
    for vert in &rg.grid {
        for node in (*vert).iter().flatten() {
            for rect in &node.rects {
                writeln!(
                    s,
                    "<rect fill=\"#{}\" x=\"{}\" y=\"{}\" width=\"{}\" height=\"{}\"/>",
                    NODE_FILL, rect.0, rect.1, rect.2, rect.3
                )
                .unwrap();
                // outline the rectangle
                writeln!(
                    s,
                    "<polyline stroke=\"#0000\" stroke-width=\"0\" points=\"{},{} {},{} {},{} \
                     {},{} {},{}\"  fill=\"#0000\"/>",
                    rect.0,
                    rect.1,
                    rect.0 + rect.2,
                    rect.1,
                    rect.0 + rect.2,
                    rect.1 + rect.3,
                    rect.0,
                    rect.1 + rect.3,
                    rect.0,
                    rect.1,
                )
                .unwrap();
            }
        }
    }

    // lines second
    for i in 0..rg.grid.len() {
        for j in 0..rg.grid[i].len() {
            if let Some(ref node) = rg.grid[i][j] {
                for k in 0..node.input_points.len() {
                    let (i, ptr, inx) = rg.grid[i][j].as_ref().unwrap().input_points[k];
                    let (o_i, o_j) = rg.dag[ptr].grid_position;
                    let color = COLORS[o_i % COLORS.len()];
                    let o = rg.grid[o_i][o_j].as_ref().unwrap().output_points[inx.unwrap_or(0)].0;
                    let p = NODE_PAD / 2;
                    writeln!(
                        s,
                        "<path stroke=\"#{}\" stroke-width=\"{}\" fill=\"#0000\" d=\"M {},{} C \
                         {},{} {},{} {},{}\"/>",
                        color,
                        RELATION_WIDTH,
                        o.0,
                        o.1,
                        o.0,
                        o.1 + p,
                        i.0,
                        i.1 - p,
                        i.0,
                        i.1
                    )
                    .unwrap();
                    /*write!(
                        s,
                        "<circle cx=\"{}\" cy=\"{}\" r=\"{}\" fill=\"orange\"/>",
                        o.0, o.1, DEBUG_WIDTH
                    )
                    .unwrap();
                    write!(
                        s,
                        "<circle cx=\"{}\" cy=\"{}\" r=\"{}\" fill=\"orange\"/>",
                        i.0, i.1, DEBUG_WIDTH
                    )
                    .unwrap();*/
                }
            } else {
                continue
            };
        }
    }

    // text last
    for vert in &rg.grid {
        for node in (*vert).iter().flatten() {
            for tmp in &node.text {
                let size = tmp.1;
                // these characters need to be escaped, do "&" first
                let final_text = tmp
                    .3
                    .replace('&', "&amp;")
                    .replace('"', "&quot;")
                    .replace('\'', "&apos;")
                    .replace('<', "&lt;")
                    .replace('>', "&gt;");
                writeln!(
                    s,
                    "<text fill=\"#{}\" font-size=\"{}\" font-family=\"{}\" x=\"{}\" y=\"{}\" \
                     textLength=\"{}\">{}</text>",
                    TEXT_COLOR, size, FONT_FAMILY, tmp.0 .0, tmp.0 .1, tmp.2, final_text
                )
                .unwrap();
                /*write!(
                    s,
                    "<circle cx=\"{}\" cy=\"{}\" r=\"{}\" fill=\"red\"/>",
                    tmp.0 .0, tmp.0 .1, DEBUG_WIDTH
                )
                .unwrap();*/
            }
        }
    }

    let output = format!(
        "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>\n\
        <!DOCTYPE svg PUBLIC \"-//W3C//DTD SVG 1.1//EN\" \
        \"http://www.w3.org/Graphics/SVG/1.1/DTD/svg11.dtd\">\n\
        <svg preserveAspectRatio=\"meet\" viewBox=\"{} {} {} {}\" width=\"100%\" height=\"100%\" \
        version=\"1.1\" xmlns=\"http://www.w3.org/2000/svg\">\n\
        {}\n\
        </svg>",
        -PAD,
        -PAD,
        rg.tot_wx + PAD,
        rg.tot_wy + PAD,
        s,
    );

    output
}

/// Renders an SVG graph representation of `arena` in a top-down order from
/// sources to sinks. Cycles are broken up by inserting `Ptr` reference nodes.
/// If `error_on_invalid_ptr` then this will return an error if an invalid
/// `Ptr` is encountered, otherwise it will insert `Ptr` nodes with
/// "(invalid)" appended.
pub fn render_to_svg<P: Ptr, T: DebugNodeTrait<P>>(
    arena: &Arena<P, T>,
    error_on_invalid_ptr: bool,
) -> Result<String, RenderError<P>> {
    let rg = grid_process(arena, error_on_invalid_ptr)?;
    Ok(gen_svg(&rg))
}

/// Writes the result of [render_to_svg] to `out_file`
pub fn render_to_svg_file<P: Ptr, T: DebugNodeTrait<P>>(
    arena: &Arena<P, T>,
    error_on_invalid_ptr: bool,
    out_file: PathBuf,
) -> Result<(), RenderError<P>> {
    let s = render_to_svg(arena, error_on_invalid_ptr)?;
    drop(fs::remove_file(&out_file));
    let mut file = OpenOptions::new()
        .write(true)
        .append(true)
        .create(true)
        .open(out_file)
        .map_err(|e| RenderError::IoError(e))?;
    // avoid trait collision
    <File as io::Write>::write_all(&mut file, s.as_bytes()).map_err(|e| RenderError::IoError(e))?;
    Ok(())
}

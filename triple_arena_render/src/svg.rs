use std::{
    fs::{self, OpenOptions},
    io::Write,
    path::PathBuf,
};

use crate::*;

/// create the SVG code
pub(crate) fn gen_svg<P: PtrTrait>(rg: &RenderGrid<P>) -> String {
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
    s += &format!(
        "<rect fill=\"#000\" x=\"0\" y=\"0\" width=\"{}\" height=\"{}\"/>",
        rg.tot_wx, rg.tot_wy
    );

    // rectangles and outlines first
    for vert in &rg.grid {
        for node in (*vert).iter().flatten() {
            for rect in &node.rects {
                s += &format!(
                    "<rect fill=\"#{}\" x=\"{}\" y=\"{}\" width=\"{}\" height=\"{}\"/>\n",
                    NODE_FILL, rect.0, rect.1, rect.2, rect.3
                );
                // outline the rectangle
                s += &format!(
                    "<polyline stroke=\"#{}\" stroke-width=\"{}\" points=\"{},{} {},{} {},{} \
                     {},{} {},{}\"  fill=\"#0000\"/>\n",
                    NODE_OUTLINE,
                    NODE_OUTLINE_WIDTH,
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
                );
            }
        }
    }

    // lines second
    for i in 0..rg.grid.len() {
        for j in 0..rg.grid[i].len() {
            let num_inputs = if let Some(ref node) = rg.grid[i][j] {
                node.input_points.len()
            } else {
                continue
            };
            for k in 0..num_inputs {
                let (i, ptr) = rg.grid[i][j].as_ref().unwrap().input_points[k];
                let (o_i, o_j) = rg.dag[ptr].grid_position;
                let color = COLORS[o_i % COLORS.len()];
                let o = rg.grid[o_i][o_j].as_ref().unwrap().output_points[0].0;
                let p = NODE_PAD / 2;
                s += &format!(
                    "<path stroke=\"#{}\" fill=\"#0000\" d=\"M {},{} C {},{} {},{} {},{}\"/>\n",
                    color,
                    o.0,
                    o.1,
                    o.0,
                    o.1 + p,
                    i.0,
                    i.1 - p,
                    i.0,
                    i.1
                );
            }
        }
    }

    // text last
    for vert in &rg.grid {
        for node in (*vert).iter().flatten() {
            for tmp in &node.text {
                let size = tmp.1;
                // these characters need to be escaped, do "&" first
                let final_text = tmp
                    .2
                    .replace('&', "&amp;")
                    .replace('"', "&quot;")
                    .replace('\'', "&apos;")
                    .replace('<', "&lt;")
                    .replace('>', "&gt;");
                s += &format!(
                    "<text fill=\"#{}\" font-size=\"{}\" font-family=\"{}\" x=\"{}\" \
                     y=\"{}\">{}</text>\n",
                    TEXT_COLOR,
                    size,
                    FONT_FAMILY,
                    tmp.0 .0,
                    tmp.0 .1 + FONT_ADJUST_Y,
                    final_text
                );
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
/// sources to sinks. Cycles are broken up by inserting pointer reference nodes.
pub fn render_to_svg<P: PtrTrait, T: DebugNodeTrait<P>>(
    arena: &Arena<P, T>,
    error_on_invalid_ptr: bool,
) -> Result<String, RenderError<P>> {
    let rg = grid_process(arena, error_on_invalid_ptr)?;
    Ok(gen_svg(&rg))
}

/// Writes the result of [render_to_svg] to `out_file`
pub fn render_to_svg_file<P: PtrTrait, T: DebugNodeTrait<P>>(
    arena: &Arena<P, T>,
    error_on_invalid_ptr: bool,
    out_file: PathBuf,
) -> Result<(), RenderError<P>> {
    let s = render_to_svg(arena, error_on_invalid_ptr)?;
    drop(fs::remove_file(&out_file));
    OpenOptions::new()
        .write(true)
        .append(true)
        .create(true)
        .open(out_file)
        .map_err(|e| RenderError::IoError(e))?
        .write_all(s.as_bytes())
        .map_err(|e| RenderError::IoError(e))?;
    Ok(())
}
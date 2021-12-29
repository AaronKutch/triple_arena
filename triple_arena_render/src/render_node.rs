use std::cmp::max;

use triple_arena::{Ptr, PtrTrait};

use crate::*;

#[derive(Debug, Clone)]
pub(crate) struct RenderNode<P: PtrTrait> {
    /// Pointer to node this is representing
    pub ptr: Ptr<P>,
    /// Rectangles in (x position, y position, x width, y width)
    pub rects: Vec<(i32, i32, i32, i32)>,
    /// Text location, size, and string
    pub text: Vec<((i32, i32), i32, String)>,
    /// Location of input points and pointers to where they should go
    pub input_points: Vec<((i32, i32), Ptr<P>)>,
    /// Location of output points and where they should go
    pub output_points: Vec<((i32, i32), Ptr<P>)>,
    /// width in x direction
    pub wx: i32,
    /// width in y direction
    pub wy: i32,
}

impl<P: PtrTrait> RenderNode<P> {
    pub fn new(node: &DebugNode<P>, ptr: Ptr<P>) -> Self {
        let mut rects = vec![];
        let mut text = vec![];
        let mut input_points = vec![];
        let mut output_points = vec![];

        let total_source_len: i32 = node.sources.iter().map(|(_, s)| s.len() as i32).sum();
        let total_sink_len: i32 = node.sinks.iter().map(|(_, s)| s.len() as i32).sum();
        let max_center_xlen: i32 = node
            .center
            .iter()
            .map(|s| s.len() as i32)
            .max()
            .unwrap_or(0);

        let total_source_wx =
            (INPUT_FONT_WX * total_source_len) + (PAD * (node.sources.len() as i32));
        let total_sink_wx =
            (INPUT_FONT_WX * total_sink_len) + ((2 * PAD) * (node.sinks.len() as i32));
        let max_center_wx = (FONT_WX * max_center_xlen) + (2 * SMALL_PAD);

        let wx = max(max(total_source_wx, total_sink_wx), max_center_wx);
        // for spreading out sources and sinks
        let extra_source_space = max(wx - total_source_wx, 0);
        let extra_sink_space = max(wx - total_sink_wx, 0);

        let mut wy = SMALL_PAD;

        // generate inputs
        let individual_spaces = extra_source_space
            .checked_div(node.sources.len() as i32 - 1)
            .unwrap_or(0);
        let mut x_progression = 0;
        for (p, s) in &node.sources {
            if !s.is_empty() {
                text.push((
                    (x_progression + PAD, wy + INPUT_FONT_WY),
                    INPUT_FONT_WY,
                    (*s).clone(),
                ));
            }
            let this_wx = INPUT_FONT_WX * (s.len() as i32) + 2 * PAD;
            let center_x = x_progression + (this_wx / 2);
            input_points.push(((center_x, wy - SMALL_PAD), *p));
            x_progression += this_wx + individual_spaces;
        }
        // we need `center_x` for the input points, but do not need any height if all
        // the strings are empty
        if node.sources.iter().any(|(_, s)| !s.is_empty()) {
            wy += INPUT_FONT_WY;
        }

        // center
        if !node.center.is_empty() {
            let offset = ((wx - max_center_wx) / 2) + SMALL_PAD;
            for (i, s) in node.center.iter().enumerate() {
                wy += FONT_WY;
                text.push(((offset, wy), FONT_WY, s.clone()));
                if i != (node.center.len() - 1) {
                    wy += SMALL_PAD;
                }
            }
        }

        // generate outputs
        if node.sinks.iter().any(|(_, s)| !s.is_empty()) {
            wy += INPUT_FONT_WY;
        }
        let individual_spaces = extra_sink_space
            .checked_div(node.sinks.len() as i32 - 1)
            .unwrap_or(0);
        let mut x_progression = 0;
        for (p, s) in &node.sinks {
            if !s.is_empty() {
                text.push((
                    (x_progression + PAD, wy + SMALL_PAD),
                    INPUT_FONT_WY,
                    (*s).clone(),
                ));
            }
            let this_wx = INPUT_FONT_WX * (s.len() as i32) + 2 * PAD;
            let center_x = x_progression + (this_wx / 2);
            output_points.push(((center_x, wy), *p));
            x_progression += this_wx + individual_spaces;
        }

        let rect = (0, 0, wx, wy);
        rects.push(rect);

        Self {
            ptr,
            rects,
            text,
            input_points,
            output_points,
            wx,
            wy,
        }
    }

    pub fn translate(&mut self, mov: (i32, i32)) {
        for rect in &mut self.rects {
            rect.0 += mov.0;
            rect.1 += mov.1;
        }
        for tmp in &mut self.text {
            tmp.0 .0 += mov.0;
            tmp.0 .1 += mov.1;
        }
        for point in &mut self.input_points {
            point.0 .0 += mov.0;
            point.0 .1 += mov.1;
        }
        for point in &mut self.output_points {
            point.0 .0 += mov.0;
            point.0 .1 += mov.1;
        }
    }
}

#![allow(clippy::type_complexity)]

use std::{cmp::max, iter::empty};

use triple_arena::{Ptr, PtrTrait};

use crate::*;

#[derive(Debug, Clone)]
pub(crate) struct RenderNode<P: PtrTrait> {
    /// Pointer to node this is representing
    pub ptr: Ptr<P>,
    /// Rectangles in (x position, y position, x width, y width)
    pub rects: Vec<(i32, i32, i32, i32)>,
    /// Text location, size, length, and string
    pub text: Vec<((i32, i32), i32, i32, String)>,
    /// Location of input points and pointers to where they should go
    pub input_points: Vec<((i32, i32), Ptr<P>, Option<usize>)>,
    /// Location of output points and where they should go
    pub output_points: Vec<((i32, i32), Ptr<P>)>,
    /// width in x direction
    pub wx: i32,
    /// width in y direction
    pub wy: i32,
}

impl<P: PtrTrait> RenderNode<P> {
    pub fn new(
        sources: &[(Ptr<P>, String, Option<usize>)],
        center: &[String],
        sinks: &[(Ptr<P>, String)],
        ptr: Ptr<P>,
    ) -> Self {
        let mut rects = vec![];
        let mut text = vec![];
        let mut input_points = vec![];
        let mut output_points = vec![];

        let total_source_len: i32 = sources.iter().map(|(_, s, _)| s.len() as i32).sum();
        let total_sink_len: i32 = sinks.iter().map(|(_, s)| s.len() as i32).sum();
        let max_center_xlen: i32 = center.iter().map(|s| s.len() as i32).max().unwrap_or(0);

        let total_source_wx =
            (INPUT_FONT_WX * total_source_len) + max(INPUT_PAD * (sources.len() as i32 - 1), 0);
        let total_sink_wx =
            (INPUT_FONT_WX * total_sink_len) + max(INPUT_PAD * (sinks.len() as i32 - 1), 0);
        let max_center_wx = FONT_WX * max_center_xlen;

        let mut wx = max(max(total_source_wx, total_sink_wx), max_center_wx) + PAD;
        // for spreading out sources and sinks
        let extra_source_space = wx - total_source_wx;
        let extra_sink_space = wx - total_sink_wx;
        let extra_center_space = wx - max_center_wx;

        let empty_node = wx == PAD;

        let mut wy = if empty_node {PAD} else {0};

        // generate inputs
        // both the len == 0 and len == 1 cases have to be specially handled
        let separation = if sources.len() < 2 {
            extra_source_space / 2
        } else {
            extra_source_space
                .checked_div(sources.len() as i32 - 1)
                .unwrap_or(0)
        };
        let mut x_progression = PAD;
        for (p, s, inx) in sources {
            if sources.len() == 1 {
                x_progression += separation;
            }
            if !s.is_empty() {
                text.push((
                    (x_progression, wy + INPUT_FONT_WY + INPUT_FONT_ADJUST_Y),
                    INPUT_FONT_SIZE,
                    INPUT_FONT_WX * (s.len() as i32),
                    (*s).clone(),
                ));
            }
            let this_wx = INPUT_FONT_WX * (s.len() as i32);
            let center_x = x_progression + (this_wx / 2);
            input_points.push(((center_x, wy), *p, *inx));
            x_progression += this_wx + separation;
        }
        // we need `center_x` for the input points, but do not need any height if all
        // the strings are empty
        if sources.iter().any(|(_, s, _)| !s.is_empty()) {
            wy += INPUT_FONT_WY;
        }

        // center
        wy += PAD;
        if !center.is_empty() {
            for (i, s) in center.iter().enumerate() {
                wy += FONT_WY;
                text.push((
                    ((extra_center_space / 2) + PAD, wy + FONT_ADJUST_Y),
                    FONT_SIZE,
                    FONT_WX * (s.len() as i32),
                    s.clone(),
                ));
                if i != (center.len() - 1) {
                    wy += PAD;
                }
            }
        }

        // generate outputs
        if sinks.iter().any(|(_, s)| !s.is_empty()) {
            wy += INPUT_FONT_WY;
        }
        let separation = if sources.len() < 2 {
            extra_sink_space / 2
        } else {
            extra_sink_space
                .checked_div(sinks.len() as i32 - 1)
                .unwrap_or(0)
        };
        let mut x_progression = PAD;
        for (p, s) in sinks {
            if sinks.len() == 1 {
                x_progression += separation;
            }
            if !s.is_empty() {
                text.push((
                    (x_progression, wy + INPUT_FONT_ADJUST_Y),
                    INPUT_FONT_SIZE,
                    INPUT_FONT_WX * (s.len() as i32),
                    (*s).clone(),
                ));
            }
            let this_wx = INPUT_FONT_WX * (s.len() as i32);
            let center_x = x_progression + (this_wx / 2);
            output_points.push(((center_x, wy), *p));
            x_progression += this_wx + separation;
        }

        if empty_node {
            wy += PAD;
        }
        wx += 2 * PAD;

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

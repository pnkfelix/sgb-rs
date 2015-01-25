use {ULong,Long,idx,long};
use basic::{Context, Repeating};
use graph::{Graph};
use graph::UtilType::{V,Z,I};

use std::fmt;

pub trait BoardDimensions {
    // The dimensionality of the board (d); note that this implies d+1
    // coordinates per point in simplex, due to the triangular
    // structure of the board.
    fn num_dims(&self) -> usize;
    // calls `f` for each n from [0,d], passing the the upper-bound
    // for the n'th coordinate as well as `n` itself.
    fn fill_bounds<F>(&self, f: F) where F: FnMut(Long, usize);
    // what these dimensions contribute to the overall simplex ID string.
    fn partial_id(&self) -> String;
}

pub trait SimplexDescription {
    type Dims: BoardDimensions + fmt::Debug;
    fn sum_of_coords(&self) -> ULong;
    fn dims(&self) -> Self::Dims;
    fn directed(&self) -> bool;
    fn id(&self) -> String;
}

//                               n,   n0,   n1,   n2,   n3,   n4, directed
impl SimplexDescription for (ULong, Long, Long, Long, Long, Long, Long) {
    type Dims = DynamicSimplexDimensions;
    fn sum_of_coords(&self) -> ULong { self.0 }
    fn dims(&self) -> DynamicSimplexDimensions {
        let (n, n0, n1, n2, n3, n4, _directed) = *self;
        decode_the_simplex_size_parameters(n, n0, n1, n2, n3, n4)
    }
    fn directed(&self) -> bool {
        let (_n, _n0, _n1, _n2, _n3, _n4, directed) = *self;
        directed != 0
    }
    fn id(&self) -> String {
        let (n, n0, n1, n2, n3, n4, directed) = *self;
        format!("simplex({},{},{},{},{},{},{})",
                n, n0, n1, n2, n3, n4, directed)
    }
}

struct SumCoords(ULong);

fn decode_the_simplex_size_parameters(
    n: ULong, n0: Long, n1: Long, n2: Long, n3: Long, n4: Long)
    -> DynamicSimplexDimensions
{
    use self::DynamicSimplexDimensions::*;
    if n0 < 0 {
        Loop1((Repeating(idx(-n0)),long(n)))
    } else if n0 == 0 {
        // default case: a triangular array w/ 3n boundary cells (i.e. n0 = -2)
        Loop1((Repeating(2), long(n)))
    } else if n1 < 0 {
        Loop1((Repeating(idx(-n1)), n0))
    } else if n1 == 0 {
        // d = 0
        Once0((n0,))
    } else if n2 < 0 {
        Loop2((Repeating(idx(-n2)), n0, n1))
    } else if n2 == 0 {
        // d = 1
        Once1((n0,n1))
    } else if n3 < 0 {
        Loop3((Repeating(idx(-n3)), n0, n1, n2))
    } else if n3 == 0 {
        // d = 2
        Once2((n0,n1,n2))
    } else if n4 < 0 {
        Loop4((Repeating(idx(-n4)), n0, n1, n2, n3))
    } else if n4 == 0 {
        // d = 3
        Once3((n0,n1,n2,n3))
    } else {
        // d = 4
        Once4((n0,n1,n2,n3,n4))
    }
}

#[derive(Copy,Show)]
/// The attached numbers in each case are the upper bounds on each
/// of the d+1 coordinates, for dimensionality d.
pub enum DynamicSimplexDimensions {
    /// Zero? dimensional (a technicality at best)
    Once0((Long,)),
    /// One dimensional
    Once1((Long,Long)),
    /// Two dimensional
    Once2((Long,Long,Long)),
    /// Three dimensional
    Once3((Long,Long,Long,Long)),
    /// Four dimensional
    Once4((Long,Long,Long,Long,Long)),
    /// n-dimensional (Repeating(n), x): all bounded by x
    Loop1((Repeating<usize>,Long,)),
    /// n-dimensional (Repeating(n), x, y): draw bounds from series x,y,x,y,...
    Loop2((Repeating<usize>,Long,Long,)),
    /// n-dimensional (Repeating(n), x, y, z): draw bounds from x,y,z,x,y,z,...
    Loop3((Repeating<usize>,Long,Long,Long,)),
    /// n-dimensional (Repeating(n), x, y, z, w): from x,y,z,w,x,y,z,w,...
    Loop4((Repeating<usize>,Long,Long,Long,Long)),
}

impl BoardDimensions for (Long,) {
    fn num_dims(&self) -> usize { 0 }
    fn partial_id(&self) -> String { format!("{},0,0,0,0", self.0) }
    fn fill_bounds<F>(&self, mut f: F) where F: FnMut(Long, usize) {
        f(self.0, 0) }
}

impl BoardDimensions for (Long,Long) {
    fn num_dims(&self) -> usize { 1 }
    fn partial_id(&self) -> String { format!("{},{},0,0,0", self.0, self.1) }
    fn fill_bounds<F>(&self, mut f: F) where F: FnMut(Long, usize) {
        f(self.0, 0);
        f(self.1, 1);
    }
}

impl BoardDimensions for (Long,Long,Long) {
    fn num_dims(&self) -> usize { 2 }
    fn partial_id(&self) -> String {
        format!("{},{},{},0,0", self.0, self.1, self.2)
    }
    fn fill_bounds<F>(&self, mut f: F) where F: FnMut(Long, usize) {
        f(self.0, 0);
        f(self.1, 1);
        f(self.2, 2);
    }
}

impl BoardDimensions for (Long,Long,Long,Long) {
    fn num_dims(&self) -> usize { 3 }
    fn partial_id(&self) -> String {
        format!("{},{},{},{},0", self.0, self.1, self.2, self.3)
    }
    fn fill_bounds<F>(&self, mut f: F) where F: FnMut(Long, usize) {
        f(self.0, 0);
        f(self.1, 1);
        f(self.2, 2);
        f(self.3, 3);
    }
}

impl BoardDimensions for (Long,Long,Long,Long,Long) {
    fn num_dims(&self) -> usize { 4 }
    fn partial_id(&self) -> String {
        format!("{},{},{},{},{}", self.0, self.1, self.2, self.3, self.4)
    }
    fn fill_bounds<F>(&self, mut f: F) where F: FnMut(Long, usize) {
        f(self.0, 0);
        f(self.1, 1);
        f(self.2, 2);
        f(self.3, 3);
        f(self.4, 4);
    }
}

impl BoardDimensions for (Repeating<usize>,Long,) {
    fn num_dims(&self) -> usize { self.0.len() }
    fn partial_id(&self) -> String {
        format!("{},{},0,0,0", self.1, -long(self.0.len()))
    }
    fn fill_bounds<F>(&self, mut f: F) where F: FnMut(Long, usize) {
        let n = [self.1];
        for k in 0..self.0.len() {
            f(n[k % 1], k);
        }
    }
}

impl BoardDimensions for (Repeating<usize>,Long,Long) {
    fn num_dims(&self) -> usize { self.0.len() }
    fn partial_id(&self) -> String {
        format!("{},{},{},0,0", self.1, self.2, -long(self.0.len()))
    }
    fn fill_bounds<F>(&self, mut f: F) where F: FnMut(Long, usize) {
        let n = [self.1, self.2];
        for k in 0..self.0.len() {
            f(n[k % 2], k);
        }
    }
}

impl BoardDimensions for (Repeating<usize>,Long,Long,Long) {
    fn num_dims(&self) -> usize { self.0.len() }
    fn partial_id(&self) -> String {
        format!("{},{},{},{},0", self.1, self.2, self.3, -long(self.0.len()))
    }
    fn fill_bounds<F>(&self, mut f: F) where F: FnMut(Long, usize) {
        let n = [self.1, self.2, self.3];
        for k in 0..self.0.len() {
            f(n[k % 3], k);
        }
    }
}

impl BoardDimensions for (Repeating<usize>,Long,Long,Long,Long) {
    fn num_dims(&self) -> usize { self.0.len() }
    fn partial_id(&self) -> String {
        format!("{},{},{},{},{}", self.1, self.2, self.3, self.4, -long(self.0.len()))
    }
    fn fill_bounds<F>(&self, mut f: F) where F: FnMut(Long, usize) {
        let n = [self.1, self.2, self.3, self.4];
        for k in 0..self.0.len() {
            f(n[k % 4], k);
        }
    }
}

impl BoardDimensions for DynamicSimplexDimensions {
    fn num_dims(&self) -> usize {
        use self::DynamicSimplexDimensions::*;
        match *self {
            Once0(ref t) => t.num_dims(),
            Once1(ref t) => t.num_dims(),
            Once2(ref t) => t.num_dims(),
            Once3(ref t) => t.num_dims(),
            Once4(ref t) => t.num_dims(),
            Loop1(ref t) => t.num_dims(),
            Loop2(ref t) => t.num_dims(),
            Loop3(ref t) => t.num_dims(),
            Loop4(ref t) => t.num_dims(),
        }
    }
    fn fill_bounds<F>(&self, f: F) where F: FnMut(Long, usize) {
        use self::DynamicSimplexDimensions::*;
        match *self {
            Once0(ref t) => t.fill_bounds(f),
            Once1(ref t) => t.fill_bounds(f),
            Once2(ref t) => t.fill_bounds(f),
            Once3(ref t) => t.fill_bounds(f),
            Once4(ref t) => t.fill_bounds(f),
            Loop1(ref t) => t.fill_bounds(f),
            Loop2(ref t) => t.fill_bounds(f),
            Loop3(ref t) => t.fill_bounds(f),
            Loop4(ref t) => t.fill_bounds(f),
        }
    }
    fn partial_id(&self) -> String {
        use self::DynamicSimplexDimensions::*;
        match *self {
            Once0(ref t) => t.partial_id(),
            Once1(ref t) => t.partial_id(),
            Once2(ref t) => t.partial_id(),
            Once3(ref t) => t.partial_id(),
            Once4(ref t) => t.partial_id(),
            Loop1(ref t) => t.partial_id(),
            Loop2(ref t) => t.partial_id(),
            Loop3(ref t) => t.partial_id(),
            Loop4(ref t) => t.partial_id(),
        }
    }
}

// (see documentation for `Context::simplex`)
pub fn simplex<SD:SimplexDescription>(c: &mut Context, sd: SD) -> Graph {
    // [Normalize the simplex parameters 27]
    let nn = &mut c.nn;
    let dims = sd.dims();
    let d = dims.num_dims();
    dims.fill_bounds(|part, k| {
        nn[k] = part;
    });

    // [Create a graph with one vertex for each point 28]

    // [Determine the number of feasible (x_0,...,x_d) and
    //  allocate the graph 29]

    // @ We determine the number of vertices by determining the
    // coefficient of~$z^n$ in the power series
    // $$(1+z+\cdots+z^{n_0})(1+z+\cdots+z^{n_1})\ldots(1+z+\cdots+z^{n_d}).$$

    let new_graph_id = sd.id();

    // hash table will be used
    let new_graph_util_types = [V,V,Z,I,I,I,Z,Z,Z,Z,Z,Z,Z,Z];
    unimplemented!();

    // [Name the points and create the arcs or edges 31]
    unimplemented!();
}

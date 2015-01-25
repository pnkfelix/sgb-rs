use {ULong,Long,idx,long,ulong};
use basic::{Context, Repeating};
use graph::{Graph, Util};
use graph::UtilType::{V,Z,I};

use std::fmt;
use std::iter;

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

#[allow(dead_code)]
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
    let &mut Context {
        ref area, ref mut nn, ref mut sig,
        ref mut xx, ref mut yy, .. } = c;
    let dims = sd.dims();
    let n = sd.sum_of_coords();
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

    let mut vertices = {
        let nverts;
        let mut coef : Vec<Long> = iter::repeat(0).take(idx(n+1)).collect();
        for k in 0..nn[0]+1 {
            coef[idx(k)] = 1;
        }
        // now coef reperesens the coefficients of 1 + z + ... + z^{n_0}
        for j in 1..d+1 {
            // [Multiply the power series coefficients
            //  by 1 + z + ... + z^{n_j} 30]

            // @ There's a neat way to multiply by
            // $1+z+\cdots+z^{n_j}$: We multiply first by
            // $1-z^{n_j+1}$, then sum the coefficients.
            // 
            // We want to detect impossibly large specifications
            // without risking integer overflow. It is easy to do this
            // because multiplication is being done via addition.

            assert!(nn[j] <= n as Long, "nn[j]={} n={} nn={:?}", nn[j], n, &nn[]);
            for (i,k) in (0..(n - ulong(nn[j]))).zip(0..n).rev() {
                coef[idx(k)] -= coef[idx(i)];
            }
            let mut s = 1;
            for k in 1..n+1 {
                s += coef[idx(k)];
                if s > 1_000_000_000 {
                    panic!("very_bad_specs s={} coef={:?}", s, coef);
                }
                coef[idx(k)] = s;
            }
        }
        nverts = coef[idx(n)];
        Graph::new_vertices(nverts)
    };

    let new_graph_id = sd.id();

    // hash table will be used
    let new_graph_util_types = [V,V,Z,I,I,I,Z,Z,Z,Z,Z,Z,Z,Z];

    let mut new_graph;

    // [Name the points and create the arcs or edges 31]

    // @ As we generate the vertices, it proves convenient to
    // precompute an array containing the numbers
    // $y_j=n_j+\cdots+n_d$, which represent the largest possible sums
    // $x_j+\cdots+x_d$. We also want to maintain the numbers
    // $\sigma_j=n-(x_0+\cdots+x_{j-1})=x_j+\cdots+x_d$. The
    // conditions
    //
    // $$0\le x_j\le n_j, \qquad \sigma_j-y_{j+1}\le x_j\le \sigma_j$$
    //
    // are necessary and sufficient, in the sense that we can find at
    // least one way to complete a partial solution $(x_0,\ldots,x_k)$
    // to a full solution $(x_0,\ldots,x_d)$ if and only if the
    // conditions hold for all $j\le k$.
    // 
    // There is at least one solution if and only if $n\le y_0$.
    // 
    // We enter the name string into a hash table, using the |hash_in|
    // routine of {\sc GB\_\,GRAPH}, because there is no simple way to
    // compute the location of a vertex from its coordinates.

    yy[d+1] = 0;
    sig[0] = long(n);
    for k in (0..d+1).rev() { yy[k] = yy[k+1] + nn[k]; }
    if yy[0] >= long(n) {
        let mut k = 0;
        xx[0] = if yy[1] >= long(n) { 0 } else { long(n) - yy[1] };

        'find_partials: for (v_i, v) in vertices.iter_mut().enumerate() {
            // [Complete the partial solution (x_0,...,x_k) 32]
            let mut s = sig[k] - xx[k];
            debug!("initializing vertex_{}, s={} k={} sig={:?} xx={:?}",
                   v_i, s, k, &sig[], &xx[]);
            k += 1;
            while k <= d {
                sig[k] = s;
                xx[k] = if s <= yy[k+1] { 0 } else { s - yy[k+1] };
                s -= xx[k]; k += 1;
            }
            assert_eq!(s, 0);

            // [Assign a symbolic name for (x_0,...,x_d) to vertex v 34]

            // @ As in the |board| routine, we represent the sequence
            // of coordinates $(2,0,1)$ by the string `"2.0.1"`.  The
            // string won't exceed |BUF_SIZE|, because the ratio
            // |BUF_SIZE/MAX_D| is plenty big.
            // 
            // The first three coordinate values, $(x_0,x_1,x_2)$, are
            // placed into utility fields |x|, |y|, and |z|, so that
            // they can be accessed immediately if an application
            // needs them.

            let mut p = String::new();
            for k in 0..d+1 {
                p.push_str(format!(".{}", xx[k]).as_slice());
            }
            v.name = p.chars().skip(1).collect(); // omit char 0, which is '.'
            v.util.x = Util::I(xx[0]);
            v.util.y = Util::I(xx[1]);
            v.util.z = Util::I(xx[2]);

            // [Advance to the next partial solution (x_0,...,x_k),
            //  where k is as large as possible; break if there are no
            //  more solutions 33]

            // @ Here we seek the largest $k$ such that $x_k$ can be
            // increased without violating the necessary and
            // sufficient conditions stated earlier.

            for k_ in (0..d).rev() {
                k = k_;
                if xx[k_] < sig[k_] && xx[k_] < nn[k_] {
                    break;
                }
                if k_ == 0 {
                    break 'find_partials;
                }
            }
            xx[k] += 1;
        }

        let vertices = area.alloc(move |:| vertices);

        new_graph = Graph::new_graph(&vertices[], area);
        new_graph.id = new_graph_id;
        new_graph.util_types = new_graph_util_types;

        for v in new_graph.vertices().iter() {
            new_graph.name_to_vertex.insert(&v.name[], v); // enter v.name into hash table (via utility fields u,v)
        }

        k = 0;
        xx[0] = if yy[1] >= long(n) { 0 } else { long(n) - yy[1] };

        'find_partials: for (v_i, v) in new_graph.vertices().iter().enumerate() {
            // [Complete the partial solution (x_0,...,x_k) 32]
            let mut s = sig[k] - xx[k];
            debug!("Finding {} for vertex_{}, s={} k={} sig={:?} xx={:?}",
                   if sd.directed() { "arcs" } else { "edges" },
                   v_i, s, k, &sig[], &xx[]);
            k += 1;
            while k <= d {
                sig[k] = s;
                xx[k] = if s <= yy[k+1] { 0 } else { s - yy[k+1] };
                s -= xx[k]; k += 1;
            }
            assert_eq!(s, 0);

            // [Create arcs or edges from previous points to v 35]

            for j in (0..d) {
                if xx[j] != 0 {
                    xx[j] -= 1;
                    for k in j+1..d+1 {
                        if xx[k] < nn[k] {
                            let mut p = String::new();
                            xx[k] += 1;
                            for i in 0..d+1 {
                                p.push_str(format!(".{}", xx[i]).as_slice());
                            }
                            let u = new_graph.name_to_vertex[p[1..p.len()]];
                            if sd.directed() {
                                new_graph.new_arc(u, v, 1);
                            } else {
                                new_graph.new_edge(u, v, 1);
                            }
                            xx[k] -= 1;
                        }
                    }
                    xx[j] += 1;
                }
            }

            // [Advance to the next partial solution (x_0,...,x_k),
            //  where k is as large as possible; break if there are no
            //  more solutions 33]

            // @ Here we seek the largest $k$ such that $x_k$ can be
            // increased without violating the necessary and
            // sufficient conditions stated earlier.

            for k_ in (0..d).rev() {
                k = k_;
                if xx[k_] < sig[k_] && xx[k_] < nn[k_] {
                    break;
                }
                if k_ == 0 {
                    break 'find_partials;
                }
            }
            xx[k] += 1;
        }
        return new_graph;
    }

    let vertices = area.alloc(move |:| vertices);
    new_graph = Graph::new_graph(&vertices[], area);
    new_graph.id = new_graph_id;
    new_graph.util_types = new_graph_util_types;
    new_graph
}

#[test]
fn d2_2d_triangular() {
    let mut c = Context::new();
    let s = c.simplex((3, 3, 3, 3, 0, 0, 0));
    println!("s: {:E}", s);
    assert_eq!(s.vertices().iter().count(), (4 * 5)/2);
    panic!("fake");
}

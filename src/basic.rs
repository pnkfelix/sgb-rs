//! Introduction. This GraphBase module contains six subroutines that generate
//! standard graphs of various types, together with six routines that combine or
//! transform existing graphs.
//!
//! Simple examples of the use of these routines can be found in the
//! demonstration programs {\sc QUEEN} and {\sc QUEEN\_WRAP}.

use ::{Long, idx};
use graph::{Area, Graph, Util};
use graph::UtilType::{Z,I};

use std::default::Default;

/// We limit the number of dimensions to 91 or less. This is hardly a
/// limitation, since the number of vertices would be astronomical
/// even if the dimensionality were only half this big. But some of
/// our later programs will be able to make good use of 40 or 50
/// dimensions and perhaps more; the number 91 is an upper limit
/// imposed by the number of standard printable characters (see the
/// convention for vertex names in the perms routine).
const MAX_D: usize = 91;

/// Several arrays will facilitate the calculations that board needs
/// to make. The number of distinct values in coordinate position k
/// will be nn[k]; this coordinate position will wrap around if and
/// only if wr[k] ̸= 0. The current moves under consideration will be
/// from (x1, . . . , xd) to (x1 + δ1, . . . , xd + δd), where δk is
/// stored in del [k]. An auxiliary array sig holds the sums σk = δ12
/// + · · · + δk2−1. Additional arrays xx and yy hold coordinates of
/// vertices before and after a move is made.
///
/// Some of these arrays are also used for other purposes by other
/// programs besides board ; we will meet those programs later.
pub struct Context {
    area: Area,
    _working_storage: Area,

    /// component sizes
    nn: [Long; MAX_D + 1],
    /// does this component wrap around?
    wr: [Long; MAX_D + 1],
    /// displacements for the current move
    del: [Long; MAX_D + 1],
    /// partial sums of squares of diplacements
    sig: [Long; MAX_D + 2],
    /// coordinate values
    xx: [Long; MAX_D + 1],
    /// coordinate values
    yy: [Long; MAX_D + 1],
}

impl Context {
    pub fn new() -> Context {
        Context {
            area: Default::default(),
            _working_storage: Default::default(),
            nn: [0; MAX_D+1],
            wr: [0; MAX_D+1],
            del: [0; MAX_D+1],
            sig: [0; MAX_D+2],
            xx: [0; MAX_D+1],
            yy: [0; MAX_D+1],
        }
    }
}

impl Context {
    pub fn simplex(&mut self) -> Graph { unimplemented!() }
    pub fn subsets(&mut self) -> Graph { unimplemented!() }
    pub fn perms(&mut self) -> Graph { unimplemented!() }
    pub fn parts(&mut self) -> Graph { unimplemented!() }
    pub fn binary(&mut self) -> Graph { unimplemented!() }
    pub fn complement(&mut self) -> Graph { unimplemented!() }
    pub fn gunion(&mut self) -> Graph { unimplemented!() }
    pub fn intersection(&mut self) -> Graph { unimplemented!() }
    pub fn lines(&mut self) -> Graph { unimplemented!() }
    pub fn product(&mut self) -> Graph { unimplemented!() }
    pub fn induced(&mut self) -> Graph { unimplemented!() }
}

impl Context {
    /// [Grids and game boards. The subroutine call]
    /// `board(n1,n2,n3,n4,piece,wrap,directed)` constructs a graph
    /// based on the moves of generalized chesspieces on a generalized
    /// rectangular board. Each vertex of the graph corresponds to a
    /// position on the board. Each arc of the graph corresponds to a
    /// move from one position to another.
    ///
    /// The first parameters, n1 through n4 , specify the size of the
    /// board. If, for example, a two-dimensional board with n1 rows
    /// and n2 columns is desired, you set n1 = n1, n2 = n2, and n3 =
    /// 0; the resulting graph will have n1n2 vertices. If you want a
    /// three-dimensional board with n3 layers, set n3 = n3 and n4 =
    /// 0. If you want a 4-D board, put the number of 4th coordinates
    /// in n4 . If you want a d-dimensional board with 2d positions,
    /// set n1 = 2 and n2 = −d.
    ///
    /// In general, the board subroutine determines the dimensions by
    /// scanning the sequence (n1, n2, n3, n4, 0) from left to right
    /// until coming to the first nonpositive parameter n{k+1}.
    /// If `k = 0` (i.e., if n1 ≤ 0), the default size 8 × 8 will be
    /// used; this is an ordinary chessboard with 8 rows and 8
    /// columns. Otherwise if n{k+1} = 0, the board will have k
    /// dimensions n1, . . . , nk. Otherwise we must have n{k+1} < 0;
    /// in this case, the board will have d = |nk+1| dimensions,
    /// chosen as the first d elements of the infinite periodic
    /// sequence (n1,...,nk,n1,...,nk,n1,...). For example, the
    /// specification (n1,n2,n3,n4) = (2,3,5,−7) is about as tricky as
    /// you can get. It produces a seven-dimensional board with
    /// dimensions (n1, . . . , n7) = (2, 3, 5, 2, 3, 5, 2), hence a
    /// graph with 2 · 3 · 5 · 2 · 3 · 5 · 2 = 1800 vertices.
    ///
    /// The piece parameter specifies the legal moves of a generalized
    /// chesspiece. If piece > 0, a move from position u to position v
    /// is considered legal if and only if the Euclidean distance
    /// between points u and v is equal to￼√ piece. For example, if
    /// piece = 1 and if we have a two-dimensional board, the legal
    /// moves from (x, y) are to (x, y ± 1) and (x ± 1, y); these are
    /// the moves of a so-called wazir, the only moves that a king and
    /// a rook can both make. If piece = 2, the legal moves from (x,y)
    /// are to (x ± 1, y ± 1); these are the four moves that a king
    /// and a bishop can both make. (A piece that can make only these
    /// moves was called a “fers” in ancient Muslim chess.)  If piece
    /// = 5, the legal moves are those of a knight, from (x, y) to (x
    /// ± 1, y ± 2) or to (x ± 2, y ± 1). If piece = 3, there are no
    /// legal moves on a two-dimensional board; but moves from (x, y,
    /// z) to (x ± 1, y ± 1, z ± 1) would be legal in three
    /// dimensions. If piece = 0, it is changed to the default value
    /// piece = 1.
    ///
    /// If the value of piece is negative, arbitrary multiples of the
    /// basic moves for |piece| are permitted. For example, piece = −1
    /// defines the moves of a rook, from (x,y) to (x ± a,y) or to
    /// (x,y ± a) for all a > 0; piece = −2 defines the moves of a
    /// bishop, from (x, y) to (x ± a, y ± a). The literature of
    /// “fairy chess” assigns standard names to the following piece
    /// values: wazir = 1, fers = 2, dabbaba = 4, knight = 5, alfil =
    /// 8, camel = 10, zebra = 13, giraffe = 17, fiveleaper = 25,
    /// root-50-leaper = 50, etc.; rook = −1, bishop = −2, unicorn =
    /// −3, dabbabarider = −4, nightrider = −5, alfilrider = −8,
    /// camelrider = −10, etc.
    ///
    /// To generate a board with the moves of a king, you can use the
    /// gunion subroutine below to take the union of boards with piece
    /// = 1 and piece = 2. Similarly, you can get queen moves by
    /// taking the union of boards with piece = −1 and piece = −2.
    ///
    /// If piece > 0, all arcs of the graph will have length 1. If
    /// piece < 0, the length of each arc will be the number of
    /// multiples of a basic move that produced the arc.
    ///
    /// If the wrap parameter is nonzero, it specifies a subset of
    /// coordinates in which values are computed modulo the
    /// corresponding size. For example, the coordinates (x, y) for
    /// vertices on a two-dimensional board are restricted to the
    /// range 0 ≤ x < n1, 0 ≤ y < n2; therefore when wrap = 0, a move
    /// from (x,y) to (x + δ1, y + δ2) is legal only if 0 ≤ x + δ1 <
    /// n1 and 0 ≤ y + δ2 < n2. But when wrap = 1, the x coordinates
    /// are allowed to “wrap around”; the move would then be made to
    /// ((x + δ1) mod n1, y + δ2), provided that 0 ≤ y + δ2 <
    /// n2. Setting wrap = 1 effectively makes the board into a
    /// cylinder instead of a rectangle. Similarly, the y coordinates
    /// are allowed to wrap around when wrap = 2. Both x and y
    /// coordinates are treated modulo their corresponding sizes when
    /// wrap = 3; the board is then effectively a torus. In general,
    /// coordinates k1, k2, . . . will wrap around when
    /// `wrap = 2k1−1 + 2k2−1 + · · ·`.
    /// Setting `wrap = −1` causes all coordinates to be computed
    /// modulo their size.
    ///
    /// The graph constructed by board will be undirected unless
    /// `directed != 0`. Directed board graphs will be acyclic when
    /// `wrap = 0`, but they may have cycles when `wrap != 0`a. Precise
    /// rules defining the directed arcs are given below.
    ///
    /// Several important special cases are worth noting. To get the
    /// complete graph on n vertices, you can say
    /// `board(n,0,0,0,−1,0,0)`. To get the transitive tournament on n
    /// vertices, i.e., the directed graph with arcs from u to v when
    /// u < v, you can say `board(n,0,0,0,−1,0,1)`. To get the empty
    /// graph on n vertices, you can say `board(n,0,0,0,2,0,0)`. To
    /// get a circuit (undirected) or a cycle (directed) of length n,
    /// you can say `board(n,0,0,0,1,1,0)` and `board(n,0,0,0,1,1,1)`,
    /// respectively.
    pub fn board(&mut self, mut n1: Long, mut n2: Long, mut n3: Long, mut n4: Long,
             mut piece: Long, wrap: Long, directed: bool) -> Graph {
        let mut vertices;
        let mut new_graph: Graph; // the graph being constructed
        // all-purpose indices
        let mut j: Long; let mut k: usize;
        let mut d: usize; // the number of dimensions

        let mut p: Long; // |piece|

        let &mut Context {
            ref area, ref mut nn, ref mut wr,
            ref mut del, ref mut sig, ref mut xx, ref mut yy, .. } = self;

        // [Normalize the board size parameters 11]
        enum E { Periodic(usize), Done }
        if let E::Periodic(k) = {
            let k: usize;
            if piece == 0 { piece = 1; }
            if n1 <= 0 { n1 = 8; n2 = 8; n3 = 0; }
            nn[1] = n1;
            let r = if n2 <= 0 {
                k = 2; d = idx(-n2); n3 = 0; n4 = 0; E::Periodic(k)
            } else {
                nn[2] = n2;
                if n3 <= 0 { k = 3; d = idx(-n3); n4 = 0; E::Periodic(k) }
                else {
                    nn[3] = n3;
                    if n4 <= 0 { k = 4; d = idx(-n4); E::Periodic(k) }
                    else { k = 0; nn[4] = n4; d = 4; E::Done }
                }
            };
            if d == 0 { assert!(k > 0); d = k - 1; E::Done } else { r } }
        {
            // [Compute component sizes periodically for d dimensions 12]

            // At this point, nn [1] through nn [k − 1] are the
            // component sizes that should be replicated periodically.
            //
            // In unusual cases, the number of dimensions might not be
            // as large as the number of specifications.
            if idx(d) > MAX_D { panic!("bad_specs d: {}", d); }
            for (j,k) in (k..idx(d+1)).enumerate() { nn[k] = nn[j+1] }
        }

        // [Set up a graph with n vertices 13]

        // We want to make the subroutine idiot-proof, so we use
        // floating-point arithmetic to make sure that boards with
        // more than a billion cells have not been specified.

        const MAX_NNN: f32 = 1_000_000_000.0;
        let (mut n, mut nnn) = (1, 1.0);
        for j in 1..d+1 {
            nnn *= nn[j] as f32;
            if nnn > MAX_NNN {
                panic!("very_bad_specs d: {} nn: {:?}",
                       d, nn.slice(1, d+1));
            }
            // this multiplication cannot cause integer overflow
            n *= nn[j];
        }
        vertices = Graph::new_vertices(n);
        let new_graph_id = format!("board({},{},{},{},{},{},{})",
                                   n1, n2, n3, n4, piece, wrap,
                                   if directed { 1 } else { 0 });
        let new_graph_util_types = [Z,Z,Z,I,I,I,Z,Z,Z,Z,Z,Z,Z,Z];
        debug!("created {} vertices for graph {}", n, new_graph_id);

        // [Give names to the vertices 14]

        // @ The symbolic name of a board position like $(3,1)$ will
        // be the string `\.{3.1}'. The first three coordinates are
        // also stored as integers, in utility fields |x.I|, |y.I|,
        // and |z.I|, because immediate access to those values will be
        // helpful in certain applications. (The coordinates can, of
        // course, always be recovered in a slower fashion from the
        // vertex name, via |sscanf|.)

        // The process of assigning coordinate values and names is
        // equivalent to adding unity in a mixed-radix number
        // system. Vertex $(x_1,\ldots,x_d)$ will be in position
        // $x_1n_2\ldots n_d+\cdots+x_{d-1}n_d+x_d$ relative to the
        // first vertex of the new graph; therefore it is also
        // possible to deduce the coordinates of a vertex from its
        // address.

        nn[0] = 0;
        xx[0] = 0; xx[1] = 0; xx[2] = 0; xx[3] = 0;
        for k in 4..d+1 { xx[k] = 0; }

        for mut v in vertices.iter_mut() {
            let mut q = String::new();
            for k in 1..d+1 {
                q.push_str(format!(".{}", xx[k]).as_slice());
            }
            v.name = q.chars().skip(1).collect(); // omit char 0, which is '.'
            v.x = Util::I(xx[1]); v.y = Util::I(xx[2]); v.z = Util::I(xx[3]);
            debug!("named vertex {}", v);

            let mut k = d;
            while xx[k] + 1 == nn[k] {
                xx[k] = 0;
                k -= 1;
            }
            if k == 0 { break } // "carry" has occurred all the way to the left
            xx[k] += 1; // increase coordinate k
        }

        let vertices = area.alloc(move |:| vertices);

        new_graph = Graph::new_graph(&vertices[], area);
        new_graph.id = new_graph_id;
        new_graph.util_types = new_graph_util_types;

        // [Insert arcs or edges for all legal moves 15]

        // @ Now we come to a slightly tricky part of the routine: the
        // move generator.  Let $p=|piece|$. The outer loop of this
        // procedure runs through all solutions of the equation
        // $\delta_1^2 + ... +\delta_d^2=p$, where the $\delta$'s are
        // nonnegative integers.
        //
        // Within that loop, we attach signs to the $\delta$'s, but we
        // always leave $\delta_k$ positive if $\delta_1=
        // \cdots=\delta_{k-1}=0$.
        //
        // For every such vector~$\delta$, we generate moves from |v|
        // to $v+\delta$ for every vertex |v|. When |directed=0|, we
        // use |gb_new_edge| instead of |gb_new_arc|, so that the
        // reverse arc from $v+\delta$ to~|v| is also generated.

        // [Initialize the |wr|, |sig|, and |del| tables 16];

        // @ The \CEE/ language does not define |>>| unambiguously. If |w| is negative,
        // the assignment `|w>>=1|' here should keep |w| negative.
        // (However, this technicality doesn't matter except in highly unusual cases
        // when there are more than 32 dimensions.)
        let mut w = wrap;
        for k in 1..d+1 {
            wr[k] = w & 1;
            del[k] = 0; sig[k] = 0;

            // (check claim above about the assignment)
            assert!(w >= 0 || (w >> 1) < 0);

            w >>= 1;
        }
        sig[0] = 0; del[0] = 0; sig[d+1] = 0;

        p = piece;
        if p < 0 { p = -p; }
        loop {
            // [Advance to the next nonnegative |del| vector, or |break| if done 17];
            k = d;
            while (sig[k] + (del[k] + 1) * (del[k] + 1)) > p {
                del[k] = 0;
                k -= 1;
            }
            if k == 0 { break; }
            del[k] += 1;
            sig[k + 1] = sig[k] + del[k] * del[k];
            for k in k+1..d+1 { sig[k+1] = sig[k]; }
            if sig[d+1] < p { continue; }
            debug!("  Advanced to next nonneg del vector, del={:?}",
                   &del[1us..idx(d+1)]);
            loop {
                debug!("    generating moves for del={:?}",
                       &del[1us..idx(d+1)]);
                // [Generate moves for the current |del| vector 19];
                for k in 1..d+1 { xx[k] = 0 }
                for v in vertices.iter() {
                    debug!("      generating moves from v={} corresponding to del={:?}",
                           v, &del[1us..idx(d+1)]);
                    // [Generate moves from v corresponding to del 20];

                    // The legal moves when |piece| is negative are
                    // derived as follows, in the presence of possible
                    // wraparound: Starting at $(x_1,\ldots,x_d)$, we
                    // move to $(x_1+\delta_1,\ldots,x_d+\delta_d)$,
                    // $(x_1+2\delta_1,\ldots, x_d+2\delta_d)$,~\dots,
                    // until either coming to a position with a
                    // nonwrapped coordinate out of range or coming
                    // back to the original point.
                    //
                    // A subtle technicality should be noted: When
                    // coordinates are wrapped and |piece>0|,
                    // self-loops are possible---for example, in
                    // |board(1,0,0,0,1,1,1)|.  But self-loops never
                    // arise when |piece<0|.

                    for k in 1..d+1 { yy[k] = xx[k] + del[k] }
                    'gen_moves_from_v: for l in (1..) {
                        // [Correct for wraparound, or goto no_more if off the board 22]
                        for k in 1..d+1 {
                            if yy[k] < 0 {
                                if wr[k] == 0 { break 'gen_moves_from_v; }
                                loop { yy[k] += nn[k];
                                       if yy[k] >= 0 { break; } }
                            } else if yy[k] >= nn[k] {
                                if wr[k] == 0 { break 'gen_moves_from_v; }
                                loop { yy[k] -= nn[k];
                                       if yy[k] < nn[k] { break; } }
                            }
                        }

                        if piece < 0 {
                            // [Go to no_more if yy == xx 21]
                            if (1..d+1).all(|k| yy[k] == xx[k]) {
                                break 'gen_moves_from_v;
                            }
                        }

                        debug!("        Record a legal move from xx={:?} to yy={:?}",
                               &xx[1us..idx(d+1)], &yy[1us..idx(d+1)]);
                        // [Record a legal move from xx to yy 23]
                        j = yy[1];
                        for k in 2..d+1 { j = nn[k] * j + yy[k] }
                        if directed {
                            new_graph.new_arc(v, &vertices[idx(j)], l);
                        } else {
                            new_graph.new_edge(v, &vertices[idx(j)], l);
                        }

                        if piece > 0 { break 'gen_moves_from_v; }
                        for k in 1..d+1 { yy[k] += del[k]; }
                    }
                    // 'no_more:

                    k = d; while xx[k] + 1 == nn[k] {
                        xx[k] = 0;
                        k -= 1;
                    }
                    if k == 0 { break; } // "carry" has occurred all the way to left
                    xx[k] += 1; // increase coordinate k
                }

                // [Advance to the next signed |del| vector, or restore |del|
                //     to nonnegative values and |break| 18];
                k = d;
                while del[k] <= 0 {
                    del[k] = -del[k];
                    k -= 1;
                }
                if sig[k] == 0 { break } // all but del[k] were negative or zero
                debug!("    Advance to next signed del vector: del={:?}",
                       &del[1us..d+1]);
                del[k] = -del[k]; // some entry preceding del[k] is positive
            }
        }

        return new_graph;
    }
}

#[test]
fn board_2x2_wazir() {
    let mut c = Context::new();
    let b = c.board(2,2,0,0, 1, 0, false);
    println!("b: {:E}", b);
    panic!("b: {}", b.id);
}
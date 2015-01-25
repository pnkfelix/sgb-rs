//! Introduction. This GraphBase module contains six subroutines that generate
//! standard graphs of various types, together with six routines that combine or
//! transform existing graphs.
//!
//! Simple examples of the use of these routines can be found in the
//! demonstration programs {\sc QUEEN} and {\sc QUEEN\_WRAP}.

use ::{Long};
use ::graph::{Area, Graph};

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

/// Classic interface for SGB basic functions.  Notably, all
/// parameters are all numerically oriented.
trait Classic {
    fn board(&mut self, n1: Long, n2: Long, n3: Long, n4: Long,
             piece: Long, wrap: Long, directed: Long) -> Graph;

    fn simplex(&mut self) -> Graph { unimplemented!() }
    fn subsets(&mut self) -> Graph { unimplemented!() }
    fn perms(&mut self) -> Graph { unimplemented!() }
    fn parts(&mut self) -> Graph { unimplemented!() }
    fn binary(&mut self) -> Graph { unimplemented!() }
    fn complement(&mut self) -> Graph { unimplemented!() }
    fn gunion(&mut self) -> Graph { unimplemented!() }
    fn intersection(&mut self) -> Graph { unimplemented!() }
    fn lines(&mut self) -> Graph { unimplemented!() }
    fn product(&mut self) -> Graph { unimplemented!() }
    fn induced(&mut self) -> Graph { unimplemented!() }
}

impl Classic for Context {
    fn board(&mut self, n1: Long, n2: Long, n3: Long, n4: Long,
             piece: Long, wrap: Long, directed: Long) -> Graph {
        Context::board(self, (n1, n2, n3, n4, piece, wrap, directed))
    }
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
    pub fn board<BD: board::BoardDescription>(&mut self, bd: BD) -> Graph {
        board::board(self, bd)
    }
}

pub mod board;

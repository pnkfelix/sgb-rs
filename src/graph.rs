use self::UtilType::{I,Z};
use ::{Long, idx, long};

use arena;

use std::cell::Cell;
use std::default::Default;
use std::fmt;
use std::iter;
use std::mem;

#[derive(Copy)]
pub struct Context {
    /// nonzero if "verbose" output is desired
    pub verbose: u32,
    /// nonzero if graph generator returns null pointer (FIXME)
    pub panic_code: PanicCode,
}

#[derive(Copy)]
pub enum PanicCode {
    /// A previous memory request failed
    AllocFault = -1,
    /// The current memory request failed
    NoRoom = 1,
    /// error detected at beginning of .dat file
    EarlyDataFault = 10,
    /// error detected at end of .dat file
    LateDataFault = 11,
    /// error detected while reading .dat file
    SyntaxError = 20,
    /// Parameter out of range or otherwise disallowed
    BadSpecs = 30,
    /// Parameter far out of range or otherwise stupid
    VeryBadSpecs = 40,
    /// Graph parameter is null
    MissingOperand = 50,
    /// Graph parameter does not obey assumptions
    InvalidOperand = 60,
    // "this can't happen"
    Impossible = 90,
}

/// The suffixes .V , .A, .G, and .S on the name of a utility variable
/// mean that the variable is a pointer to a vertex, arc, graph, or
/// string, respectively; the suffix .I means that the variable is an
/// integer. (We use one-character names because such names are easy
/// to type when debugging.)
pub enum Util<'v>  {
    V(&'v Vertex<'v>),
    A(&'v Arc<'v>),
    G(&'v Graph<'v>),
    S(&'v str),
    I(Long),
    Z,
}

impl<'v> Default for Util<'v>  {
    fn default() -> Util<'v> {
        Util::Z
    }
}

/// Each Vertex has two standard fields and six utility fields; hence
/// it occupies 32 bytes on most systems, not counting the memory
/// needed for supplementary string data. The standard fields are
///
/// - arcs, a pointer to an Arc;
/// - name, a pointer to a string of characters.
///
/// If v points to a Vertex and v⃗arcs is Λ, there are no arcs
/// emanating from v. But if v⃗arcs is non-Λ, it points to an Arc
/// record representing an arc from v, and that record has a next
/// field that points in the same way to the representations of all
/// other arcs from v.
///
/// The utility fields are called u, v, w, x, y, z. Macros can be used
/// to give them syntactic sugar in particular applications. They are
/// typically used to record such things as the in-degree or
/// out-degree, or whether a vertex is ‘marked’. Utility fields might
/// also link the vertex to other vertices or arcs in one or more
/// lists.
pub struct Vertex<'v>  {
    /// linked-list of arcs coming out of this vertex
    arcs: Cell<Option<&'v Arc<'v>>>,
    /// string identifying this vertex symbolically
    pub name: String,
    /// multipurpose field
    pub u: Util<'v>,
    /// multipurpose field
    pub v: Util<'v>,
    /// multipurpose field
    pub w: Util<'v>,
    /// multipurpose field
    pub x: Util<'v>,
    /// multipurpose field
    pub y: Util<'v>,
    /// multipurpose field
    pub z: Util<'v>,
}

impl<'v> Default for Vertex<'v>  {
    fn default() -> Vertex<'v> {
        Vertex {
            arcs: Cell::new(None),
            name: String::new(),
            u: Default::default(),
            v: Default::default(),
            w: Default::default(),
            x: Default::default(),
            y: Default::default(),
            z: Default::default(),
        }
    }
}

/// Each Arc has three standard fields and two utility fields. Thus it
/// occupies 20 bytes on most computer systems. The standard fields
/// are
///
/// - tip, a pointer to a Vertex;
/// - next, a pointer to an Arc;
/// - len, a (long) integer.
///
/// If a points to an Arc in the list of arcs from vertex v, it
/// represents an arc of length a⃗len from v to a⃗tip, and the next arc
/// from v in the list is represented by a⃗next.
///
/// The utility fields are called a and b.
pub struct Arc<'v>  {
    /// the arc points to this vertex
    pub tip: &'v Vertex<'v>,
    /// if non-null, another arc pointing from the same vertex
    pub next: Option<&'v Arc<'v>>,
    /// length of this arc
    pub len: Long,
    /// multipurpose field
    pub a: Util<'v>,
    /// multipurpose field
    pub b: Util<'v>,
}

pub struct Area {
    arena: arena::Arena
}

impl Area {
    pub fn new() -> Area { Default::default() }
    pub fn alloc<T, F>(&self, op: F) -> &mut T where F: FnOnce() -> T {
        self.arena.alloc(op)
    }
}

impl Default for Area {
    fn default() -> Area {
        Area { arena: arena::Arena::new() }
    }
}

/// either I (denoting a long integer), S (denoting a pointer to a
/// string), V (denoting a pointer to a Vertex), A (denoting a
/// pointer to an Arc), G (denoting a pointer to a Graph), or Z
/// (denoting an unused field that remains zero)
#[derive(Copy)]
#[repr(i8)]
pub enum UtilType {
    I = 'I' as i8,
    S = 'S' as i8,
    V = 'V' as i8,
    A = 'A' as i8,
    G = 'G' as i8,
    Z = 'Z' as i8,
}

/// Now we’re ready to look at the Graph type. This is a data
/// structure that can be passed to an algorithm that operates on
/// graphs—to find minimum spanning trees, or strong components, or
/// whatever.  A Graph record has seven standard fields and six
/// utility fields. The standard fields are
///
/// -￼vertices, a pointer to an array of Vertex records;
/// - n, the total number of vertices;
/// - m, the total number of arcs;
/// - id, a symbolic identification giving parameters of the GraphBase procedure that generated this graph;
/// - util_types, a symbolic representation of the data types in utility fields;
/// - data, an Area used for Arc storage and string storage;
/// - aux_data, an Area used for auxiliary information that some users might want to discard.
///
/// ￼￼The utility fields are called uu, vv, ww, xx, yy, and zz.
///
/// As a consequence of these conventions, we can visit all arcs of a graph g by using the following program:
///
/// ```text
/// let mut a: &Arc;
/// for v in g.vertices.iter() {
///     a = v.arcs.get();
///     while let Some(arc) = a {
///        a = arc.next;
///        visit (v, a);
///     }
/// }
/// ```
pub struct Graph<'v>  {
    /// the vertex array
    vertices: &'v [Vertex<'v>],
    /// total number of vertices
    pub n: Long,
    /// total number of arcs
    pub m: Long,
    /// GraphBase identification
    pub id: String,
    /// usage of utility fields
    ///
    /// The util types field should always hold a string of length 14,
    /// followed as usual by a null character to terminate that
    /// string. The first six characters of util types specify the
    /// usage of utility fields u, v, w, x, y, and z in Vertex
    /// records; the next two characters give the format of the
    /// utility fields in Arc records; the last six give the format of
    /// the utility fields in Graph records. Each character should be
    /// either I (denoting a long integer), S (denoting a pointer to a
    /// string), V (denoting a pointer to a Vertex), A (denoting a
    /// pointer to an Arc), G (denoting a pointer to a Graph), or Z
    /// (denoting an unused field that remains zero). The default for
    /// util types is "ZZZZZZZZZZZZZZ", when none of the utility
    /// fields is being used.
    ///
    /// For example, suppose that a bipartite graph g is using field
    /// g⃗uu.I to specify the size of its first part. Suppose further
    /// that g has a string in utility field a of each Arc and uses
    /// utility field w of Vertex records to point to an Arc. If g
    /// leaves all other utility fields untouched, its util types
    /// should be "ZZAZZZSZIZZZZZ".
    ///
    /// The util types string is presently examined only by the save
    /// graph and restore graph routines, which convert GraphBase
    /// graphs from internal data structures to symbolic external
    /// files and vice versa. Therefore users need not update the util
    /// types when they write algorithms to manipulate graphs, unless
    /// they are going to use save graph to output a graph in symbolic
    /// form, or unless they are using some other GraphBase-related
    /// software that might rely on the conventions of util types
    /// . (Such software is not part of the “official” Stanford
    /// GraphBase, but it might conceivably exist some day.)
    pub util_types: [UtilType; 14],
    /// the main data blocks
    pub data: &'v Area,
    /// subsidiary data blocks
    pub aux_data: Area,
    /// multipurpose field
    pub uu: Util<'v>,
    /// multipurpose field
    pub vv: Util<'v>,
    /// multipurpose field
    pub ww: Util<'v>,
    /// multipurpose field
    pub xx: Util<'v>,
    /// multipurpose field
    pub yy: Util<'v>,
    /// multipurpose field
    pub zz: Util<'v>,
}

pub const ID_FIELD_SIZE: Long = 161;

pub const EXTRA_N: Long = 4;

impl<'v> Graph<'v>  {
    /// Some applications of bipartite graphs require all vertices of
    /// the first part to appear at the beginning of the vertices
    /// array. In such cases, utility field uu .I is traditionally
    /// given the symbolic name n 1 , and it is set equal to the size
    /// of that first part. The size of the other part is then g⃗n − g⃗n
    /// 1 .
    pub fn mark_bipartitle(&mut self, n1: Long) {
        self.uu = Util::I(n1);
        self.util_types[8] = I
    }

    /// A new graph is created by calling gb new graph(n), which
    /// returns a pointer to a Graph record for a graph with n
    /// vertices and no arcs. This function also initializes several
    /// private variables that are used by the gb new arc, gb new
    /// edge, gb virgin arc, and gb save string procedures below.
    ///
    /// We actually reserve space for n + extra n vertices, although
    /// claiming only n, because several graph manipulation algorithms
    /// like to add a special vertex or two to the graphs they deal
    /// with.
    pub fn new_vertices(n: Long) -> Vec<Vertex<'v>> {
        let mut vertices = Vec::with_capacity(idx(n + EXTRA_N));
        for _ in (0..n+EXTRA_N) {
            let v : Vertex = Default::default();
            vertices.push(v);
        }
        vertices
    }

    pub fn new_graph(vertices: &'v [Vertex<'v>], data: &'v Area) -> Graph<'v> {
        let n = long(vertices.len()) - EXTRA_N;
        Graph {
            vertices: vertices,
            n: n,
            m: 0,
            id: format!("gb_new_graph({})", n),
            util_types: [Z, Z, Z, Z,
                         Z, Z, Z, Z,
                         Z, Z, Z, Z,
                         Z, Z,],
            data: data,
            aux_data: Default::default(),
            uu: Default::default(),
            vv: Default::default(),
            ww: Default::default(),
            xx: Default::default(),
            yy: Default::default(),
            zz: Default::default(),
        }
    }

    /// The id field of a graph is sometimes manufactured from the id
    /// field of another graph. The following routines do this without
    /// allowing the string to get too long after repeated copying.
    pub fn make_compound_id(&mut self, s1: &str, gg: &Graph, s2: &str) {
        let avail = idx(ID_FIELD_SIZE - long(s1.len()) - long(s2.len()));
        if gg.id.len() < avail {
            self.id = format!("{}{}{}", s1, gg.id, s2);
        } else {
            self.id = format!("{}{}...{}", s1, gg.id.slice_to(avail - 5), s2);
        }
    }

    /// The id field of a graph is sometimes manufactured from the id
    /// field of another graph. The following routines do this without
    /// allowing the string to get too long after repeated copying.
    pub fn make_double_compound_id(&mut self, s1: &str,
                               gg: &Graph, s2: &str,
                               ggg: &Graph, s3: &str) {
        let avail = idx(ID_FIELD_SIZE - long(s1.len()) - long(s2.len()) - long(s3.len()));
        if gg.id.len() + ggg.id.len() < avail {
            self.id = format!("{}{}{}{}{}", s1, gg.id, s2, ggg.id, s3);
        } else {
            self.id = format!("{}{}{}{}{}",
                              s1, gg.id.slice_to(avail/2 - 5),
                              s2, ggg.id.slice_to((avail - 9)/2),
                              s3);
        }
    }

    /// The routine |gb_new_arc(u,v,len)| creates a new arc of length
    /// |len| from vertex~|u| to vertex~|v|. The arc becomes part of
    /// the graph that was most recently created by
    /// |gb_new_graph|---the graph pointed to by the private variable
    /// |cur_graph|. This routine assumes that |u| and |v| are both
    /// vertices in |cur_graph|.
    ///
    /// The new arc will be pointed to by |u->arcs|, immediately after
    /// |gb_new_arc(u,v,len)| has acted. If there is no room for the
    /// new arc, |gb_trouble_code| is set nonzero, but |u->arcs| will
    /// point to the non-|NULL| record |dummy_arc| so that additional
    /// information can safely be stored in its utility fields without
    /// risking system crashes before |gb_trouble_code| is tested.
    /// However, the linking structure of arcs is apt to be fouled up
    /// in such cases; programs should make sure that
    /// |gb_trouble_code==0| before doing any extensive computation on
    /// a graph.
    pub fn new_arc(&mut self, u: &Vertex<'v>, v: &'v Vertex<'v>, len: Long) {
        debug!("new_arc(u={}, v={}, len={})", u, v, len);
        let cur_arc : &Arc = self.data.arena.alloc(|| Arc {
            tip: v,
            next: u.arcs.get(),
            len: len,
            a: Default::default(),
            b: Default::default(),
        });
        u.arcs.set(Some(cur_arc));
        self.m += 1;
    }

    /// An undirected graph has “edges” instead of arcs. We represent
    /// an edge by two arcs, one going each way.
    ///
    /// The fact that arcs per block is even means that the gb new
    /// edge routine needs to call gb virgin arc only once instead of
    /// twice.
    ///
    /// Caveats: This routine, like gb new arc, should be used only
    /// after gb new graph has caused the private variable cur graph
    /// to point to the graph containing the new edge. The routine gb
    /// new edge must not be used together with gb new arc or gb
    /// virgin arc when building a graph, unless gb new arc and gb
    /// virgin arc have been called an even number of times before gb
    /// new edge is invoked.
    ///
    /// The new edge will be pointed to by u⃗arcs and by v⃗arcs
    /// immediately after gb new edge has created it, assuming that u
    /// ̸= v. The two arcs appear next to each other in memory; indeed,
    /// gb new edge rigs things so that v⃗arcs is u⃗arcs + 1 when u < v.
    ///
    /// On many computers it turns out that the first Arc record of
    /// every such pair of arcs will have an address that is a
    /// multiple of 8, and the second Arc record will have an address
    /// that is not a multiple of 8 (because the first Arc will be 20
    /// bytes long, and because calloc always returns a multiple of
    /// 8). However, it is not safe to assume this when writing
    /// portable code. Algorithms for undirected graphs can still make
    /// good use of the fact that arcs for edges are paired, without
    /// needing any mod 8 assumptions, if all edges have been created
    /// and linked into the graph by gb new edge: The inverse of an
    /// arc a from u to v will be arc a+1 if and only if u < v or
    /// a⃗next = a + 1; it will be arc a − 1 if and only if u ≥ v and
    /// a⃗next ̸= a + 1. The condition a⃗next =a+1 can hold only if u=v.
    pub fn new_edge(&mut self, u: &'v Vertex<'v>, v: &'v Vertex<'v>, len: Long) {
        debug!("new_edge(u={}, v={}, len={})", u, v, len);
        let u_first = unsafe {
            mem::transmute::<_,usize>(&*u) < mem::transmute::<_,usize>(&*v)
        };

        let u_arcs_old = u.arcs.get();
        let v_arcs_old = v.arcs.get();
        let arcs: &(Arc, Arc) = if u_first {
            self.data.arena.alloc(
                || (Arc { tip: v,
                          next: u_arcs_old,
                          len: len,
                          a: Default::default(),
                          b: Default::default(),
                },
                    Arc { tip: u,
                          next: v_arcs_old,
                          len: len,
                          a: Default::default(),
                          b: Default::default(),
                    }))
        } else {
            self.data.arena.alloc(
                || (Arc { tip: u,
                          next: v_arcs_old,
                          len: len,
                          a: Default::default(),
                          b: Default::default(),
                },
                    Arc { tip: v,
                          next: u_arcs_old,
                          len: len,
                          a: Default::default(),
                          b: Default::default(),
                    }))
        };
        if u_first {
            u.arcs.set(Some(&arcs.0));
            v.arcs.set(Some(&arcs.1));
        } else {
            u.arcs.set(Some(&arcs.1));
            v.arcs.set(Some(&arcs.0));
        }
        self.m += 2;
    }
}

impl<'v> Graph<'v> {
    fn edges(&self) -> EdgeIterator<'v> {
        EdgeIterator {
            vertices: self.vertices,
            curr_ver: 0,
            next_ver: 1,
            next_arc: None,
        }
    }
}

pub struct EdgeIterator<'v> {
    vertices: &'v [Vertex<'v>],
    curr_ver: usize,
    next_ver: usize,
    next_arc: Option<&'v Arc<'v>>,
}

impl<'v> EdgeIterator<'v> {
    fn try_fill_next_arc(&mut self) {
        while self.next_arc.is_none() {
            if self.next_ver >= self.vertices.len() { return; }
            self.curr_ver = self.next_ver;
            let v = &self.vertices[self.curr_ver];
            self.next_ver += 1;
            self.next_arc = v.arcs.get();
        }
    }
}

impl<'v> iter::Iterator for EdgeIterator<'v> {
    type Item = (&'v Vertex<'v>, &'v Arc<'v>);
    fn next(&mut self) -> Option<(&'v Vertex<'v>, &'v Arc<'v>)> {
        self.try_fill_next_arc();
        if let Some(a) = self.next_arc {
            self.next_arc = a.next;
            Some((&self.vertices[self.curr_ver], a))
        } else {
            None
        }
    }
}

impl<'v> fmt::String for Vertex<'v> {
    fn fmt(&self, w: &mut fmt::Formatter) -> fmt::Result {
        write!(w, "{}", self.name.as_slice())
    }
}

impl<'v> fmt::UpperExp for Graph<'v> {
    fn fmt(&self, w: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(w, "Graph {{ nodes: ["));
        let mut saw_node = false;
        for v in self.vertices.slice_to(idx(self.n)).iter() {
            if saw_node { try!(write!(w, ", ")); }
            try!(write!(w, "{}", v));
            saw_node = true;
        }

        try!(write!(w, "], edges: ["));
        let mut saw_edge = false;
        for (v, a) in self.edges() {
            if saw_edge { try!(write!(w, ", ")); }
            try!(write!(w, "{} -> {}", v, a.tip));
            saw_edge = true;
        }
        write!(w, "] }}")
    }
}

#[test]
fn main_test() {
    // <create a small graph>
    //
    // (indeed, it is a *very* small graph.  And very little
    //  functionality is provided by this module in terms of
    //  traversing/manipulating graphs)

    let mut vertices = Graph::new_vertices(2);
    {
        let (u, v) = vertices.split_at_mut(1);
        let u = &mut u[0];
        let v = &mut v[0];
        u.name = format!("vertex 0");
        v.name = format!("vertex 1");
    }

    let data: Area = Default::default();
    let mut g = Graph::new_graph(vertices.as_slice(), &data);

    let (u, v) = g.vertices.split_at(1);
    let u = &u[0];
    let v = &v[0];

    // (We aren't using the memory allocation scheme outlined by Knuth
    // in the SGB, so there's no analog to his "intentional errors".)
    // <test some intentional errors>
    assert!(u.name != v.name);

    g.new_edge(v, u, -1);
    g.new_edge(u, u,  1);
    g.new_arc(v, u, -1);

    let (u, v) = g.vertices.split_at(1);
    let u = &u[0];
    let v = &v[0];
    assert!(u.name != v.name);

    let vc = v.name.char_at(7) as i32;
    let vnc = v.arcs.get().unwrap().next.unwrap().tip.name.char_at(7) as i32;
    // '1' +   2 != '0' + 5 - 2
    if vc + g.n != vnc + g.m - 2 {
        panic!("Sorry, the graph data structures aren't working yet. \
                vc: {} g.n: {} vnc: {} g.m: {}", vc, g.n, vnc, g.m);
    }
}

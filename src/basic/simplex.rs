use basic::{Context};
use graph::{Graph};

pub trait SimplexDescription {

}

// (see documentation for `Context::simplex`)
pub fn simplex<SD:SimplexDescription>(c: &mut Context, sd: SD) -> Graph {
    let _ = (c, sd);
    unimplemented!()
}

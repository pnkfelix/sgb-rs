#![allow(unstable)]

extern crate arena;
#[macro_use]
extern crate log;

use std::num::ToPrimitive;

pub mod graph;
pub mod io;
pub mod basic;

pub type Long = i32;
fn idx<T:ToPrimitive>(t: T) -> usize { t.to_uint().unwrap() }
fn long<T:ToPrimitive>(t: T) -> Long { t.to_i32().unwrap() }


#[test]
fn it_works() {
}

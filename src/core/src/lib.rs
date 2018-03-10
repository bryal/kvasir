extern crate rand;

use std::io::{self, BufRead};

pub mod string;

#[no_mangle]
pub extern "C" fn read_line() -> String {
    let stdin = io::stdin();
    let s = stdin
        .lock()
        .lines()
        .next()
        .expect("there was no next line")
        .expect("the line could not be read");
    s
}

#[no_mangle]
pub extern "C" fn read_int64() -> i64 {
    read_line().parse().expect("Could not parse as Int64")
}

#[no_mangle]
pub extern "C" fn read_uint64() -> u64 {
    read_line().parse().expect("Could not parse as UInt64")
}

#[no_mangle]
pub extern "C" fn print_int64(n: i64) {
    println!("{}", n)
}

#[no_mangle]
pub extern "C" fn print_uint64(n: u64) {
    println!("{}", n)
}

#[no_mangle]
pub extern "C" fn print_float64(x: u64) {
    println!("{}", x)
}

extern crate libc;
extern crate rand;

use std::io::{self, BufRead};
use std::mem::size_of;
use libc::malloc;
use string::*;

pub mod string;

type Rc<T> = *mut (u64, T);

unsafe fn new_rc<T>(data: T) -> Rc<T> {
    let rc = malloc(size_of::<(u64, T)>()) as *mut (u64, T);
    *rc = (1, data);
    rc
}

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

#[no_mangle]
pub unsafe extern "C" fn _panic(s: KvsString) {
    println!(
        "Kvasir thread panicked with message: {}",
        kvs_string_to_string(s)
    );
    std::process::exit(1)
}

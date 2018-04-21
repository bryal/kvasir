use std::{char, slice, str};
use new_rc;

// Representation of a kvasir `String`
//
// 1. It's an algebraic data type
// 2. ADTs are implemented as tagged unions
// 3. The tag of a union is always 16-bit.
// 4. The value of the tag is equal to the index of the variant in
//    the variant sequence in the `data` special form in the
//    kvasir source.
// 5. The union part is of some arbitrary type, of which the size is
//    equal to the size of the largest variant of the ADT,
//    excluding the tag and optional wrapping pointer.
// 6. `String` is a recursive type, and therefore will always be
//    stored behind a reference counted pointer
// 7. Refcount pointers are represented as a pointer to a pair of
//    the 64-bit reference count, and the arbitrarily sized data.

// Largest   = { i32, String }
// String_in = { i16, LARGEST }
// String    = { i64, String_in }*

#[repr(u32)]
#[derive(Debug)]
pub enum Tag {
    Empty,
    Cons,
}

#[repr(C)]
pub union Variant {
    empty: (),
    cons: (u32, String_),
}

#[repr(C)]
pub struct String_in {
    tag: Tag,
    data: Variant,
}

pub type String_ = *mut (u64, String_in);

#[repr(C)]
#[derive(Debug)]
pub struct KvsString(String_);

impl KvsString {
    unsafe fn empty() -> KvsString {
        let empty_in = String_in {
            tag: Tag::Empty,
            data: Variant { empty: () },
        };
        KvsString(new_rc(empty_in))
    }

    unsafe fn cons<T: Into<u32>>(c: T, rest: KvsString) -> KvsString {
        let cons_in = String_in {
            tag: Tag::Cons,
            data: Variant {
                cons: (c.into(), rest.0),
            },
        };
        KvsString(new_rc(cons_in))
    }

    unsafe fn refcount(&self) -> u64 {
        (*self.0).0
    }

    unsafe fn data(&self) -> &String_in {
        &(*self.0).1
    }

    unsafe fn split_first(&self) -> Option<(u32, Self)> {
        let s = self.data();
        match s.tag {
            Tag::Empty => None,
            Tag::Cons => Some((s.data.cons.0, KvsString(s.data.cons.1))),
        }
    }

    unsafe fn first(&self) -> Option<u32> {
        self.split_first().map(|(c, _)| c)
    }
}

pub unsafe fn kvs_string_to_string(mut s: KvsString) -> String {
    let mut buf = String::new();
    loop {
        if let Some((c, s_)) = s.split_first() {
            buf.push(char::from_u32(c).unwrap());
            s = s_;
        } else {
            break;
        }
    }
    buf
}

#[no_mangle]
pub unsafe extern "C" fn str_lit_to_string((len, ptr): (usize, *const u8)) -> KvsString {
    let slice = slice::from_raw_parts(ptr, len);
    let s = str::from_utf8(slice).unwrap();
    s.chars()
        .rev()
        .fold(KvsString::empty(), |acc, c| KvsString::cons(c, acc))
}

#[no_mangle]
pub unsafe extern "C" fn c_display(s: KvsString) {
    println!("{}", kvs_string_to_string(s))
}

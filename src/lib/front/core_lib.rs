// The MIT License (MIT)
//
// Copyright (c) 2015 Johan Johansson
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

use std::iter::FromIterator;
use std::collections::HashMap;
use super::Type;

pub fn core_consts() -> HashMap<&'static str, Type> {
	HashMap::from_iter(vec![
		("+", Type::new_fn(vec![Type::new_basic("i64"), Type::new_basic("i64")], Type::new_basic("i64"))),
		("-", Type::new_fn(vec![Type::new_basic("i64"), Type::new_basic("i64")], Type::new_basic("i64"))),
		("*", Type::new_fn(vec![Type::new_basic("i64"), Type::new_basic("i64")], Type::new_basic("i64"))),
		("/", Type::new_fn(vec![Type::new_basic("i64"), Type::new_basic("i64")], Type::new_basic("i64"))),
		("=", Type::new_fn(vec![Type::new_basic("i64"), Type::new_basic("i64")], Type::new_bool())),
		("<", Type::new_fn(vec![Type::new_basic("i64"), Type::new_basic("i64")], Type::new_bool())),
		(">", Type::new_fn(vec![Type::new_basic("i64"), Type::new_basic("i64")], Type::new_bool())),
		("true", Type::new_bool()),
		("false", Type::new_bool()),
		("println!", Type::new_fn(vec![Type::new_basic("&str"), Type::new_poly("T")], Type::new_nil())),
	])
}

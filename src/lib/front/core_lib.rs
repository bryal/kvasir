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
use lib::front::parse::Type;

macro_rules! core_ty {
	($constr:expr; $($args:expr),*) => {
		Type::Construct($constr, vec![$(Type::Basic($args)),*])
	}
}

lazy_static! {
pub static ref CORE_CONSTS_TYPES: HashMap<&'static str, Type<'static>> = HashMap::from_iter(vec![
	("+", core_ty!("proc"; "Int64", "Int64", "Int64")),
	("-", core_ty!("proc"; "Int64", "Int64", "Int64")),
	("*", core_ty!("proc"; "Int64", "Int64", "Int64")),
	("/", core_ty!("proc"; "Int64", "Int64", "Int64")),
	("=", core_ty!("proc"; "Int64", "Int64", "Bool")),
	("<", core_ty!("proc"; "Int64", "Int64", "Bool")),
	(">", core_ty!("proc"; "Int64", "Int64", "Bool")),
	("and", core_ty!("proc"; "Bool", "Bool", "Bool")),
	("or", core_ty!("proc"; "Bool", "Bool", "Bool"))
]);
}

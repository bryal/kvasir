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

use std::collections::{ HashMap, HashSet };
use std::mem::replace;
use front::AST;

impl AST {
	pub fn remove_unused_consts(&mut self) {
		let mut used_consts = HashSet::new();
		let mut const_defs = ConstDefScopeStack::new();

		const_defs.push(wrap_defs_some(replace(&mut self.const_defs, HashMap::new())));

		const_defs.do_for_item_at_height("main", 0, |const_defs, main| {
			let mut env = Env::new(const_defs, Vec::new());
			main.infer_types(&Type::new_nil(), &mut env);
			env.const_defs
		});

		if const_defs.height() != 1 {
			panic!("AST::infer_types: Stack is not single scope");
		}

		self.const_defs = unwrap_option_defs(const_defs.pop().unwrap())




		let mut const_defs = ConstDefScopeStack::new();

		// Push the module scope on top of the stack
		const_defs.push(vec_to_def_scope(replace(&mut self.const_defs, Vec::new())));

		let mut main = match const_defs.get_at_height_mut("main", 0) {
			Some(main) => main.replace_into_def().unwrap(),
			None => panic!("AST::infer_types: No main function found")
		};

		let mut env = Env{
			core_consts: core_consts(),
			const_defs: const_defs,
			var_types: Vec::new()
		};

		main.infer_types(&mut env);

		env.const_defs.get_at_height_mut("main", 0).unwrap().insert_def(main);

		if env.const_defs.height() != 1 {
			panic!("AST::infer_types: Stack is not single scope");
		}

		self.const_defs = def_scope_to_vec(env.const_defs.pop().unwrap())
	}
}

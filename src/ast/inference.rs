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

//! Infer types where explicit type signatures are not available

// TODO: Check for mutual recursion when infering types. Maybe list of function call ancestry.
// Like: foo calling bar calling baz calling foo => ERROR

use super::{ Item, Type };

impl super::FnDef {
	// TODO: Infer types for incomplete function sig. E.g. inc: <→ u32 _> => inc: <→ u32 u32>
	fn infer_types(&mut self, fn_stack: &mut [FnDef]) {
		let mut arg_bindings = self.arg_bindings.clone();

		if let Some((fn_arg_types, fn_body_type)) = self.extract_type_sig() {
			// Type signature already exists. Just infer types for body and make sure
			// there are no collisions

			self.set_arg_types(fn_arg_types);

			self.body.infer_types(Some(fn_body_type), fn_stack, &mut arg_bindings, &mut Vec::new());
		} else {
			// No type signature for function binding. Pass arg bindings to body and infer types
			// for body, then get function signature from updated arg types and body type

			let arg_bindings_old_len = arg_bindings.len();

			// args: type_to_infer_to, stack_of_available_functions, constants, vars
			self.body.infer_types(Some(fn_body_type), fn_stack, &mut arg_bindings, &mut Vec::new());

			if arg_bindings.len() != arg_bindings_old_len {
				panic!("FnDef::infer_types: arg_bindings.len() != arg_bindings_old_len");
			}

			let arg_types = arg_bindings.into_iter().map(|b| b.type_sig);
			self.set_arg_types();

			self.construct_fn_sig()
			self.binding.type_sig = Some(construct_fn_type())
		}
	}
}

impl super::AST {
	pub fn infer_types(&mut self) {
		if let Some(main_def) = self.items.iter_mut()
			.find(|meta| if let Item::FnDef(ref def) = *meta.item {
				def.binding.ident == "main"
			} else {
				false
			})
		{
			main_def.infer_types(&mut self.items).unwrap()
		} else {
			panic!("AST::infer_types: No main function found")
		}
	}
}

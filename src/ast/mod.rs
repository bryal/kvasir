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

mod parse;
mod inference;
mod core_lib;

use std::collections::HashMap;
use std::borrow::Cow;
use std::mem::replace;

struct Env {
	core_consts: HashMap<&'static str, Type>,
	const_defs: ConstDefScopeStack,
	var_types: Vec<TypedBinding>
}
impl Env {
	fn get_var_type(&self, ident: &str) -> Option<Option<&Type>> {
		self.var_types.iter()
			.rev()
			.find(|stack_tb| stack_tb.ident == ident)
			.map(|stack_tb| stack_tb.type_sig.as_ref())
	}
	fn get_var_type_mut(&mut self, bnd: &str) -> Option<&mut Option<Type>> {
		self.var_types.iter_mut()
			.rev()
			.find(|stack_tb| stack_tb.ident == bnd)
			.map(|stack_tb| &mut stack_tb.type_sig)
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
	Basic(String),
	Construct(String, Vec<Type>),
	Tuple(Vec<Type>),
}
impl Type {
	fn nil() -> Type {
		Type::Tuple(vec![])
	}

	fn basic<T: Into<String>>(ts: T) -> Type {
		Type::Basic(ts.into())
	}

	fn construct<T: Into<String>>(constructor: T, args: Vec<Type>) -> Type {
		Type::Construct(constructor.into(), args)
	}

	fn fn_sig(mut arg_tys: Vec<Type>, return_ty: Type) -> Type {
		arg_tys.push(return_ty);
		Type::Construct("→".into(), arg_tys)
	}

	fn bool() -> Type {
		Type::Basic("bool".into())
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypedBinding {
	pub ident: String,
	pub type_sig: Option<Type>,
}

/// A path to an expression or item. Could be a path to a module in a use statement,
/// of a path to a function or constant in an expression.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Path {
	parts: Vec<String>,
	is_absolute: bool,
}
impl Path {
	fn new(parts: Vec<String>, is_absolute: bool) -> Path {
		Path{ parts: parts, is_absolute: is_absolute }
	}

	fn from_ident(ident: &str) -> Path {
		Path::new(vec![ident.into()], false)
	}

	pub fn is_absolute(&self) -> bool { self.is_absolute }

	pub fn parts(&self) -> &[String] { &self.parts }

	/// If self is just a simple ident, return it as Some
	fn ident(&self) -> Option<&str> {
		if self.parts.len() == 1 && !self.is_absolute {
			Some(&self.parts[0])
		} else {
			None
		}
	}

	pub fn to_str(&self) -> String {
		format!(
			"{}{}{}",
			if self.is_absolute() { "/" } else { "" },
			self.parts[0],
			self.parts[1..].iter().fold(String::new(), |acc, p| acc + "/" + p))
	}
}
impl PartialEq<str> for Path {
	fn eq(&self, rhs: &str) -> bool {
		self.to_str() == rhs
	}
}
impl ::std::fmt::Display for Path {
	fn fmt(&self, f: &mut ::std::fmt::Formatter) -> Result<(), ::std::fmt::Error> {
		f.write_str(&self.to_str())
	}
}

#[derive(Debug, Clone)]
pub struct Use {
	pub paths: Vec<Path>,
}

#[derive(Debug, Clone)]
pub struct ConstDef {
	pub binding: TypedBinding,
	pub body: ExprMeta,
}
impl ConstDef {
	fn get_type(&self) -> Option<&Type> {
		self.binding.type_sig.as_ref()
	}

	fn set_type(&mut self, ty: Option<Type>) {
		self.binding.type_sig = ty
	}
}

enum ConstDefOrType {
	Def(ConstDef),
	Type(Option<Type>),
}
impl ConstDefOrType {
	fn get_type(&self) -> Option<&Type> {
		match self {
			&ConstDefOrType::Def(ref def) => def.binding.type_sig.as_ref(),
			&ConstDefOrType::Type(ref ty) => ty.as_ref()
		}
	}

	/// Extracts a mutable ConstDef reference from self if self is of variant Def. Else, panic.
	fn as_def(&mut self) -> Option<&mut ConstDef> {
		match self {
			&mut ConstDefOrType::Def(ref mut def) => Some(def),
			_ => None
		}
	}

	/// If variant is Def, return contained ConstDef. Panic otherwise
	fn unwrap_def(self) -> ConstDef {
		match self {
			ConstDefOrType::Def(def) => def,
			_ => panic!("ConstDefOrType::into_def: Variant wasn't `Def`")
		}
	}

	/// If variant is `Def`, replace def with `Type` and return def
	fn replace_into_def(&mut self) -> Option<ConstDef> {
		let ty = match self.as_def() {
			Some(def) => def.binding.type_sig.clone(),
			None => return None
		};

		Some(replace(self, ConstDefOrType::Type(ty)).unwrap_def())
	}

	/// If variant is `Type`, replace self with `Def` variant containing passed def. Panic otherwise
	fn insert_def(&mut self, def: ConstDef) {
		match self {
			&mut ConstDefOrType::Type(_) => *self = ConstDefOrType::Def(def),
			_ => panic!("ConstDefOrType::insert_def: `self` is already `Type`")
		}
	}
}

type ConstDefScope = HashMap<String, ConstDefOrType>;

/// A stack of scopes of constant definitions. There are no double entries.
struct ConstDefScopeStack(
	Vec<ConstDefScope>
);
impl ConstDefScopeStack {
	fn new() -> ConstDefScopeStack {
		ConstDefScopeStack(Vec::new())
	}

	fn height(&self) -> usize {
		self.0.len()
	}

	fn contains_def(&self, def_ident: &str) -> bool {
		self.0.iter().any(|scope| scope.contains_key(def_ident))
	}

	fn get_height(&self, key: &str) -> Option<usize> {
		for (height, scope) in self.0.iter().enumerate() {
			if scope.contains_key(key) {
				return Some(height);
			}
		}
		None
	}

	fn get(&self, key: &str) -> Option<(&ConstDefOrType, usize)> {
		for (height, scope) in self.0.iter().enumerate() {
			if let Some(ref def) = scope.get(key) {
				return Some((def, height));
			}
		}
		None
	}
	fn get_mut(&mut self, key: &str) -> Option<(&mut ConstDefOrType, usize)> {
		for (height, scope) in self.0.iter_mut().enumerate() {
			if let Some(def) = scope.get_mut(key) {
				return Some((def, height));
			}
		}
		None
	}

	fn get_at_height(&self, key: &str, height: usize) -> Option<&ConstDefOrType> {
		self.0.get(height).and_then(|scope| scope.get(key))
	}
	fn get_at_height_mut(&mut self, key: &str, height: usize) -> Option<&mut ConstDefOrType> {
		self.0.get_mut(height).and_then(|scope| scope.get_mut(key))
	}

	fn split_from(&mut self, from: usize) -> Vec<ConstDefScope> {
		self.0.split_off(from)
	}

	fn push(&mut self, scope: ConstDefScope) {
		if scope.keys().any(|key| self.contains_def(key)) {
			panic!("ConstDefScopeStack::push: Key already exists in scope");
		}

		self.0.push(scope);
	}
	fn pop(&mut self) -> Option<ConstDefScope> {
		self.0.pop()
	}
	fn extend<I: IntoIterator<Item=ConstDefScope>>(&mut self, scopes: I) {
		// TODO: These checks for doubles would preferably be handled somewhere else
		for scope in scopes {
			self.push(scope);
		}
	}
}

#[derive(Debug, Clone)]
pub struct SExpr {
	pub func: ExprMeta,
	pub args: Vec<ExprMeta>,
}

#[derive(Debug, Clone)]
pub struct Block {
	pub uses: Vec<Use>,
	pub const_defs: Vec<ConstDef>,
	pub exprs: Vec<ExprMeta>,
}

#[derive(Debug, Clone)]
pub struct Cond {
	pub clauses: Vec<(ExprMeta, ExprMeta)>,
	pub else_clause: Option<ExprMeta>
}
impl Cond {
	/// Iterate over all clauses of self, including the else clause
	fn iter_clauses<'a>(&'a self) -> Box<Iterator<Item=(Cow<ExprMeta>, &ExprMeta)> + 'a> {
		Box::new(self.clauses.iter()
			.map(|&(ref p, ref c)| (Cow::Borrowed(p), c))
			.chain(self.else_clause.iter().map(|c| (Cow::Owned(ExprMeta::new_true()), c))))
	}

	/// Iterate over all clauses of self, including the else clause
	fn iter_consequences<'a>(&'a self) -> Box<Iterator<Item=&ExprMeta> + 'a> {
		Box::new(self.clauses.iter().map(|&(_, ref c)| c).chain(self.else_clause.iter()))
	}
	/// Iterate over all clauses of self, including the else clause
	fn iter_consequences_mut<'a>(&'a mut self) -> Box<Iterator<Item=&mut ExprMeta> + 'a> {
		Box::new(self.clauses.iter_mut()
			.map(|&mut (_, ref mut c)| c)
			.chain(self.else_clause.iter_mut()))
	}

	fn get_type(&self) -> Option<&Type> {
		match self.iter_consequences().map(|c| c.type_.as_ref()).find(|ty| ty.is_some()) {
			Some(found) => found,
			None => panic!("Cond::get_type: Could not get type from any clause")
		}
	}
}

#[derive(Debug, Clone)]
pub struct Lambda {
	pub arg_bindings: Vec<TypedBinding>,
	pub body: ExprMeta
}

// TODO: Separate into declaration and assignment. Let VarDecl create an l-value
#[derive(Debug, Clone)]
pub struct VarDef {
	pub binding: TypedBinding,
	pub mutable: bool,
	pub body: ExprMeta,
}

#[derive(Debug, Clone)]
pub struct Assign {
	pub lvalue: TypedBinding,
	pub rvalue: ExprMeta,
}

#[derive(Debug, Clone)]
pub enum Expr {
	Nil,
	NumLit(String),
	StrLit(String),
	Bool(bool),
	Binding(Path),
	SExpr(SExpr),
	Block(Block),
	Cond(Cond),
	Lambda(Lambda),
	VarDef(VarDef),
	Assign(Assign)
}
impl Expr {
	fn is_var_def(&self) -> bool {
		if let Expr::VarDef(_) = *self {
			true
		} else {
			false
		}
	}
}

/// An expression with additional attributes such as type information
#[derive(Debug, Clone)]
pub struct ExprMeta {
	pub value: Box<Expr>,
	pub type_: Option<Type>
}
impl ExprMeta {
	fn new(value: Expr, ty: Option<Type>) -> ExprMeta {
		ExprMeta{ value: Box::new(value), type_: ty }
	}

	fn new_true() -> ExprMeta {
		ExprMeta::new(Expr::Bool(true), Some(Type::bool()))
	}

	fn new_false() -> ExprMeta {
		ExprMeta::new(Expr::Bool(false), Some(Type::bool()))
	}

	fn nil() -> ExprMeta {
		ExprMeta::new(Expr::Nil, Some(Type::nil()))
	}

	pub fn expr(&mut self) -> &mut Expr {
		&mut self.value
	}

	fn set_type(&mut self, ty: Option<Type>) {
		// TODO: Try using Cow for speedup
		match (&mut self.type_, ty) {
			(&mut Some(ref expected), Some(ref found)) if expected != found => panic!(
				"ExprMeta::set_type: Type mismatch. Expected `{:?}`, found `{:?}`",
				expected,
				found),
			(t @ &mut None, Some(found)) => *t = Some(found),
			_ => (),
		}
	}
}

#[derive(Debug)]
pub enum Item {
	Use(Use),
	ConstDef(ConstDef),
	Expr(ExprMeta),
}

#[derive(Debug, Clone)]
pub struct AST {
	pub uses: Vec<Use>,
	pub const_defs: Vec<ConstDef>,
}

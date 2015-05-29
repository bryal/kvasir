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

use std::collections::HashMap;
use std::borrow::Cow;
use std::fmt::{ self, Debug };

fn list_items_to_string<T: Debug>(list: &[T]) -> String {
	list.iter().fold(String::new(), |acc, e| format!("{} {:?}", acc, e))
}

static FUNCTION_CONSTRUCTORS: &'static [&'static str] = &["→", "fn", "->"];

#[derive(Clone, PartialEq, Eq)]
pub enum Type {
	Inferred,
	Basic(String),
	Construct(String, Vec<Type>),
	Tuple(Vec<Type>),
	Poly(String)
}
impl Type {
	pub fn new_nil() -> Type { Type::Tuple(vec![]) }
	pub fn new_basic<T: Into<String>>(ts: T) -> Type { Type::Basic(ts.into()) }
	pub fn new_construct<T: Into<String>>(constructor: T, args: Vec<Type>) -> Type {
		Type::Construct(constructor.into(), args)
	}
	pub fn new_poly<T: Into<String>>(ts: T) -> Type { Type::Poly(ts.into()) }
	pub fn new_fn(mut arg_tys: Vec<Type>, return_ty: Type) -> Type {
		arg_tys.push(return_ty);
		Type::Construct("→".into(), arg_tys)
	}

	pub fn is_inferred(&self) -> bool {
		match self {
			&Type::Inferred => true,
			_ => false
		}
	}
	// TODO: Remake into something like `is_known`, include partial constructors etc.
	pub fn is_specified(&self) -> bool {
		!self.is_inferred()
	}
	pub fn is_poly(&self) -> bool {
		match self {
			&Type::Poly(_) => true,
			_ => false
		}
	}

	/// Basically lhs == rhs, with some exceptions. E.g. "→" == "fn"
	pub fn constructor_eq(lhs: &str, rhs: &str) -> bool {
		(FUNCTION_CONSTRUCTORS.contains(&lhs) && FUNCTION_CONSTRUCTORS.contains(&rhs))
			|| lhs == rhs
	}
}
impl Debug for Type {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			&Type::Inferred => write!(f, "_"),
			&Type::Basic(ref s) => write!(f, "{}", s),
			&Type::Construct(ref constr, ref args) => write!(f, "{{{}{}}}",
				constr,
				list_items_to_string(&args)),
			&Type::Tuple(ref tys) => write!(f, "({})", list_items_to_string(tys)),
			&Type::Poly(ref poly) => write!(f, "{}", poly),
		}
	}
}

#[derive(Clone, PartialEq, Eq)]
pub struct TypedBinding {
	pub ident: String,
	pub type_sig: Type,
}
impl Debug for TypedBinding {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "(:{:?} {})", self.type_sig, self.ident)
	}
}

/// A path to an expression or item. Could be a path to a module in a use statement,
/// of a path to a function or constant in an expression.
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct Path {
	parts: Vec<String>,
	is_absolute: bool,
}
impl Path {
	pub fn new(parts: Vec<String>, is_absolute: bool) -> Path {
		Path{ parts: parts, is_absolute: is_absolute }
	}

	pub fn is_absolute(&self) -> bool { self.is_absolute }

	pub fn parts(&self) -> &[String] { &self.parts }

	/// If self is just a simple ident, return it as Some
	pub fn ident(&self) -> Option<&str> {
		if self.parts.len() == 1 && !self.is_absolute {
			Some(&self.parts[0])
		} else {
			None
		}
	}

	pub fn concat(mut self, other: Path) -> Result<Path, String> {
		if other.is_absolute {
			Err(format!(
				"Path::concat: `{:?}` is an absolute path",
				other.to_str()))
		} else {
			self.parts.extend(other.parts);
			Ok(self)
		}
	}

	pub fn to_str(&self) -> String {
		format!(
			"{}{}{}",
			if self.is_absolute() { "\\" } else { "" },
			self.parts[0],
			self.parts[1..].iter().fold(String::new(), |acc, p| acc + "\\" + p))
	}
}
impl PartialEq<str> for Path {
	fn eq(&self, rhs: &str) -> bool {
		self.to_str() == rhs
	}
}
impl Debug for Path {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.write_str(&self.to_str())
	}
}

#[derive(Clone)]
pub struct Use {
	pub paths: Vec<Path>,
}
impl Debug for Use {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "(Use ({}))", list_items_to_string(&self.paths))
	}
}

#[derive(Clone)]
pub struct SExpr {
	pub func: ExprMeta,
	pub args: Vec<ExprMeta>,
}
impl Debug for SExpr {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "({:?} {})", self.func, list_items_to_string(&self.args))
	}
}

fn const_defs_to_string(consts: &HashMap<String, ExprMeta>) -> String {
	consts.iter()
		.fold(String::new(), |acc, (name, val)| format!("{} (ConstDef {} {:?})", acc, name, val))
}

#[derive(Clone)]
pub struct Block {
	pub uses: Vec<Use>,
	pub const_defs: HashMap<String, ExprMeta>,
	pub exprs: Vec<ExprMeta>,
}
impl Debug for Block {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "(Block {} {} {})",
			list_items_to_string(&self.uses),
			const_defs_to_string(&self.const_defs),
			list_items_to_string(&self.exprs))
	}
}

#[derive(Clone)]
pub struct Cond {
	pub clauses: Vec<(ExprMeta, ExprMeta)>,
	pub else_clause: Option<ExprMeta>
}
impl Cond {
	/// Iterate over all clauses of self, including the else clause
	#[allow(dead_code)]
	pub fn iter_clauses<'a>(&'a self) -> Box<Iterator<Item=(Cow<ExprMeta>, &ExprMeta)> + 'a> {
		Box::new(self.clauses.iter()
			.map(|&(ref p, ref c)| (Cow::Borrowed(p), c))
			.chain(self.else_clause.iter().map(|c| (Cow::Owned(ExprMeta::new_true()), c))))
	}
	/// Iterate over predicates of clauses.
	/// This excludes the else clause, since it contains no predicate
	pub fn iter_predicates_mut<'a>(&'a mut self) -> Box<Iterator<Item=&mut ExprMeta> + 'a> {
		Box::new(self.clauses.iter_mut().map(|&mut (ref mut p, _)| p))
	}
	/// Iterate over all clauses of self, including the else clause
	pub fn iter_consequences<'a>(&'a self) -> Box<Iterator<Item=&ExprMeta> + 'a> {
		Box::new(self.clauses.iter().map(|&(_, ref c)| c).chain(self.else_clause.iter()))
	}
	/// Iterate over all clauses of self, including the else clause
	pub fn iter_consequences_mut<'a>(&'a mut self) -> Box<Iterator<Item=&mut ExprMeta> + 'a> {
		Box::new(self.clauses.iter_mut()
			.map(|&mut (_, ref mut c)| c)
			.chain(self.else_clause.iter_mut()))
	}
}
impl Debug for Cond {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "(Cond {}{})",
			list_items_to_string(&self.clauses),
			self.else_clause.as_ref().map(|e| format!(" {:?}", e)).unwrap_or("".into()))
	}
}

#[derive(Clone)]
pub struct Lambda {
	pub arg_bindings: Vec<TypedBinding>,
	pub body: ExprMeta
}
impl Debug for Lambda {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "(Lambda ({}) {:?})", list_items_to_string(&self.arg_bindings), self.body)
	}
}

// TODO: Separate into declaration and assignment. Let VarDecl create an l-value
#[derive(Clone)]
pub struct VarDef {
	pub binding: TypedBinding,
	pub mutable: bool,
	pub body: ExprMeta,
}
impl Debug for VarDef {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "(VarDef{} {:?} {:?})",
			if self.mutable { " mut" } else { "" },
			self.binding,
			self.body)
	}
}

#[derive(Clone)]
pub struct Assign {
	pub lvalue: TypedBinding,
	pub rvalue: ExprMeta,
}
impl Debug for Assign {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "(Assign {:?} {:?})", self.lvalue, self.rvalue)
	}
}

#[derive(Clone)]
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
	pub fn is_var_def(&self) -> bool {
		if let Expr::VarDef(_) = *self {
			true
		} else {
			false
		}
	}
}
impl Debug for Expr {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			&Expr::Nil => write!(f, "()"),
			&Expr::NumLit(ref n) => write!(f, "{}", n),
			&Expr::StrLit(ref s) => write!(f, "{}", s),
			&Expr::Bool(ref b) => write!(f, "{}", b),
			&Expr::Binding(ref p) => write!(f, "{:?}", p),
			&Expr::SExpr(ref e) => write!(f, "{:?}", e),
			&Expr::Block(ref b) => write!(f, "{:?}", b),
			&Expr::Cond(ref c) => write!(f, "{:?}", c),
			&Expr::Lambda(ref l) => write!(f, "{:?}", l),
			&Expr::VarDef(ref v) => write!(f, "{:?}", v),
			&Expr::Assign(ref a) => write!(f, "{:?}", a)
		}
	}
}

/// An expression with additional attributes such as type information
#[derive(Clone)]
pub struct ExprMeta {
	pub value: Box<Expr>,
	pub type_: Type
}
impl ExprMeta {
	pub fn new(value: Expr, ty: Type) -> Self { ExprMeta{ value: Box::new(value), type_: ty } }
	pub fn new_true() -> ExprMeta { ExprMeta::new(Expr::Bool(true), Type::new_basic("bool")) }
	pub fn new_false() -> ExprMeta { ExprMeta::new(Expr::Bool(false), Type::new_basic("bool")) }
	pub fn new_nil() -> ExprMeta { ExprMeta::new(Expr::Nil, Type::new_nil()) }

	pub fn get_type(&self) -> &Type { &self.type_ }

	pub fn expr(&self) -> &Expr { &self.value }
	pub fn expr_mut(&mut self) -> &mut Expr { &mut self.value }
}
impl Debug for ExprMeta {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "(:{:?} {:?})", self.type_, self.value)
	}
}

#[derive(Clone)]
pub struct AST {
	pub uses: Vec<Use>,
	pub const_defs: HashMap<String, ExprMeta>,
}
impl Debug for AST {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "(AST {} {})",
			list_items_to_string(&self.uses),
			const_defs_to_string(&self.const_defs))
	}
}

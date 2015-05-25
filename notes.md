Good read http://www.codecommit.com/blog/scala/what-is-hindley-milner-and-why-is-it-cool

## Spec

Constant: `(define c <body>)`
	Statement placement in scope is irrelevant. Available everywhere, like `fn ...` and `const ...`
	in Rust. Cannot be overwritten by future definitions for the same name.
Function: `(define (f x) <body>)`
	A function definition is actually a constant definition of a function pointer.
Variable: `(var x <body>)`
	Similar to constant definition, but only available after statement. An already defined
	variable can be overwritten by a new definition of possibly different type.
	Actually shorthand for declaration + assignment
Mutable variable: `(var mut x <body>)`
	To `var` as `let mut` is to `let` in Rust.
Type ascription:
	Types of expressions can be described explicitly to help with type inference and to create a
	coerce site. Syntax is `(:TYPE EXPR)` e.g. `(:u32 5)`
Pragmas:
	Compiler attributes for items.
	Examples:
		* Platform specific code:
			`(#cfg ((platform windows)) (const FOO 0)) (#cfg ((platform unix)) (const FOO 1))`
		* Disallow CTE:
			`(#no-cte (fn (foo) (foo)))`
		* Prefer CTE:
			`(#prefer-cte (fn (! n) (* n (! (dec n)))))`


## Idéas

Interactive programming enviroment. AST is interpreted and runs. Modified code is sent to server
where it's verified. Then execution of running program is temporarily paused while AST is being
updated. Then program is resumed with new code.
When sending code, only run it if it compiles to AST without errors. Wait until in an unmodified
function before inserting new code.

Default type for numbers is u64/f64, but type can be specified with :

Notes:
Not sure what to do with const defs and maps. Should ConstDef contain a TypedBinding
(String, not Path), or only Type?

* Compile time evaluation, how to make sure there are no infinite loops.
  Wouldn't want the compiler to hang.
  http://stackoverflow.com/questions/19259114/why-are-constant-expressions-not-evaluated-at-compile-time-in-haskell
  Maybe keep a caller stack in interpreter, and if same function is called to many times, abort.
* Maybe allow different modes for the compiler:
  * Strictly no CTE
  * No CTE unless explicitly allowed, `(#prefer-cte ...)` or `(#cte ...)` or maybe `(#allow-cte ...)`
  * Discriminate between `def-proc` and `def-func`, decide whether to CTE from this.
    `def-func` defines a function in the mathematical sense, i.e. a pure function, `(#prefer-cte ...)`
    `def-proc` defines a procedure, a list of commands to execute. Not guaranteed to be a function. Neither `(#no-cte ...)` nor `(#prefer-cte ...)`
  * CTE unless explicitly disallowed, `(#no-cte ...)`
* Add pattern matching for bindings. Would for example allow both `(lambda x ...)` and `(lambda (a b) ...)`
* Let definitions take symbol instead of binding. This would allow for easier pattern matching.
  symbol => bind, expression => compare. E.g:
    `(match x ('(a ,(@ b (+ 3 2)) ,PI) ...))` would correspond to `match x { [a, b, c] if b == 3 + 2 && c == PI => ..., }`
* Store definitions in a stack of scopes. Pop scopes until the def is found, then send remaining stack along when infering


const a 1
const b {
	const c 2
	const d {
		const e 3
		const f c
	}
}

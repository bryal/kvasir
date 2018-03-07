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
Macros:
	Definition:
		`(def-macro-rules if (then else)
			((predicate then consequence else otherwise)
			 (cond (predicate consequence) (else otherwise))))`
	Application and expandion:
		`(if (> 3 x) then (display "Yes") else (display "No"))`
		=>
		`(cond ((> 3 x) (display "Yes")) (else (display "No"))`


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
* Streaming tokenizer & parser


## Match

(match foo
  [(Foo bar) (+ bar 1)]
  [Bar       10])

Idé: Gör match binär. Antingen matchar den ett mönster, eller så kör den default.
     Likt cond för if.
     Då blir det färre fall att tänka på, men kanske sämre prestanda?

För att typinferensa, se till att alla högerled är samma typ, likt en cond.

Vid match:
  Om identifierare:
    Some(Bind identifierare)
  Annars om variant är rätt / konstruktor är samma:
    Matcha barn mot barn
  Annars:
    None

TODO: if and let can be implemented in terms of match. Vice versa?

## Algebraic data types

Shouldn't have "multiple" members. For products, use tuples (maybe
anonymous structs / tuples with names fields later?).

May allow for simple implementation of `match`?
Just generate functions for variant testing and unwrapping:
  def:
    (define-data (Foo a)
      (Three (a, a, a))
      (One   a))
  generate:
    of-variant-Three    :: Three a -> Bool
    unsafe-unwrap-Three :: Three a -> (a, a, a)

## Algebraic data types and pattern matching

If we generate functions or add special forms for testing variants and
unwrapping constructors, I think we could implement `match` in terms
of `if` and `let`

foo = (Foo x (Bar y))

(match foo
  [(Foo a (Bar b))   (+ a b)]
  [(Foo a _)         (+ a 1)]
  [Baz               0])

<=>

(cond [(and (of-variant? foo Foo) (of-variant? Bar (cdr (as-variant foo Foo))))
       (let [[_1    (as-variant foo Foo)]
             [a     (car _1)]
             [b     (as-variant (cdr _1) Bar)]]
         (+ a b))]
      [(of-variant? foo Foo)
       (let [[_1    (as-variant foo Foo)]
             [a     (car _1)]]
         (+ a 1))]
      [(of-variant? foo Baz)
       0])

If `data` tag is always of size 16bit, easy way to cast is
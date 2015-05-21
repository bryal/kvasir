Good read http://www.codecommit.com/blog/scala/what-is-hindley-milner-and-why-is-it-cool

```
(define (f x) x)
```

End constraints for this function is (f x: X): X
When concrete type can't be infered, make the function polymorphic and leave X as a type parameter
```
(define (f<T>::<fn (T) T> x: T) x)
```


```
(define (g x) x)

(define (f x) (block
	(let ((a 10))
		(+ (g x) a))))

(define (main) (block
	(define x (zeroed))
	(f x)))
```


## Method 1

### Rules

- Start infering in main, work downwards in complexity.

### Procedure

```
main has no return type
	infer(main, None)

No specific type is expected from (block ...)
	infer((block ...), None)

For block, return type is type of tail expression
	infer((f x), None)

type variables for expression: (f: F x: X): Z

	Expected type adds constraint to Z, but expected is None, so nothing happens.
	F and X can both gain constraints from definition of f
		infer(f, None)



When infering for expression first, infer for arguments.
	infer(x, None)


```

AST: alla items clonas till vector. För varje item inferas typ, och vektorn ski8ckas med mutably.

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

## Idéas

Interactive programming enviroment. AST is interpreted and runs. Modified code is sent to server
where it's verified. Then execution of running program is temporarily paused while AST is being
updated. Then program is resumed with new code.
When sending code, only run it if it compiles to AST without errors. Wait until in an unmodified
function before inserting new code.

Default type for numbers is u64/f64, but type can be specified with :

Log:
Not sure what to do with const defs and maps. Should ConstDef contain a TypedBinding
(String, not Path), or only Type?

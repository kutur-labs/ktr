---
title: Language Reference
order: 2
---

# Language Reference

ktr is a domain-specific language for parametric pattern drafting. Programs
describe measurements, geometric constructions, and constraints that a solver
can resolve at runtime. The compiler (`ktrc`) translates `.ktr` source into a
line-oriented intermediate representation (`.ktrir`) consumed by runtimes.

The formal grammars are also available as standalone EBNF files:

- [ktr.ebnf](https://github.com/kutur-labs/ktr/blob/main/ktrc/spec/ktr.ebnf) -- ktr source language grammar
- [ktrir.ebnf](https://github.com/kutur-labs/ktr/blob/main/ktrc/spec/ktrir.ebnf) -- ktr-ir intermediate representation grammar

---

## 1. Notation

The grammar uses ISO 14977 Extended Backus-Naur Form (EBNF).

| Notation        | Meaning                                   |
|-----------------|-------------------------------------------|
| `=`             | definition                                |
| `,`             | concatenation                             |
| `\|`            | alternation                               |
| `[ ... ]`       | optional (0 or 1)                         |
| `{ ... }`       | repetition (0 or more)                    |
| `( ... )`       | grouping                                  |
| `" ... "`       | terminal string                           |
| `(* ... *)`     | comment                                   |
| `- `            | exception                                 |

---

## 2. Lexical Grammar

### 2.1 Source Encoding

Source files are UTF-8 encoded. The grammar operates over bytes; identifiers
and keywords use ASCII only.

### 2.2 Whitespace and Comments

Whitespace (spaces, tabs, newlines) separates tokens but is otherwise ignored.

Line comments begin with `//` and extend to the end of the line. They are
treated as whitespace and may appear anywhere a token boundary is valid.

```
COMMENT = "//" , { ANY - NEWLINE } ;
```

Example:

```ktr
// This is a comment
let x = 100mm  // inline comment
```

### 2.3 Keywords

```
let  input  fn  return  search  bounds  tolerance  require  export  as  assert
```

Keywords are reserved and cannot be used as identifiers.

### 2.4 Tokens

```ebnf
(* ------------------------------------------------------------------ *)
(* ktr source language -- Lexical grammar                             *)
(* ------------------------------------------------------------------ *)

LETTER           = "A" | "B" | "C" | "D" | "E" | "F" | "G" | "H"
                 | "I" | "J" | "K" | "L" | "M" | "N" | "O" | "P"
                 | "Q" | "R" | "S" | "T" | "U" | "V" | "W" | "X"
                 | "Y" | "Z"
                 | "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h"
                 | "i" | "j" | "k" | "l" | "m" | "n" | "o" | "p"
                 | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x"
                 | "y" | "z" ;

DIGIT            = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7"
                 | "8" | "9" ;

IDENT            = ( LETTER | "_" ) , { LETTER | DIGIT | "_" } ;

INTEGER          = DIGIT , { DIGIT } ;

NUMBER           = [ "-" ] , DIGIT , { DIGIT } , [ "." , DIGIT , { DIGIT } ] ;

UNIT             = "mm" | "cm" ;

DIMENSION        = NUMBER , UNIT ;                  (* e.g. 100mm, 25cm     *)

PERCENTAGE       = NUMBER , "%" ;                   (* e.g. 50%             *)

STRING           = '"' , { ANY - '"' } , '"' ;
```

The lexer greedily attaches a unit suffix to a preceding number. An unknown
suffix causes the number and suffix to lex as separate tokens (a bare number
followed by an identifier).

---

## 3. Syntactic Grammar

```ebnf
(* ------------------------------------------------------------------ *)
(* ktr source language v0.1 -- Syntactic grammar                      *)
(* ------------------------------------------------------------------ *)

program          = { statement } ;

statement        = let_statement
                 | input_decl
                 | fn_def
                 | export_stmt ;

(* ------------------------------------------------------------------ *)
(* Let bindings                                                        *)
(* ------------------------------------------------------------------ *)

let_statement    = "let" , IDENT , "=" , expression ;

(* ------------------------------------------------------------------ *)
(* Input declarations                                                  *)
(* ------------------------------------------------------------------ *)

input_decl       = "input" , IDENT , "=" , expression ,
                   [ "{" , { assert_stmt } , "}" ] ;

assert_stmt      = "assert" , IDENT , cmp_op , expression ;

cmp_op           = "==" | "!=" | ">" | "<" | ">=" | "<=" ;

(* ------------------------------------------------------------------ *)
(* Function definitions                                                *)
(* ------------------------------------------------------------------ *)

fn_def           = "fn" , IDENT , "(" , [ param_list ] , ")" ,
                   "{" , fn_body , "}" ;

param_list       = param , { "," , param } ;

param            = IDENT , ":" , type_name ;

fn_body          = { let_statement } , return_stmt ;

return_stmt      = "return" , expression ;

(* ------------------------------------------------------------------ *)
(* Search (solver) blocks                                              *)
(* ------------------------------------------------------------------ *)

(* Search appears as the RHS of a let binding:                         *)
(*   let tweak = search (t: f64) { ... }                               *)

search_expr      = "search" , "(" , param , ")" ,
                   "{" , search_body , "}" ;

search_body      = bounds_clause ,
                   tolerance_clause ,
                   require_clause ;

bounds_clause    = "bounds" , IDENT , "[" , expression , ".." , expression , "]" ;

tolerance_clause = "tolerance" , expression ;

require_clause   = "require" , expression , cmp_op , expression ;

(* ------------------------------------------------------------------ *)
(* Export statements                                                    *)
(* ------------------------------------------------------------------ *)

export_stmt      = "export" , expression , "as" , STRING ;

(* ------------------------------------------------------------------ *)
(* Expressions                                                         *)
(* ------------------------------------------------------------------ *)

expression       = additive_expr ;

additive_expr    = multiplicative_expr ,
                   { ( "+" | "-" ) , multiplicative_expr } ;

multiplicative_expr = unary_expr ,
                      { ( "*" | "/" ) , unary_expr } ;

unary_expr       = [ "-" ] , postfix_expr ;

postfix_expr     = primary_expr , { field_access | method_call } ;

field_access     = "." , IDENT ;

method_call      = "." , IDENT , "(" , [ arg_list ] , ")" ;

primary_expr     = DIMENSION                         (* 100mm              *)
                 | PERCENTAGE                        (* 50%                *)
                 | NUMBER                            (* 42, 3.14           *)
                 | fn_call                           (* point(x, y)        *)
                 | search_expr                       (* search (t) { ... } *)
                 | IDENT                             (* head               *)
                 | "(" , expression , ")" ;          (* grouping           *)

fn_call          = IDENT , "(" , [ arg_list ] , ")" ;

arg_list         = expression , { "," , expression } ;

(* ------------------------------------------------------------------ *)
(* Type names                                                          *)
(* ------------------------------------------------------------------ *)

type_name        = "f64"
                 | "length"
                 | "percentage"
                 | "point"
                 | "bezier"
                 | "line"
                 | "bool" ;
```

### 3.1 Operator Precedence (lowest to highest)

| Precedence | Operators         | Associativity |
|------------|-------------------|---------------|
| 1          | `+`  `-`          | Left          |
| 2          | `*`  `/`          | Left          |
| 3          | unary `-`         | Right (prefix)|
| 4          | `.field` `.method()` | Left          |

Comparison operators (`==`, `>`, `<`, etc.) appear only in `assert` and
`require` clauses, not as general expression operators.

---

## 4. Type System

| Type         | Description                                         |
|--------------|-----------------------------------------------------|
| `f64`        | Bare scalar (unitless double-precision float)       |
| `length`     | Dimensional value carrying a unit (`mm`, `cm`)      |
| `percentage` | Percentage value (`%` suffix in source)             |
| `point`      | 2D coordinate `(x: length, y: length)`              |
| `bezier`     | Cubic Bezier curve (4 control points)               |
| `line`       | Straight segment between two points                 |
| `bool`       | Boolean (internal to assertions/requires)           |

### 4.1 Units

Length values carry their original unit through compilation. The compiler
preserves units; conversion happens at runtime.

| Unit | Name        |
|------|-------------|
| `mm` | millimeters |
| `cm` | centimeters |

### 4.2 Type Inference

The type of a `let` binding is inferred from its right-hand side:

- A `DIMENSION` literal has type `length`.
- A `PERCENTAGE` literal has type `percentage`.
- A bare `NUMBER` has type `f64`.
- An identifier reference inherits the type of the referenced binding.
- Arithmetic expressions follow standard promotion rules (future spec).
- Function calls have the declared return type of the function.

### 4.3 Poison Type

`poison` is a compiler-internal pseudo-type assigned when type resolution
fails (e.g., referencing an undefined identifier). Poison suppresses
cascading diagnostic errors. It never appears in `.ktr` source or `.ktrir`
output.

---

## 5. Program Structure

A ktr program is a sequence of top-level declarations. Bindings are
evaluated in source order; every name must be defined before it is
referenced (topological ordering).

### 5.1 Inputs

```ktr
input head = 100mm {
  assert head > 0mm
  assert head < 800mm
}
```

An `input` declares a parametric measurement with a default value and
optional constraints. At runtime, inputs can be overridden by the user
within the bounds specified by their assertions.

### 5.2 Let Bindings

```ktr
let right = point(tweak * head / 10, 0mm)
```

A `let` binding introduces a named value. The right-hand side is an
arbitrary expression. Bindings are immutable.

### 5.3 Functions

```ktr
fn neck_quarter(tweak: f64) {
  let right  = point(tweak * head / 10, 0mm)
  let bottom = point(0mm, tweak * head / 12)
  return bezier(right, cp1, cp2, bottom)
}
```

Functions take typed parameters and contain a sequence of `let` bindings
followed by a single `return` expression. Functions may reference inputs
and other top-level bindings. Recursion is not supported.

### 5.4 Search (Solver)

```ktr
let tweak = search (t: f64) {
  bounds t [0.6 .. 1.6]
  tolerance 1mm
  require neck_quarter(t).length == target_neck
}
```

A `search` expression declares a solver variable. The runtime finds a
value for the parameter within the given `bounds` such that the `require`
constraint is satisfied within the given `tolerance`.

### 5.5 Exports

```ktr
export neck_quarter(tweak) as "Neck Curve"
```

An `export` marks a value for output by the runtime (e.g., rendering as
SVG). The string label is the human-readable name.

---

## 6. Built-in Functions and Methods

### 6.1 Constructors

| Function                    | Signature                                  |
|-----------------------------|--------------------------------------------|
| `point(x, y)`              | `(length, length) -> point`                |
| `bezier(p1, p2, p3, p4)`   | `(point, point, point, point) -> bezier`   |
| `line(start, end)`         | `(point, point) -> line`                   |

### 6.2 Field Accessors

Composite types expose named fields via dot syntax. Field access can be
chained (e.g., `some_line.point1.x`).

#### Point Fields

| Field | Type     | Description                        |
|-------|----------|------------------------------------|
| `.x`  | `length` | Horizontal coordinate of the point |
| `.y`  | `length` | Vertical coordinate of the point   |

#### Line Fields

| Field     | Type    | Description              |
|-----------|---------|--------------------------|
| `.point1` | `point` | Start point of the line  |
| `.point2` | `point` | End point of the line    |

#### Bezier Fields

| Field     | Type    | Description                     |
|-----------|---------|---------------------------------|
| `.point1` | `point` | First control point (start)     |
| `.point2` | `point` | Second control point            |
| `.point3` | `point` | Third control point             |
| `.point4` | `point` | Fourth control point (end)      |

### 6.3 Point Methods

| Method         | Signature                      | Description                      |
|----------------|--------------------------------|----------------------------------|
| `.up(d)`       | `(point, length) -> point`     | Shift point up by `d`            |
| `.down(d)`     | `(point, length) -> point`     | Shift point down by `d`          |
| `.left(d)`     | `(point, length) -> point`     | Shift point left by `d`          |
| `.right(d)`    | `(point, length) -> point`     | Shift point right by `d`         |
| `.dx(other)`   | `(point, point) -> length`     | Horizontal distance to `other`   |
| `.dy(other)`   | `(point, point) -> length`     | Vertical distance to `other`     |

### 6.4 Curve Methods

| Method         | Signature                      | Description                      |
|----------------|--------------------------------|----------------------------------|
| `.length`      | `(bezier) -> length`           | Arc length of the curve          |

---

## 7. Full Example

```ktr
input head = 100mm {
  assert head > 0mm
  assert head < 800mm
}

input target_neck = 200mm {
  assert target_neck > 0mm
  assert target_neck < 500mm
}

fn neck_quarter(tweak: f64) {
  let right  = point(tweak * head / 10, 0mm)
  let bottom = point(0mm, tweak * head / 12)
  let cp1 = right.up(bottom.dy(right) / 2)
  let cp2 = bottom.right(bottom.dx(right) / 2)
  return bezier(right, cp1, cp2, bottom)
}

let tweak = search (t: f64) {
  bounds t [0.6 .. 1.6]
  tolerance 1mm
  require neck_quarter(t).length == target_neck
}

export neck_quarter(tweak) as "Neck Curve"
```

---

## 8. Compiler Pipeline

```
.ktr source
  │
  ├─ lexer    ─── tokenization
  ├─ parser   ─── AST construction
  ├─ sema     ─── type checking, name resolution
  ├─ lower    ─── AST + Sema → IR
  └─ ir_emit  ─── IR → .ktrir text

.ktrir text
  │
  ├─ ir_parse     ─── .ktrir text → IR  (for runtimes)
  └─ ir_decompile ─── IR → .ktr text    (roundtrip verification)
```

---

## 9. Implementation Status

The compiler currently implements the following subset:

- [x] `let` bindings with literal values (`100mm`, `50%`, `42`)
- [x] `let` bindings with identifier references (`let y = x`)
- [x] Type inference for `length`, `percentage`, `f64`
- [x] Arithmetic expressions (`+`, `-`, `*`, `/`) with precedence
- [x] Parenthesized grouping
- [x] Duplicate binding detection
- [x] Undefined reference detection
- [x] Poison type for error suppression
- [x] IR lowering, emission, parsing, and decompilation
- [x] Full roundtrip: `.ktr` → IR → `.ktrir` → IR → `.ktr`
- [x] Runtime evaluator (`ktrr`) with unit normalization (cm → mm)
- [x] Runtime WASM module with JSON output
- [x] `input` declarations with literal defaults (`input head = 100mm`)
- [x] Runtime input overrides (parametric evaluation)
- [x] `point`, `bezier`, `line` constructor types with full pipeline support
- [x] `fn` definitions with typed parameters
- [x] Function calls (user-defined and built-in constructors)
- [x] Field accessors (`.x`, `.y`, `.point1`, etc.) with chaining

Planned (not yet implemented):

- [ ] `input` assertion blocks (`assert head > 0mm`)
- [ ] Unary negation (`-expr`)
- [ ] Method calls (`.up()`, `.dx()`, etc.)
- [ ] `search` solver blocks
- [ ] `export` statements
- [ ] `bool` type

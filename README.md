<picture>
  <source media="(prefers-color-scheme: dark)" srcset="./resources/repo-banner-dark.png">
  <source media="(prefers-color-scheme: light)" srcset="./resources/repo-banner-light.png">
  <img alt="ktr" src="./resources/repo-banner-light.png">
</picture>

# ktr

ktr is a domain-specific language for parametric sewing patterns. It describes
patterns as geometry and constraints that compile into a stable, diffable
intermediate representation (`.ktrir`) consumed by runtimes.

> **Status:** Early development (v0.1.0). The compiler currently handles `let`
> bindings with literals and identifier references. See
> [Implementation Status](#implementation-status) below.

## Example

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

## Goals

- Define sewing patterns as precise geometry with explicit drafting constraints.
- Support fully parametric patterns driven by body measurements.
- Compile to a stable, diffable IR suitable for version control and visual editors.
- Provide TypeScript and Zig runtimes out of the box.
- Expose a C-defined runtime interface, enabling portable runtimes and bindings in any language.
- Ship first-class tooling: compiler, LSP and editor integrations.

ktr is designed for reproducible pattern drafting, not for general-purpose programming.

## Repository Structure

```
ktrc/              Compiler (Zig)
  src/               Lexer, parser, sema, IR lowering, emit/parse/decompile
  spec/              Formal grammars (ktr.ebnf, ktrir.ebnf) and language reference
website/           Documentation site (Astro)
  src/pages/         Landing page, reference docs, playground
  public/ktrc.wasm   Compiler WASM module for the browser playground
```

## Building

The compiler requires [Zig](https://ziglang.org/) (0.14+).

```sh
cd ktrc

# Run all tests
zig build test

# Build the CLI
zig build

# Compile a .ktr file to .ktrir
zig build run -- compile program.ktr
zig build run -- compile program.ktr -o output.ktrir

# Decompile .ktrir back to .ktr
zig build run -- decompile output.ktrir

# Pipe through both directions
cat file.ktr | zig build run -- compile | zig build run -- decompile

# Build the WASM module
zig build wasm
```

The website requires [Bun](https://bun.sh/):

```sh
cd website
bun install
bun run dev
```

## Language Reference

The full language reference is in [`ktrc/spec/lang.md`](ktrc/spec/lang.md).
Standalone EBNF grammars:

- [`ktr.ebnf`](ktrc/spec/ktr.ebnf) -- source language grammar
- [`ktrir.ebnf`](ktrc/spec/ktrir.ebnf) -- intermediate representation grammar

## Implementation Status

The compiler currently implements:

- [x] `let` bindings with literal values (`100mm`, `50%`, `42`)
- [x] `let` bindings with identifier references (`let y = x`)
- [x] Type inference for `length`, `percentage`, `f64`
- [x] Duplicate binding detection
- [x] Undefined reference detection
- [x] Poison type for error suppression
- [x] IR lowering, emission, parsing, and decompilation
- [x] Full roundtrip: `.ktr` → IR → `.ktrir` → IR → `.ktr`
- [x] WASM build target with browser playground

Planned:

- [ ] `input` declarations with assertion blocks
- [ ] Arithmetic expressions (`+`, `-`, `*`, `/`)
- [ ] `fn` definitions with typed parameters
- [ ] Function calls and constructor calls (`point()`, `bezier()`)
- [ ] Method calls (`.up()`, `.dx()`, etc.)
- [ ] `search` solver blocks
- [ ] `export` statements
- [ ] `point`, `bezier`, `bool` types

## License

[MIT](LICENSE)

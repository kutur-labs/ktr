---
title: Introduction
order: 1
---

# Introduction

ktr is a domain-specific language for parametric sewing patterns.  
It describes patterns as geometry and constraints.

A ktr program is compiled into a canonical, diffable IR and executed by a runtime.

## Goals

- Define sewing patterns as precise geometry with explicit drafting constraints.
- Support fully parametric patterns driven by body measurements.
- Compile to a stable, diffable IR suitable for version control and visual editors.
- Provide TypeScript and Zig runtimes out of the box.
- Expose a C-defined runtime interface, enabling portable runtimes and bindings in any language.
- Ship first-class tooling: compiler, LSP and editor integrations.

ktr is designed for reproducible pattern drafting, not for general-purpose programming.

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
  let right  = point(tweak * head / 10, 0mm)
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

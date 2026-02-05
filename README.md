<picture>
  <source media="(prefers-color-scheme: dark)" srcset="./resources/repo-banner-dark.png">
  <source media="(prefers-color-scheme: light)" srcset="./resources/repo-banner-light.png">
  <img alt="ktr" src="./resources/repo-banner-light.png">
</picture>

# ktr

ktr is a DSL for parametric sewing patterns that compiles geometry and constraints into a diffable, runtime-independent IR. It describes patterns as geometry and constraints.

A ktr program is compiled into a canonical, diffable IR and executed by a runtime.

## Goals

- Define sewing patterns as precise geometry with explicit drafting constraints.
- Support fully parametric patterns driven by body measurements.
- Compile to a stable, diffable IR suitable for version control and visual editors.
- Provide TypeScript and Zig runtimes out of the box.
- Expose a C-defined runtime interface, enabling portable runtimes and bindings in any language.
- Ship first-class tooling: compiler, LSP and editor integrations.

ktr is designed for reproducible pattern drafting, not for general-purpose programming.

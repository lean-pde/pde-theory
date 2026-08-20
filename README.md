# pde-theory

Foundational **partial differential equation (PDE) theory**, formalized in
[Lean 4](https://lean-lang.org/) on top of
[mathlib4](https://github.com/leanprover-community/mathlib4).

## Mission

Build the foundational mathematics of PDE theory in Lean — the definitions,
constructions, and theorems (function spaces, weak derivatives, distributions,
Sobolev theory, and the existence/uniqueness/regularity results that rest on them)
that a serious body of PDE work needs but that mathlib does not yet contain.

## Vision

- **An upstreaming staging ground.** Almost everything here is intended to eventually
  land in mathlib4. This repository exists so that development is not blocked by
  upstreaming latency: results mature here and are contributed upstream as they
  stabilize. The long-run goal is for this library to shrink as its contents migrate
  into mathlib.
- **The shared foundation for the `lean-pde` organization.** Every paper formalized in
  this organization depends on this repository plus mathlib, co-versioned. `pde-theory`
  is the common base those formalizations build on, so that they share definitions and
  don't re-derive the groundwork.
- **Always current with mathlib.** The library tracks the latest mathlib4 release. Being
  a faithful, idiomatic extension of mathlib — same conventions, same style — is what
  makes upstreaming realistic.

## Relationship to mathlib

This project is **co-versioned** with mathlib: it is pinned to a specific mathlib
*release tag*, and the Lean toolchain matches that tag.

| Component | Version |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.33.0` |
| mathlib4 | tag `v4.33.0` |

Version bumps are performed **manually**. To adopt a newer mathlib release, update both
`lean-toolchain` and the `rev` of the mathlib dependency in `lakefile.toml` to the same
`vX.Y.Z` release tag, then run `lake update mathlib` and `lake exe cache get`.

## Building

Requires [`elan`](https://github.com/leanprover/elan) (which provides the pinned Lean
toolchain automatically).

```sh
lake exe cache get   # download the prebuilt mathlib cache (do this before building)
lake build           # build the PDETheory library
```

## Layout

```
PDETheory.lean        -- library root; imports the modules below
PDETheory/
  Basic.lean          -- placeholder "hello world" module
```

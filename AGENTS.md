# Agent guidance for `pde-theory`

Foundational PDE theory in Lean 4 on top of mathlib4, co-versioned with mathlib (currently pinned to
the `v4.33.0` release; bump `lean-toolchain` and the mathlib `rev` together, then `lake update`). The
library aims at a mathlib-upstreaming quality bar: **zero `sorry`, zero warnings**, coordinate-free
and idiomatic.

## Imports: use specific modules, never `import Mathlib`

**Do not write `import Mathlib`.** Importing the whole library forces every file to load the entire
mathlib environment before elaboration, which makes each build take *minutes* (observed ~300s per
file) and makes the interactive `lean-lsp` server time out on first elaboration. Instead import the
specific mathlib modules a file actually needs — the transitive closure is far smaller, so builds and
LSP are dramatically faster.

Guidelines:
- Import the module that **defines** each mathlib lemma/def you use (not one that merely uses it).
  Find it with `grep -rlE "^(theorem|lemma|def|instance) <name>" .lake/packages/mathlib/Mathlib`.
- Prefer importing another `PDETheory.*` module over re-importing what it already pulls in —
  transitive imports carry through.
- Keep the import list minimal but complete; if the build reports an unknown identifier, add the
  module that defines it rather than falling back to `import Mathlib`.
- Reference points for the analysis/measure layers used here:
  - `Mathlib.Analysis.Calculus.ContDiff.Defs` — `ContDiff`, `.of_le`, `.continuous`,
    `.continuous_fderiv`, `.differentiable`; `Mathlib.Analysis.Calculus.ContDiff.Operations` for the
    arithmetic `.add/.neg/.const_smul` (imports `Defs`).
  - `Mathlib.Analysis.Normed.Module.FiniteDimension` — finite-dim normed-space facts, incl. the
    `SecondCountableTopology`/`ProperSpace` instances.
  - `Mathlib.Analysis.Calculus.FDeriv.Const` — `fderiv_of_notMem_tsupport`, `HasCompactSupport.fderiv`.
  - `Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts` — the multidimensional integration by
    parts `integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable` (and the Bochner-integral / Haar
    infrastructure it pulls in).
  - `Mathlib.Analysis.FunctionalSpaces.SobolevInequality` — Gagliardo–Nirenberg–Sobolev
    (`eLpNorm_le_eLpNorm_fderiv_of_le`, …).
  - `Mathlib.MeasureTheory.Function.LpSpace.Indicator` — `MemLp`, `eLpNorm`,
    `Continuous.memLp_of_hasCompactSupport`.
  - `Mathlib.MeasureTheory.Function.LocallyIntegrable` — `Continuous.integrable_of_hasCompactSupport`,
    `Continuous.locallyIntegrable`.
  - `Mathlib.MeasureTheory.Function.LpSeminorm.Basic` — `eLpNorm_zero`, `MemLp.restrict`.
  - `Mathlib.MeasureTheory.VectorMeasure.SetIntegral` — `∫ x in s, …` and
    `setIntegral_eq_integral_of_forall_compl_eq_zero`.
  - `Mathlib.Topology.Algebra.Support` — `HasCompactSupport.add/.neg/.smul_left`, `tsupport_*`.
  - `Mathlib.Geometry.Euclidean.Volume.Measure` — `μHE[·]` (`euclideanHausdorffMeasure`) and its Haar
    instance (only where the Euclidean-normalized surface/volume measure is used).

## Conventions

- **Zero `sorry`, zero warnings.** Every file must `lake build` cleanly. Check
  `grep -rnwE "sorry|admit" PDETheory/` is empty. Fix unused-section-variable linter warnings with
  `omit [...] in` (which must precede the docstring) or by scoping variables tightly.
- **Coordinate-free where possible.** Develop over an abstract normed / inner-product space `E` and
  specialize to `EuclideanSpace ℝ (Fin d)` only where dimension or coordinates are essential. Add
  `[InnerProductSpace ℝ E]` only where the inner product is actually used (weak-derivative and
  `W^{1,p}` layers need only `[NormedSpace ℝ E]`).
- **Predicate style** for definitions (`IsFoo`/`HasFoo`/`MemFoo : Prop`), with dotted extraction
  lemmas; bundle into structures/types only where a genuine algebraic object is needed.
- **Module docstrings** in mathlib style: `# Title`, `## Main definitions`, `## Main results`,
  `## Implementation notes`, `## References`.

## Build tips

- `lake build PDETheory.Path.To.Module` builds a single module (and its dependencies); use this while
  iterating rather than a full `lake build`.
- mathlib oleans are cached; if a dependency cache is missing, `lake exe cache get`.
- Some mathlib gotchas seen at v4.33.0: `fderiv_of_notMem_tsupport` takes an **explicit** field
  argument (`fderiv_of_notMem_tsupport ℝ h`); the smoothness order is `WithTop ℕ∞` with `∞`/`ω`
  notation (`open scoped ContDiff`), and `∞` cannot appear in an identifier name; downgrade
  `ContDiff ∞` to `ContDiff 1` with `.of_le (mod_cast le_top)`; use `simp`/`exact` rather than `rw`
  under an unreduced `fun x => …` redex; real inner product is `⟪x, y⟫` (no `_ℝ`; `open scoped
  RealInnerProductSpace`).

import PDETheory.Analysis.Sobolev.TestFunction
import PDETheory.Analysis.Sobolev.WeakDeriv
import PDETheory.Analysis.Sobolev.MemWkp
import PDETheory.Analysis.Sobolev.MemW1p0
import PDETheory.Analysis.Sobolev.Poincare
import PDETheory.Analysis.Sobolev.Divergence
import PDETheory.Analysis.Sobolev.LpOn
import PDETheory.Analysis.Sobolev.H10Space
import PDETheory.Analysis.Sobolev.LaxMilgram

/-!
# Sobolev spaces on domains

Aggregator for the theory of Sobolev spaces on a domain `Ω`, built on the coordinate-free weak
Fréchet derivative. Re-exports:

* `PDETheory.Analysis.Sobolev.TestFunction` — the test-field predicate `IsTestField` / `IsTestFn`
  (smooth, compactly supported, `tsupport ⊆ Ω`) and its structural and analytic properties.
* `PDETheory.Analysis.Sobolev.WeakDeriv` — the weak directional / Fréchet derivative
  (`IsWeakDerivDir`, `IsWeakDeriv`) and that a `C¹` field's classical derivative is its weak
  derivative (`contDiff_isWeakDeriv`).
* `PDETheory.Analysis.Sobolev.MemWkp` — `Lᵖ(Ω)` (`MemLpOn`), `W^{1,p}(Ω)` (`MemW1p`) and `H¹(Ω)`
  (`MemH1`), with `IsTestField.memW1p`.
* `PDETheory.Analysis.Sobolev.MemW1p0` — the zero-trace space `W^{1,p}₀(Ω)` (`MemW1p0`) / `H¹₀(Ω)`
  (`MemH10`), with `IsTestField.memW1p0`.
* `PDETheory.Analysis.Sobolev.Poincare` — the Poincaré inequality for test fields on a bounded
  domain (`poincare_testField`) and its extension to `H¹₀` (`poincare_H10`).
* `PDETheory.Analysis.Sobolev.Divergence` — the divergence of a `𝕜`-valued vector field
  (`vectorDivergence`) and the distributional divergence-free condition (`IsWeaklyDivFree`).
* `PDETheory.Analysis.Sobolev.LpOn` — the bundled `Lᵖ(Ω)` Banach/Hilbert space (`LpOn`) with the
  `Mem…`-to-bundled bridge (`MemLpOn.toLpOn`, `norm_toLpOn`).
* `PDETheory.Analysis.Sobolev.H10Space` — the bundled `H¹₀(Ω)` Hilbert space in coordinate form
  (`H10Space`), with the Hilbert–Schmidt Jacobian (`gradPi`, `GradFib`) as the coordinate model
  for the weak gradient.
* `PDETheory.Analysis.Sobolev.LaxMilgram` — the weak-form operator interface: the bounded operator
  of a `ℂ`-sesquilinear form (`formOperator`) and the real coercive Lax–Milgram equivalence
  (`coerciveEquiv`).
-/

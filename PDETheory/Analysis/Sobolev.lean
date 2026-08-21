import PDETheory.Analysis.Sobolev.TestFunction

/-!
# Sobolev spaces on domains

Aggregator for the theory of Sobolev spaces on a domain `Ω`, built on the coordinate-free weak
Fréchet derivative. Re-exports:

* `PDETheory.Analysis.Sobolev.TestFunction` — the test-field predicate `IsTestField` / `IsTestFn`
  (smooth, compactly supported, `tsupport ⊆ Ω`) and its structural and analytic properties.

Further modules (weak derivative, `W^{1,p}`/`H¹`, `W^{1,p}₀`/`H¹₀`, Poincaré/coercivity, …) are
added as the development proceeds.
-/

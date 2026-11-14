module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Data.Finsupp.Indicator
public import Mathlib.Data.PNat.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Order.LiminfLimsup

/-!
# Frozen: `PrimeCarleson.multDiff`

The definition as the author approved it before any proof used it; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson

/-- The iterated conjugation-difference `Δ_{h₁,…,h_s} f` (e:triangle):
`Δ_h f(x) = f(x) · conj (f(x + h))` and `Δ_{h₁,…,h_s} f = Δ_{h_s}(Δ_{h₁,…,h_{s-1}} f)`. -/
def multDiff : (s : ℕ) → (Fin s → ℤ) → (ℤ → ℂ) → ℤ → ℂ
  | 0, _, f => f
  | s + 1, h, f => fun x =>
      multDiff s (Fin.init h) f x * conj (multDiff s (Fin.init h) f (x + h (Fin.last s)))

end PrimeCarleson

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
public import PrimeCarleson.Frozen.Exp

/-!
# Frozen: `PrimeCarleson.majorArcModel`

The definition as the author approved it before any proof used it; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson

/-- The major-arc model `∑_{q ≤ M} ∑_{1 ≤ a ≤ q, (a, q) = 1} S(a/q) e(n a / q)`. -/
def majorArcModel (S : ℚ → ℂ) (M : ℕ) (n : ℤ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 M, ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
    S ((a : ℚ) / q) * e ((n : ℝ) * a / q)

end PrimeCarleson

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
public import PrimeCarleson.Frozen.ModulatedSum

/-!
# Frozen: `PrimeCarleson.carlesonMax`

The definition as the author approved it before any proof used it; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson

/-- The maximally modulated operator `sup_{λ ∈ 𝕋} |∑_{n ≠ 0} f(x - n) w(|n|) e(λ n) / n|`:
`𝒞_ℙ` of (e:CP) for `w = Λ`, and `𝒞_v` of the Appendix A.1 lemma for `w = v`. -/
def carlesonMax (w : ℕ → ℝ) (f : ℤ →₀ ℂ) (x : ℤ) : ℝ≥0∞ :=
  ⨆ lam ∈ Set.Ico (0 : ℝ) 1, ‖modulatedSum w f lam x‖ₑ

end PrimeCarleson

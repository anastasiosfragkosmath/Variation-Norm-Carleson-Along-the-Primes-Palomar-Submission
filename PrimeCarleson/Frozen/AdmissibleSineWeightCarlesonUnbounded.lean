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
public import PrimeCarleson.Frozen.Admissible
public import PrimeCarleson.Frozen.SineWeight
public import PrimeCarleson.Frozen.CarlesonMax
import PrimeCarleson.Proof.AdmissibleSineWeightCarlesonUnbounded

/-!
# Frozen: `PrimeCarleson.admissible_sineWeight_carleson_unbounded`

The statement as the author approved it before any proof was written; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson

/-- **Appendix A.1 lemma.** For `0 < α < 1` and an integer `q₀ ≥ 3`, the weight
`v(n) = 1 + α sin(2πn/q₀)` is admissible, but `𝒞_v` (sum over `n ≠ 0`, as in (e:CP)) is
unbounded on `ℓ^p` for each `1 ≤ p ≤ ∞`. -/
theorem admissible_sineWeight_carleson_unbounded (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1)
    (q₀ : ℕ) (hq₀ : 3 ≤ q₀) :
    Admissible (sineWeight α q₀) ∧
      ∀ p : ℝ≥0∞, 1 ≤ p → ¬ ∃ K : ℝ, ∀ f : ℤ →₀ ℂ,
        eLpNorm (carlesonMax (sineWeight α q₀) f) p Measure.count ≤
          ENNReal.ofReal K * eLpNorm (⇑f) p Measure.count :=
  by exact PrimeCarleson.Proof.admissible_sineWeight_carleson_unbounded

end PrimeCarleson

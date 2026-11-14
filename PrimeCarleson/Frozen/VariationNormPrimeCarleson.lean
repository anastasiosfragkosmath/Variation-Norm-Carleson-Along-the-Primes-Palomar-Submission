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
public import PrimeCarleson.Frozen.PrimeVariation
import PrimeCarleson.Proof.VariationNormPrimeCarleson

/-!
# Frozen: `PrimeCarleson.variation_norm_prime_carleson`

The statement as the author approved it before any proof was written; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson

/-- **Theorem 1.3 (`t:main`).** For each `r > 2` there are `𝐜(r) , 𝐂(r)` with
`r' < 𝐜(r) < 2 < 𝐂(r)`, `𝐜(r) → 1` and `𝐂(r) → ∞` as `r → ∞`, and for each
`𝐜(r) < p < 𝐂(r)` a constant `0 < C_{p,r} < ∞` with `‖𝒱^r_ℙ f‖_{ℓ^p} ≤ C_{p,r} ‖f‖_{ℓ^p}`. -/
theorem variation_norm_prime_carleson :
    ∃ c C : ℝ → ℝ,
      (∀ r : ℝ, 2 < r → r / (r - 1) < c r ∧ c r < 2 ∧ 2 < C r) ∧
      Tendsto c atTop (𝓝 1) ∧ Tendsto C atTop atTop ∧
      ∀ r : ℝ, 2 < r → ∀ p : ℝ, c r < p → p < C r →
        ∃ K : ℝ, 0 < K ∧ ∀ f : ℤ →₀ ℂ,
          eLpNorm (primeVariation r f) (ENNReal.ofReal p) Measure.count ≤
            ENNReal.ofReal K * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count :=
  by exact PrimeCarleson.Proof.variation_norm_prime_carleson

end PrimeCarleson

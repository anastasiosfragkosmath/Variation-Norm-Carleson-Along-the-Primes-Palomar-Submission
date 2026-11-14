module

public import PrimeCarleson.Frozen.VariationNormPrimeCarleson
public import PrimeCarleson.Frozen.PrimeCarlesonMaximal

/-!
# Solution: the two main theorems, proved

The statements of `Challenge.lean`, word for word, proved by the development's theorems
`PrimeCarleson.variation_norm_prime_carleson` (Theorem 1.3, `t:main`, in
`PrimeCarleson/Frozen/VariationNormPrimeCarleson.lean`) and
`PrimeCarleson.prime_carleson_maximal` (`t:carmax`, in
`PrimeCarleson/Frozen/PrimeCarlesonMaximal.lean`), which have the same statements. The
definitions they use are imported from the development under the names the challenge uses.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Palomar

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
  PrimeCarleson.variation_norm_prime_carleson

/-- **`t:carmax`.** For every `1 < p < ∞` there is `0 < C_p < ∞` with
`‖𝒞_ℙ f‖_{ℓ^p} ≤ C_p ‖f‖_{ℓ^p}`. -/
theorem prime_carleson_maximal :
    ∀ p : ℝ, 1 < p → ∃ K : ℝ, 0 < K ∧ ∀ f : ℤ →₀ ℂ,
      eLpNorm (carlesonMax (ArithmeticFunction.vonMangoldt : ℕ → ℝ) f) (ENNReal.ofReal p)
          Measure.count ≤
        ENNReal.ofReal K * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count :=
  PrimeCarleson.prime_carleson_maximal

end PrimeCarleson.Palomar

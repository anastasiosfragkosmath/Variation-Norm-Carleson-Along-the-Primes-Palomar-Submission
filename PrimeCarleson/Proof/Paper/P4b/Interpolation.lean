module

public import PrimeCarleson.Proof.Paper.P4a.LpCount
public import PrimeCarleson.Proof.Paper.Defs.Basic
public import PrimeCarleson.Proof.Common.Variation
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Interpolation of the pointwise variation in the exponent

Source: main paper `c:U3modvariation`, L1057–L1067 (the paper says "follows immediately by
interpolation", L1056); the mechanism is the log-convexity of the variation in the exponent and
Hölder's inequality:

* pointwise, `V^r(a_λ(x)) ≤ V²(a_λ(x))^{2/r} (2 sup_λ |a_λ(x)|)^{1-2/r}` for `r ≥ 2`
  (`Common.rVariationOn_le_interpolate`, `ρ = 2`);
* Hölder in `x` with the exponents `r/2` and `r/(r-2)` (`eLpNorm_two_count_le_rpow_mul`).

`eLpNorm_pointwiseVariation_le` is the resulting inequality for an arbitrary family
`a : ℝ → ℤ → ℂ`, and `eLpNorm_pointwiseVariation_le_of_bounds` the form used by the consumers
(the two endpoint bounds `P`, `Q` in, the interpolated bound out).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- Hölder in `ℓ²(ℤ)` (Hölder's inequality, exponents `1/θ` and `1/(1-θ)`
on the squares): if `a ≤ A^θ B^{1-θ}` pointwise (`0 ≤ θ ≤ 1`), then
`‖a‖_{ℓ²} ≤ ‖A‖_{ℓ²}^θ ‖B‖_{ℓ²}^{1-θ}`. -/
theorem eLpNorm_two_count_le_rpow_mul {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {a A B : ℤ → ℝ≥0∞}
    (h : ∀ x, a x ≤ A x ^ θ * B x ^ (1 - θ)) :
    eLpNorm a 2 Measure.count ≤
      eLpNorm A 2 Measure.count ^ θ * eLpNorm B 2 Measure.count ^ (1 - θ) := by
  have hθ' : 0 ≤ 1 - θ := sub_nonneg.2 hθ1
  rw [eLpNorm_two_count_enn, eLpNorm_two_count_enn, eLpNorm_two_count_enn]
  have h1 : ∑' x, a x ^ (2 : ℝ) ≤
      (∑' x, A x ^ (2 : ℝ)) ^ θ * (∑' x, B x ^ (2 : ℝ)) ^ (1 - θ) := by
    calc ∑' x, a x ^ (2 : ℝ)
        ≤ ∑' x, (A x ^ (2 : ℝ)) ^ θ * (B x ^ (2 : ℝ)) ^ (1 - θ) := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          calc a x ^ (2 : ℝ) ≤ (A x ^ θ * B x ^ (1 - θ)) ^ (2 : ℝ) :=
                ENNReal.rpow_le_rpow (h x) (by norm_num)
            _ = (A x ^ (2 : ℝ)) ^ θ * (B x ^ (2 : ℝ)) ^ (1 - θ) := by
                rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
                  ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_comm θ 2,
                  mul_comm (1 - θ) 2]
      _ ≤ (∑' x, A x ^ (2 : ℝ)) ^ θ * (∑' x, B x ^ (2 : ℝ)) ^ (1 - θ) := by
          have := ENNReal.lintegral_mul_norm_pow_le (μ := (Measure.count : Measure ℤ))
            (f := fun x : ℤ => A x ^ (2 : ℝ)) (g := fun x : ℤ => B x ^ (2 : ℝ))
            (Measurable.of_discrete.aemeasurable) (Measurable.of_discrete.aemeasurable) hθ0 hθ'
            (by ring)
          simpa only [lintegral_count] using this
  calc (∑' x, a x ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ ((∑' x, A x ^ (2 : ℝ)) ^ θ * (∑' x, B x ^ (2 : ℝ)) ^ (1 - θ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h1 (by norm_num)
    _ = ((∑' x, A x ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ θ *
          ((∑' x, B x ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ (1 - θ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_comm θ, mul_comm (1 - θ)]

/-- **The interpolation in `r`, the mechanism** (Source: main paper `c:U3modvariation`, L1056): for
`r ≥ 2` and any family `a : ℝ → ℤ → ℂ`,
`‖V^r(a_λ : λ ∈ 𝕋)‖_{ℓ²} ≤ ‖V²(a_λ : λ ∈ 𝕋)‖_{ℓ²}^{2/r} (2 ‖sup_λ |a_λ|‖_{ℓ²})^{1-2/r}` (pointwise
log-convexity `V^r ≤ (V²)^{2/r} (2 sup)^{1-2/r}` and Hölder in `x`). -/
theorem eLpNorm_pointwiseVariation_le {r : ℝ} (hr : 2 ≤ r) (a : ℝ → ℤ → ℂ) :
    eLpNorm (pointwiseVariation r a) 2 Measure.count ≤
      eLpNorm (pointwiseVariation 2 a) 2 Measure.count ^ (2 / r) *
        (2 * eLpNorm (fun x => ⨆ lam : ℝ, ‖a lam x‖ₑ) 2 Measure.count) ^ (1 - 2 / r) := by
  have hr0 : 0 < r := by linarith
  have hθ0 : 0 ≤ 2 / r := by positivity
  have hθ1 : 2 / r ≤ 1 := (div_le_one hr0).2 hr
  have hpt : ∀ x, pointwiseVariation r a x ≤
      pointwiseVariation 2 a x ^ (2 / r) *
        (2 * ⨆ lam : ℝ, ‖a lam x‖ₑ) ^ (1 - 2 / r) := by
    intro x
    have h := Common.rVariationOn_le_interpolate (ρ := 2) (r := r) two_pos hr (Set.Ico 0 1)
      (fun l => a l x)
    refine h.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow ?_ (sub_nonneg.2 hθ1)))
    refine mul_le_mul' le_rfl ?_
    exact iSup₂_le fun t _ => le_iSup (fun lam : ℝ => ‖a lam x‖ₑ) t
  have h := eLpNorm_two_count_le_rpow_mul hθ0 hθ1
    (a := pointwiseVariation r a) (A := pointwiseVariation 2 a)
    (B := fun x => 2 * ⨆ lam : ℝ, ‖a lam x‖ₑ) hpt
  refine h.trans (le_of_eq ?_)
  congr 2
  have := eLpNorm_count_const_mul 2 (fun x => ⨆ lam : ℝ, ‖a lam x‖ₑ) (p := 2) two_pos
  simpa only [ENNReal.ofReal_ofNat] using this

/-- **The interpolation in `r`, quantitative form** (Source: main paper `c:U3modvariation`, L1056):
if the family `a : ℝ → ℤ → ℂ` has the endpoint bounds `‖V²(a_λ)‖_{ℓ²} ≤ P F` and
`‖sup_λ |a_λ|‖_{ℓ²} ≤ Q F` (`P, Q ≥ 0`, `F ∈ [0, ∞]`), then for `r ≥ 2`,
`‖V^r(a_λ)‖_{ℓ²} ≤ P^{2/r} (2Q)^{1-2/r} F`. -/
theorem eLpNorm_pointwiseVariation_le_of_bounds {r : ℝ} (hr : 2 ≤ r) (a : ℝ → ℤ → ℂ) {P Q : ℝ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) {F : ℝ≥0∞}
    (h2 : eLpNorm (pointwiseVariation 2 a) 2 Measure.count ≤ ENNReal.ofReal P * F)
    (hsup : eLpNorm (fun x => ⨆ lam : ℝ, ‖a lam x‖ₑ) 2 Measure.count ≤ ENNReal.ofReal Q * F) :
    eLpNorm (pointwiseVariation r a) 2 Measure.count ≤
      ENNReal.ofReal (P ^ (2 / r) * (2 * Q) ^ (1 - 2 / r)) * F := by
  have hr0 : 0 < r := by linarith
  have hθ0 : 0 ≤ 2 / r := by positivity
  have hθ1 : 2 / r ≤ 1 := (div_le_one hr0).2 hr
  have hθ' : 0 ≤ 1 - 2 / r := sub_nonneg.2 hθ1
  refine (eLpNorm_pointwiseVariation_le hr a).trans ?_
  calc eLpNorm (pointwiseVariation 2 a) 2 Measure.count ^ (2 / r) *
        (2 * eLpNorm (fun x => ⨆ lam : ℝ, ‖a lam x‖ₑ) 2 Measure.count) ^ (1 - 2 / r)
      ≤ (ENNReal.ofReal P * F) ^ (2 / r) * (2 * (ENNReal.ofReal Q * F)) ^ (1 - 2 / r) := by
        gcongr
    _ = ENNReal.ofReal (P ^ (2 / r) * (2 * Q) ^ (1 - 2 / r)) * F := by
        have h2Q : (2 : ℝ≥0∞) * (ENNReal.ofReal Q * F) = ENNReal.ofReal (2 * Q) * F := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, mul_assoc]
        have e1 : ENNReal.ofReal (P ^ (2 / r) * (2 * Q) ^ (1 - 2 / r)) =
            ENNReal.ofReal P ^ (2 / r) * ENNReal.ofReal (2 * Q) ^ (1 - 2 / r) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_rpow_of_nonneg hP hθ0,
            ENNReal.ofReal_rpow_of_nonneg (by positivity) hθ']
        rw [h2Q, ENNReal.mul_rpow_of_nonneg _ _ hθ0, ENNReal.mul_rpow_of_nonneg _ _ hθ', e1]
        calc ENNReal.ofReal P ^ (2 / r) * F ^ (2 / r) *
              (ENNReal.ofReal (2 * Q) ^ (1 - 2 / r) * F ^ (1 - 2 / r))
            = ENNReal.ofReal P ^ (2 / r) * ENNReal.ofReal (2 * Q) ^ (1 - 2 / r) *
              (F ^ (2 / r) * F ^ (1 - 2 / r)) := by ring
          _ = ENNReal.ofReal P ^ (2 / r) * ENNReal.ofReal (2 * Q) ^ (1 - 2 / r) * F := by
              rw [← ENNReal.rpow_add_of_nonneg _ _ hθ0 hθ', add_sub_cancel, ENNReal.rpow_one]

end PrimeCarleson.Proof.Paper

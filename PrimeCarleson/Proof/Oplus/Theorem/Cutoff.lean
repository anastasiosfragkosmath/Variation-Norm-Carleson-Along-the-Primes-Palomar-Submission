module

public import PrimeCarleson.Proof.Oplus.Theorem.Bump
public import Mathlib.Analysis.Fourier.Convolution

/-!
# The Fourier cutoff operator and its `L¹`, `L^∞` and `L^p` bounds

Helper for the Fourier cutoff of [O+] `linearizedtheorem` ([O+] L921-L926).

* `cutOp χ f = f ⋆ 𝓕⁻χ`: the Schwartz function with `𝓕(cutOp χ f) = 𝓕f · χ`
  (`fourier_cutOp`), given by the convolution formula `cutOp_apply`;
* `lintegral_enorm_cutOp_le`: `‖f ⋆ κ‖_{L¹} ≤ ‖f‖_{L¹} ‖κ‖_{L¹}` (Young);
* `norm_le_integral_norm_fourier`: `‖g‖_{L^∞} ≤ ‖ĝ‖_{L¹}` (Fourier inversion);
* `eLpNorm_le_of_enorm_le_of_lintegral_le`: `‖g‖_{L^p}^p ≤ ‖g‖_{L^∞}^{p-1} ‖g‖_{L¹}` for `p > 1`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

/-- The Fourier multiplier operator `f ↦ f ⋆ 𝓕⁻χ` on Schwartz functions:
`𝓕(cutOp χ f) = 𝓕 f · χ`. -/
def cutOp (χ f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f (𝓕⁻ χ)

/-- `𝓕(cutOp χ f) = 𝓕f · χ`. -/
theorem fourier_cutOp (χ f : 𝓢(ℝ, ℂ)) (η : ℝ) :
    𝓕 (⇑(cutOp χ f)) η = 𝓕 (⇑f) η * χ η := by
  have h := congrArg (fun g : 𝓢(ℝ, ℂ) => g η)
    (SchwartzMap.fourier_convolution (ContinuousLinearMap.mul ℂ ℂ) f (𝓕⁻ χ))
  simp only [SchwartzMap.pairing_apply_apply, SchwartzMap.fourier_coe] at h
  have h2 : 𝓕 ⇑(𝓕⁻ χ : 𝓢(ℝ, ℂ)) = ⇑χ := by
    rw [← SchwartzMap.fourier_coe, FourierInvPair.fourier_fourierInv_eq]
  unfold cutOp
  rw [h, h2]
  simp

/-- The convolution formula `cutOp χ f (x) = ∫ f(y) 𝓕⁻χ(x - y) dy`. -/
theorem cutOp_apply (χ f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    cutOp χ f x = ∫ y, f y * (𝓕⁻ χ : 𝓢(ℝ, ℂ)) (x - y) := by
  unfold cutOp
  rw [SchwartzMap.convolution_apply, convolution_mul]

/-- **Young's inequality in `L¹`**: `‖cutOp χ f‖_{L¹} ≤ ‖f‖_{L¹} ‖𝓕⁻χ‖_{L¹}`. -/
theorem lintegral_enorm_cutOp_le (χ f : 𝓢(ℝ, ℂ)) :
    ∫⁻ x, ‖cutOp χ f x‖ₑ ≤ (∫⁻ y, ‖f y‖ₑ) * ∫⁻ y, ‖(𝓕⁻ χ : 𝓢(ℝ, ℂ)) y‖ₑ := by
  set κ : 𝓢(ℝ, ℂ) := 𝓕⁻ χ with hκ
  have hmeas : Measurable (Function.uncurry fun (x y : ℝ) => ‖f y‖ₑ * ‖κ (x - y)‖ₑ) := by
    have h1 : Measurable fun p : ℝ × ℝ => ‖f p.2‖ₑ :=
      (f.continuous.enorm.measurable).comp measurable_snd
    have h2 : Measurable fun p : ℝ × ℝ => ‖κ (p.1 - p.2)‖ₑ :=
      (κ.continuous.enorm.measurable).comp (measurable_fst.sub measurable_snd)
    exact h1.mul h2
  calc ∫⁻ x, ‖cutOp χ f x‖ₑ ≤ ∫⁻ x, ∫⁻ y, ‖f y‖ₑ * ‖κ (x - y)‖ₑ := by
        refine lintegral_mono fun x => ?_
        rw [cutOp_apply]
        refine (enorm_integral_le_lintegral_enorm _).trans ?_
        simp_rw [enorm_mul]
        exact le_rfl
    _ = ∫⁻ y, ∫⁻ x, ‖f y‖ₑ * ‖κ (x - y)‖ₑ := lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ y, ‖f y‖ₑ * ∫⁻ x, ‖κ x‖ₑ := by
        refine lintegral_congr fun y => ?_
        have hm : Measurable fun x : ℝ => ‖κ (x - y)‖ₑ :=
          κ.continuous.enorm.measurable.comp (measurable_id.sub_const y)
        rw [lintegral_const_mul _ hm]
        congr 1
        exact lintegral_sub_right_eq_self (fun x => ‖κ x‖ₑ) y
    _ = _ := by
        rw [lintegral_mul_const _ f.continuous.enorm.measurable]

/-- `‖g‖_{L^∞} ≤ ‖ĝ‖_{L¹}` for a Schwartz function `g` (Fourier inversion). -/
theorem norm_le_integral_norm_fourier (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖g x‖ ≤ ∫ η, ‖𝓕 (⇑g) η‖ := by
  rw [fourier_inversion_schwartz g x]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine le_of_eq (integral_congr_ae (Eventually.of_forall fun η => ?_))
  simp [norm_e]

/-- **Interpolation between `L¹` and `L^∞`**: for `p > 1`,
`‖g‖_{L^p} ≤ (δ^{p-1} M)^{1/p}` if `|g| ≤ δ` and `‖g‖_{L¹} ≤ M`. -/
theorem eLpNorm_le_of_enorm_le_of_lintegral_le {g : ℝ → ℂ} {p : ℝ} (hp : 1 < p) {δ M : ℝ≥0∞}
    (hg : AEStronglyMeasurable g volume) (hδ0 : δ ≠ ⊤) (hδ : ∀ x, ‖g x‖ₑ ≤ δ)
    (hM : ∫⁻ x, ‖g x‖ₑ ≤ M) :
    eLpNorm g (ENNReal.ofReal p) volume ≤ (δ ^ (p - 1) * M) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hp0]) (by simp) hg,
    ENNReal.toReal_ofReal hp0.le]
  gcongr
  calc ∫⁻ x, ‖g x‖ₑ ^ p ≤ ∫⁻ x, δ ^ (p - 1) * ‖g x‖ₑ := by
        refine lintegral_mono fun x => ?_
        have : ‖g x‖ₑ ^ p = ‖g x‖ₑ ^ (p - 1) * ‖g x‖ₑ := by
          conv_lhs => rw [show p = (p - 1) + 1 by ring]
          rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
        rw [this]
        gcongr
        exact hδ x
    _ = δ ^ (p - 1) * ∫⁻ x, ‖g x‖ₑ :=
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) hδ0)
    _ ≤ _ := by gcongr

end PrimeCarleson.Proof.Oplus

module

public import PrimeCarleson.Proof.Paper.P6a.Hyps
public import PrimeCarleson.Proof.Paper.P7.VarcarZ

/-!
# `l:varcarZ` in the form used by `P6a/` from the Euclidean estimate

`P6a/` takes `l:varcarZ` as the named `Prop` `VarCarZ r` (`P6a/Hyps.lean`), for a multiplier
`m : ℝ → ℂ` with no measurability hypothesis and the factor `r/(r-2)`; `P7/` proves it, for
measurable `k̂` and with the constant `C_r`, from `OplusVariationBound` (`varcarZ_of_oplus`). The
adapter `varCarZ_of_oplusBound` bridges the three mismatches:

* a function of finite total variation on `ℝ` is measurable
  (`BoundedVariationOn.measurable`);
* `r/(r-2) ≥ 1` for `r > 2`, so the constant of `P7/` is absorbed;
* `varOp r u f x = V^r(λ ↦ ∑_n f(x-n) u(n) e(λ n) : λ ∈ [0, 1))` and the `ℓ²` norm is
  `(∑_x F(x)²)^{1/2}`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-- The modulated sum with the kernel `k(n) = ∫ m(ξ) e(nξ) dξ` is `dilSum m 1`. -/
theorem weightedModSum_eq_dilSum_one (m : ℝ → ℂ) (f : ℤ →₀ ℂ) (lam : ℝ) (x : ℤ) :
    weightedModSum (fun n : ℤ => ∫ ξ : ℝ, m ξ * e ((n : ℝ) * ξ)) (⇑f) lam x =
      dilSum m 1 f x lam := by
  unfold weightedModSum dilSum
  refine tsum_congr fun n => ?_
  simp only [one_mul]
  ring

/-- **`l:varcarZ` in the form used by `P6a/`** (conditional on `hO : OplusVariationBound`): for
every `r > 2`, `VarCarZ r`. -/
theorem varCarZ_of_oplusBound (hO : OplusVariationBound) {r : ℝ} (hr : 2 < r) : VarCarZ r := by
  obtain ⟨C, hC0, hC⟩ := varcarZ_of_oplus hO hr
  have hr2 : 0 < r - 2 := by linarith
  have hge : (1 : ℝ) ≤ r / (r - 2) := by rw [le_div_iff₀ hr2]; linarith
  refine ⟨C, hC0, fun m a hsupp c₀ hc₀ hvar f => ?_⟩
  have hm : Measurable m := by
    have hfin : BoundedVariationOn m Set.univ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvar
    exact hfin.measurable
  have h := hC m c₀ a hm hsupp hvar f (Set.Ico 0 1) le_rfl
  rw [← eLpNorm_two_eq_tsum_sq', ← eLpNorm_two_eq_tsum_sq] at h
  have hfun : (fun x : ℤ => rVariationOn r (Set.Ico 0 1) (fun lam => dilSum m 1 f x lam)) =
      varOp r (fun n : ℤ => ∫ ξ : ℝ, m ξ * e ((n : ℝ) * ξ)) (⇑f) := by
    funext x
    rw [varOp_eq]
    exact congrArg (rVariationOn r (Set.Ico 0 1))
      (funext fun lam => (weightedModSum_eq_dilSum_one m f lam x).symm)
  rw [hfun] at h
  refine h.trans (mul_le_mul_left ?_ _)
  exact ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hC0 hc₀])

end PrimeCarleson.Proof.Paper

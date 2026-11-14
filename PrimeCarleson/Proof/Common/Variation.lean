module

public import PrimeCarleson.Frozen.RVariation
public import PrimeCarleson.Proof.MswTransference.Variation
public import Mathlib.Analysis.MeanInequalities

/-!
# Elementary facts about the `r`-variation

A toolkit of elementary properties of the `PrimeCarleson.rVariationOn`: monotonicity in
`r`, the triangle inequality, log-convexity in `r` and interpolation of the sequence norms (the
paper, `sources/Variational_Carleson.tex`, uses them freely when passing between exponents):

* `rVariation_eq_rVariationOn`: `rVariation r a` is the `r`-variation over `[0, 1)`;
* `rVariationOn_mono_set`: monotonicity in the index set;
* `rVariationOn_anti_exponent`: `V^s ≤ V^r` for `0 < r ≤ s`;
* `rVariationOn_add_le`, `rVariationOn_sum_le`: the triangle inequality for `1 ≤ r`;
* `rVariationOn_const_smul`: homogeneity;
* `sum_rpow_rpow_le_interpolate`, `rVariationOn_le_interpolate`: log-convexity in the exponent,
  `V^r ≤ (V^ρ)^{ρ/r} (2 sup |a|)^{1-ρ/r}` for `0 < ρ ≤ r`.

All statements are in `ℝ≥0∞`; no finiteness hypothesis is needed.
-/

@[expose] public noncomputable section

open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Common

open PrimeCarleson PrimeCarleson.Proof.MswTransference

/-- `rVariation r a` is the `r`-variation over the index set `[0, 1)`. -/
theorem rVariation_eq_rVariationOn (r : ℝ) (a : ℝ → ℂ) :
    rVariation r a = rVariationOn r (Set.Ico 0 1) a := rfl

/-- The `r`-variation is monotone in the index set. -/
theorem rVariationOn_mono_set {r : ℝ} {S T : Set ℝ} (h : S ⊆ T) (a : ℝ → ℂ) :
    rVariationOn r S a ≤ rVariationOn r T a :=
  rVariationOn_le fun _ _ hm hS => le_rVariationOn hm fun i => h (hS i)

/-- Sequence-norm interpolation, `ℝ≥0∞`-valued version: for `0 < ρ ≤ r`,
`(∑ xᵢ^r)^{1/r} ≤ (∑ xᵢ^ρ)^{1/r} (sup xᵢ)^{1-ρ/r}`. -/
theorem sum_rpow_rpow_le_interpolate {ι : Type*} (s : Finset ι) {ρ r : ℝ} (hρ : 0 < ρ)
    (hρr : ρ ≤ r) (x : ι → ℝ≥0∞) :
    (∑ i ∈ s, x i ^ r) ^ (1 / r) ≤
      (∑ i ∈ s, x i ^ ρ) ^ (1 / r) * (⨆ i ∈ s, x i) ^ (1 - ρ / r) := by
  have hr : 0 < r := hρ.trans_le hρr
  have h1 : ∑ i ∈ s, x i ^ r ≤ (⨆ i ∈ s, x i) ^ (r - ρ) * ∑ i ∈ s, x i ^ ρ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    calc x i ^ r = x i ^ (r - ρ) * x i ^ ρ := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.2 hρr) hρ.le]
          congr 1
          ring
      _ ≤ (⨆ i ∈ s, x i) ^ (r - ρ) * x i ^ ρ := by
          gcongr
          exact le_iSup₂ (f := fun i (_ : i ∈ s) => x i) i hi
  have hexp : (r - ρ) * (1 / r) = 1 - ρ / r := by
    field_simp
  calc (∑ i ∈ s, x i ^ r) ^ (1 / r)
      ≤ ((⨆ i ∈ s, x i) ^ (r - ρ) * ∑ i ∈ s, x i ^ ρ) ^ (1 / r) :=
        ENNReal.rpow_le_rpow h1 (by positivity)
    _ = (∑ i ∈ s, x i ^ ρ) ^ (1 / r) * (⨆ i ∈ s, x i) ^ (1 - ρ / r) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, hexp, mul_comm]

/-- The `ℓ^r` norms of a finite family decrease in `r`: for `0 < r ≤ s`,
`(∑ xᵢ^s)^{1/s} ≤ (∑ xᵢ^r)^{1/r}`. -/
theorem sum_rpow_rpow_anti_exponent {ι : Type*} (t : Finset ι) {r s : ℝ} (hr : 0 < r)
    (hrs : r ≤ s) (x : ι → ℝ≥0∞) :
    (∑ i ∈ t, x i ^ s) ^ (1 / s) ≤ (∑ i ∈ t, x i ^ r) ^ (1 / r) := by
  have hs : 0 < s := hr.trans_le hrs
  set P : ℝ≥0∞ := ∑ i ∈ t, x i ^ r with hP
  have hsup : (⨆ i ∈ t, x i) ≤ P ^ (1 / r) := by
    refine iSup₂_le fun i hi => ?_
    rw [one_div, ENNReal.le_rpow_inv_iff hr]
    exact Finset.single_le_sum (f := fun i => x i ^ r) (fun _ _ => zero_le) hi
  have hexp : 1 / r * (1 - r / s) = 1 / r - 1 / s := by
    field_simp
  have hnn : 0 ≤ 1 / r - 1 / s := by
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le hr hrs
  calc (∑ i ∈ t, x i ^ s) ^ (1 / s)
      ≤ P ^ (1 / s) * (⨆ i ∈ t, x i) ^ (1 - r / s) :=
        sum_rpow_rpow_le_interpolate t hr hrs x
    _ ≤ P ^ (1 / s) * (P ^ (1 / r)) ^ (1 - r / s) := by
        gcongr
        rw [sub_nonneg]
        exact div_le_one_of_le₀ hrs hs.le
    _ = P ^ (1 / r) := by
        rw [← ENNReal.rpow_mul, hexp, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) hnn]
        congr 1
        ring

/-- `V^s ≤ V^r` for `0 < r ≤ s` (`ℓ^r` norms decrease in `r`). -/
theorem rVariationOn_anti_exponent {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) (S : Set ℝ)
    (a : ℝ → ℂ) : rVariationOn s S a ≤ rVariationOn r S a := by
  refine rVariationOn_le fun J t hm hS => ?_
  have h1 := sum_rpow_rpow_anti_exponent Finset.univ hr hrs
    (fun i : Fin J => ‖a (t i.castSucc) - a (t i.succ)‖ₑ)
  have h2 := le_rVariationOn (r := r) (S := S) (a := a) hm hS
  exact h1.trans h2

/-- The `r`-variation of the zero family vanishes. -/
theorem rVariationOn_zero {r : ℝ} (hr : 0 < r) (S : Set ℝ) :
    rVariationOn r S (0 : ℝ → ℂ) = 0 := by
  refine le_antisymm (rVariationOn_le fun J t _ _ => ?_) zero_le
  have h : ∀ i : Fin J, ‖(0 : ℝ → ℂ) (t i.castSucc) - (0 : ℝ → ℂ) (t i.succ)‖ₑ ^ r = 0 := by
    intro i
    simp [ENNReal.zero_rpow_of_pos hr]
  simp only [h, Finset.sum_const_zero]
  exact (ENNReal.zero_rpow_of_pos (one_div_pos.2 hr)).le

/-- Triangle inequality for the `r`-variation, `1 ≤ r`. -/
theorem rVariationOn_add_le {r : ℝ} (hr : 1 ≤ r) (S : Set ℝ) (a b : ℝ → ℂ) :
    rVariationOn r S (a + b) ≤ rVariationOn r S a + rVariationOn r S b := by
  refine rVariationOn_le fun J t hm hS => ?_
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  calc (∑ i : Fin J, ‖(a + b) (t i.castSucc) - (a + b) (t i.succ)‖ₑ ^ r) ^ (1 / r)
      ≤ (∑ i : Fin J, (‖a (t i.castSucc) - a (t i.succ)‖ₑ +
          ‖b (t i.castSucc) - b (t i.succ)‖ₑ) ^ r) ^ (1 / r) := by
        refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun i _ => ?_) (by positivity)
        refine ENNReal.rpow_le_rpow ?_ hr0
        simp only [Pi.add_apply]
        rw [add_sub_add_comm]
        exact enorm_add_le _ _
    _ ≤ (∑ i : Fin J, ‖a (t i.castSucc) - a (t i.succ)‖ₑ ^ r) ^ (1 / r) +
          (∑ i : Fin J, ‖b (t i.castSucc) - b (t i.succ)‖ₑ ^ r) ^ (1 / r) :=
        ENNReal.Lp_add_le _ _ _ hr
    _ ≤ rVariationOn r S a + rVariationOn r S b :=
        add_le_add (le_rVariationOn hm hS) (le_rVariationOn hm hS)

/-- Triangle inequality for finite sums of families in the `r`-variation, `1 ≤ r`. -/
theorem rVariationOn_sum_le {ι : Type*} (s : Finset ι) {r : ℝ} (hr : 1 ≤ r) (S : Set ℝ)
    (a : ι → ℝ → ℂ) :
    rVariationOn r S (∑ i ∈ s, a i) ≤ ∑ i ∈ s, rVariationOn r S (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rVariationOn_zero (zero_lt_one.trans_le hr)]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (rVariationOn_add_le hr S _ _).trans (add_le_add_right ih _)

/-- Scalar multiplication scales the `r`-variation by at most `‖c‖ₑ`. -/
private theorem rVariationOn_const_smul_le {r : ℝ} (hr : 0 < r) (S : Set ℝ) (c : ℂ)
    (a : ℝ → ℂ) : rVariationOn r S (c • a) ≤ ‖c‖ₑ * rVariationOn r S a := by
  refine rVariationOn_le fun J t hm hS => ?_
  have hr0 : 0 ≤ r := hr.le
  calc (∑ i : Fin J, ‖(c • a) (t i.castSucc) - (c • a) (t i.succ)‖ₑ ^ r) ^ (1 / r)
      = ‖c‖ₑ * (∑ i : Fin J, ‖a (t i.castSucc) - a (t i.succ)‖ₑ ^ r) ^ (1 / r) := by
        simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, enorm_mul]
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr0]
        rw [← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / r),
          ← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one]
    _ ≤ ‖c‖ₑ * rVariationOn r S a := mul_le_mul_right (le_rVariationOn hm hS) _

/-- Homogeneity of the `r`-variation: `V^r(c a) = |c| V^r(a)`. -/
theorem rVariationOn_const_smul {r : ℝ} (hr : 0 < r) (S : Set ℝ) (c : ℂ) (a : ℝ → ℂ) :
    rVariationOn r S (c • a) = ‖c‖ₑ * rVariationOn r S a := by
  refine le_antisymm (rVariationOn_const_smul_le hr S c a) ?_
  by_cases hc : c = 0
  · simp [hc]
  · have h := rVariationOn_const_smul_le hr S c⁻¹ (c • a)
    rw [← mul_smul, inv_mul_cancel₀ hc, one_smul] at h
    calc ‖c‖ₑ * rVariationOn r S a ≤ ‖c‖ₑ * (‖c⁻¹‖ₑ * rVariationOn r S (c • a)) :=
          mul_le_mul_right h _
      _ = rVariationOn r S (c • a) := by
          rw [← mul_assoc, ← enorm_mul, mul_inv_cancel₀ hc, enorm_one, one_mul]

/-- Log-convexity in the exponent: `V^r ≤ (V^ρ)^{ρ/r} (2 sup_S |a|)^{1-ρ/r}` for `0 < ρ ≤ r`. -/
theorem rVariationOn_le_interpolate {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (S : Set ℝ)
    (a : ℝ → ℂ) :
    rVariationOn r S a ≤ rVariationOn ρ S a ^ (ρ / r) * (2 * ⨆ t ∈ S, ‖a t‖ₑ) ^ (1 - ρ / r) := by
  have hr : 0 < r := hρ.trans_le hρr
  have hnn : 0 ≤ 1 - ρ / r := sub_nonneg.2 (div_le_one_of_le₀ hρr hr.le)
  refine rVariationOn_le fun J t hm hS => ?_
  have h1 := sum_rpow_rpow_le_interpolate Finset.univ hρ hρr
    (fun i : Fin J => ‖a (t i.castSucc) - a (t i.succ)‖ₑ)
  refine h1.trans (mul_le_mul' ?_ ?_)
  · calc (∑ i : Fin J, ‖a (t i.castSucc) - a (t i.succ)‖ₑ ^ ρ) ^ (1 / r)
        = ((∑ i : Fin J, ‖a (t i.castSucc) - a (t i.succ)‖ₑ ^ ρ) ^ (1 / ρ)) ^ (ρ / r) := by
          rw [← ENNReal.rpow_mul]
          congr 1
          field_simp
      _ ≤ rVariationOn ρ S a ^ (ρ / r) :=
          ENNReal.rpow_le_rpow (le_rVariationOn hm hS) (by positivity)
  · refine ENNReal.rpow_le_rpow ?_ hnn
    refine iSup₂_le fun i _ => ?_
    calc ‖a (t i.castSucc) - a (t i.succ)‖ₑ
        ≤ ‖a (t i.castSucc)‖ₑ + ‖a (t i.succ)‖ₑ := enorm_sub_le
      _ ≤ (⨆ u ∈ S, ‖a u‖ₑ) + ⨆ u ∈ S, ‖a u‖ₑ :=
          add_le_add (le_iSup₂_of_le (t i.castSucc) (hS _) le_rfl)
            (le_iSup₂_of_le (t i.succ) (hS _) le_rfl)
      _ = 2 * ⨆ u ∈ S, ‖a u‖ₑ := (two_mul _).symm

end PrimeCarleson.Proof.Common

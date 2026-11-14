module

public import PrimeCarleson.Proof.Paper.P6a.Basic
public import Mathlib.Analysis.BoundedVariation

/-!
# A partition of unity of `ℝ` by hat functions of support length `1/10`

For the tiling of the error multiplier `KQerr_Q` (Source: main paper `p:red-var`, L1483–L1502): the
hat functions `hat t ξ = max(0, 1 - 20 |ξ - t/20|)`, `t ∈ ℤ`, are continuous, `20`-Lipschitz,
supported in `((t-1)/20, (t+1)/20)` (an interval of length `1/10`), and sum to `1`. Since `hat t`
vanishes at the end points of its support, `m · hat t` has no jump terms in its total variation.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

/-- The hat function `max(0, 1 - 20 |ξ - t/20|)`. -/
def hat (t : ℤ) (ξ : ℝ) : ℝ := max (1 - 20 * |ξ - (t : ℝ) / 20|) 0

theorem hat_nonneg (t : ℤ) (ξ : ℝ) : 0 ≤ hat t ξ := le_max_right _ _

theorem hat_le_one (t : ℤ) (ξ : ℝ) : hat t ξ ≤ 1 := by
  unfold hat
  refine max_le ?_ (by norm_num)
  have : 0 ≤ 20 * |ξ - (t : ℝ) / 20| := by positivity
  linarith

/-- `hat t` vanishes outside `((t-1)/20, (t+1)/20)`. -/
theorem hat_eq_zero {t : ℤ} {ξ : ℝ} (h : ξ ∉ Ioo (((t : ℝ) - 1) / 20) (((t : ℝ) + 1) / 20)) :
    hat t ξ = 0 := by
  unfold hat
  refine max_eq_right ?_
  have : 1 / 20 ≤ |ξ - (t : ℝ) / 20| := by
    by_contra hc
    rw [not_le, abs_lt] at hc
    exact h ⟨by linarith [hc.1], by linarith [hc.2]⟩
  linarith

theorem continuous_hat (t : ℤ) : Continuous (hat t) := by
  unfold hat
  fun_prop

/-- `hat t` is `20`-Lipschitz. -/
theorem lipschitzWith_hat (t : ℤ) : LipschitzWith 20 (hat t) := by
  have h1 : LipschitzWith 20 (fun ξ : ℝ => 1 - 20 * |ξ - (t : ℝ) / 20|) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [Real.dist_eq, NNReal.coe_ofNat]
    have : |(1 - 20 * |x - (t : ℝ) / 20|) - (1 - 20 * |y - (t : ℝ) / 20|)| =
        20 * |(|y - (t : ℝ) / 20| - |x - (t : ℝ) / 20|)| := by
      rw [show (1 - 20 * |x - (t : ℝ) / 20|) - (1 - 20 * |y - (t : ℝ) / 20|) =
        20 * (|y - (t : ℝ) / 20| - |x - (t : ℝ) / 20|) by ring, abs_mul]
      norm_num
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
    rw [show y - (t : ℝ) / 20 - (x - (t : ℝ) / 20) = y - x by ring, abs_sub_comm]
  exact h1.max_const 0

/-- **Partition of unity**: `∑_{t ∈ ℤ} hat t ξ = 1`. -/
theorem hasSum_hat (ξ : ℝ) : HasSum (fun t : ℤ => hat t ξ) 1 := by
  set j : ℤ := ⌊20 * ξ⌋ with hj
  have h1 : (j : ℝ) ≤ 20 * ξ := Int.floor_le _
  have h2 : 20 * ξ < j + 1 := Int.lt_floor_add_one _
  have hsub : ∀ t ∉ ({j, j + 1} : Finset ℤ), hat t ξ = 0 := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    unfold hat
    refine max_eq_right ?_
    have : 1 / 20 ≤ |ξ - (t : ℝ) / 20| := by
      rcases lt_or_gt_of_ne ht.1 with h | h
      · have : (t : ℝ) + 1 ≤ j := by exact_mod_cast (by omega : t + 1 ≤ j)
        rw [le_abs]; left; linarith
      · have h3 : (j : ℝ) + 2 ≤ t := by exact_mod_cast (by omega : j + 2 ≤ t)
        rw [le_abs]; right; linarith
    linarith
  have hh := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℤ)
    (f := fun t : ℤ => hat t ξ) hsub
  rw [Finset.sum_pair (by omega)] at hh
  have e1 : hat j ξ = 1 - (20 * ξ - j) := by
    unfold hat
    rw [abs_of_nonneg (by linarith), max_eq_left (by linarith)]
    ring
  have e2 : hat (j + 1) ξ = 20 * ξ - j := by
    unfold hat
    push_cast
    rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
    ring
  rw [e1, e2] at hh
  convert hh using 1
  ring

/-- The total variation of a hat function over its support interval is at most `2`. -/
theorem eVariationOn_hat_le (t : ℤ) :
    eVariationOn (hat t) (Icc (((t : ℝ) - 1) / 20) (((t : ℝ) + 1) / 20)) ≤ 2 := by
  have h := (lipschitzWith_hat t).lipschitzOnWith (s := univ)
    |>.comp_eVariationOn_le (g := id) (s := Icc (((t : ℝ) - 1) / 20) (((t : ℝ) + 1) / 20))
      (fun _ _ => mem_univ _)
  have h2 := eVariationOn_id_Icc (((t : ℝ) - 1) / 20) (((t : ℝ) + 1) / 20)
  refine (h.trans ?_)
  rw [Function.comp_id] at *
  have h3 : (((t : ℝ) + 1) / 20 - ((t : ℝ) - 1) / 20) = 1 / 10 := by ring
  rw [h2, h3]
  have : ((20 : NNReal) : ℝ≥0∞) = 20 := by simp
  rw [this, ← ENNReal.ofReal_ofNat 20, ← ENNReal.ofReal_mul (by norm_num)]
  have : (20 : ℝ) * (1 / 10) = 2 := by norm_num
  rw [this]; simp

end PrimeCarleson.Proof.Paper

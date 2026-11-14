module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The geometric series of Lépingle's inequality

Source: Zorin-Kranich's notes, (02-Lepingle.tex, L164–L165): the weights
`2^{-(m-2)(r-2)/2}`, `m ≥ 2`, sum to at most `(3/2) · r / (r - 2)` for every `r > 2`.

With `k = m - 2`, `lepingleWeight r k = ((2⁻¹)^k)^{(r-2)/2} = 2^{-k(r-2)/2}` (`lepingleWeight_eq`);
`tsum_lepingleWeight_le` is the bound `∑_k 2^{-k(r-2)/2} ≤ (3/2) r/(r-2)`. The proof computes the
sum `(1 - q)⁻¹` of the geometric series `q = 2^{-(r-2)/2}` and uses
`2^y ≥ 1 + y log 2 ≥ 1 + (2/3) y`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Lepingle

/-- The weight `2^{-(m-2)(r-2)/2}` of the level `m = k + 2` in Lépingle's inequality. -/
def lepingleWeight (r : ℝ) (k : ℕ) : ℝ := ((2⁻¹ : ℝ) ^ k) ^ ((r - 2) / 2)

theorem lepingleWeight_nonneg (r : ℝ) (k : ℕ) : 0 ≤ lepingleWeight r k :=
  Real.rpow_nonneg (by positivity) _

/-- `2^{-(k)(r-2)/2} = q^k` with the ratio `q = 2^{-(r-2)/2}`. -/
theorem lepingleWeight_eq (r : ℝ) (k : ℕ) :
    lepingleWeight r k = ((2⁻¹ : ℝ) ^ ((r - 2) / 2)) ^ k := by
  unfold lepingleWeight
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul (by positivity), mul_comm]

/-- The square of the weight is `((2⁻¹)^k)^{r-2} = 2^{-k(r-2)}`, the weight of (2.7) at `ρ = 2`. -/
theorem lepingleWeight_sq (r : ℝ) (k : ℕ) :
    lepingleWeight r k ^ 2 = ((2⁻¹ : ℝ) ^ k) ^ (r - 2) := by
  unfold lepingleWeight
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  ring

/-- The ratio `q = 2^{-(r-2)/2}` of the geometric series lies in `(0, 1)` for `r > 2`. -/
theorem lepingleRatio_lt_one {r : ℝ} (hr : 2 < r) : (2⁻¹ : ℝ) ^ ((r - 2) / 2) < 1 :=
  Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)

theorem summable_lepingleWeight {r : ℝ} (hr : 2 < r) : Summable (lepingleWeight r) := by
  have : lepingleWeight r = fun k => ((2⁻¹ : ℝ) ^ ((r - 2) / 2)) ^ k :=
    funext (lepingleWeight_eq r)
  rw [this]
  exact summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _) (lepingleRatio_lt_one hr)

/-- **Geometric series** (Zorin-Kranich's notes, L164-L165): for `r > 2`,
`∑_{m ≥ 2} 2^{-(m-2)(r-2)/2} ≤ (3/2) · r / (r - 2)`. -/
theorem tsum_lepingleWeight_le {r : ℝ} (hr : 2 < r) :
    ∑' k : ℕ, lepingleWeight r k ≤ 3 / 2 * (r / (r - 2)) := by
  have hr0 : 0 < r := by linarith
  have hr2 : 0 < r - 2 := by linarith
  set q : ℝ := (2⁻¹ : ℝ) ^ ((r - 2) / 2) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := lepingleRatio_lt_one hr
  have hsum : ∑' k : ℕ, lepingleWeight r k = (1 - q)⁻¹ := by
    have : lepingleWeight r = fun k => q ^ k := funext (lepingleWeight_eq r)
    rw [this]
    exact tsum_geometric_of_lt_one hq0.le hq1
  -- `X = 2^{(r-2)/2} ≥ 1 + (r-2)/3`
  set X : ℝ := (2 : ℝ) ^ ((r - 2) / 2) with hX
  have hXq : q = X⁻¹ := by
    rw [hq, hX, Real.inv_rpow (by norm_num)]
  have hXge : (r + 1) / 3 ≤ X := by
    have h1 : X = Real.exp (((r - 2) / 2) * Real.log 2) := by
      rw [hX, Real.rpow_def_of_pos (by norm_num), mul_comm]
    have h2 := Real.add_one_le_exp (((r - 2) / 2) * Real.log 2)
    have h3 := Real.log_two_gt_d9
    rw [← h1] at h2
    nlinarith
  have hXpos : 0 < X := Real.rpow_pos_of_pos (by norm_num) _
  have hqle : q ≤ 3 / (r + 1) := by
    rw [hXq]
    calc X⁻¹ ≤ ((r + 1) / 3)⁻¹ := inv_anti₀ (by positivity) hXge
      _ = 3 / (r + 1) := by rw [inv_div]
  have h1q : 0 < 1 - q := by linarith
  rw [hsum, inv_le_comm₀ h1q (by positivity)]
  have hcalc : (3 / 2 * (r / (r - 2)))⁻¹ = 2 * (r - 2) / (3 * r) := by
    field_simp
  rw [hcalc]
  have hle : 1 - 3 / (r + 1) ≤ 1 - q := by linarith
  refine le_trans ?_ hle
  rw [show (1 : ℝ) - 3 / (r + 1) = (r - 2) / (r + 1) by field_simp; ring,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

end PrimeCarleson.Proof.Lepingle

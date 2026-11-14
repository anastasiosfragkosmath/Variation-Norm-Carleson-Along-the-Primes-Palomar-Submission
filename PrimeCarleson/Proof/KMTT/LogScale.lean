module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# KMTT's logarithmic scale and Japanese bracket

Source: [KMTT] `log-scale`, L275–L284 (arXiv:2409.10510v2,
[KMTT] TeX):

* `jbracket x = (1 + |x|²)^{1/2}` (the Japanese bracket `⟨x⟩`);
* `logScale Q = ⌊log Q / log 2⌋` (the natural number `Log Q` with `2^(Log Q) ≤ Q < 2^(Log Q + 1)`);
* `logBracket Q = ⟨Log Q⟩`.

Elementary facts used by the Rankin steps of KMTT Lemma 4.6 ([KMTT], L881–L886, L899–L902, L912–L916
and L919–L922):
`⟨Log Q⟩ ≥ max (1, Log Q)`, `log Q ≤ 2 ⟨Log Q⟩`, `r^(1/⟨Log Q⟩) ≤ 4` for `0 ≤ r ≤ Q`, and
`log Q / ⟨Log Q⟩ ≥ 1/2` for `Q ≥ 8`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.KMTT

/-- The Japanese bracket `⟨x⟩ = (1 + |x|²)^{1/2}` (KMTT L275). -/
def jbracket (x : ℝ) : ℝ := Real.sqrt (1 + x ^ 2)

/-- The logarithmic scale `Log Q = ⌊log Q / log 2⌋` (KMTT L282), a natural number for `Q ≥ 1`. -/
def logScale (Q : ℝ) : ℕ := ⌊Real.logb 2 Q⌋₊

/-- `⟨Log Q⟩`. -/
def logBracket (Q : ℝ) : ℝ := jbracket (logScale Q)

/-- `1 ≤ ⟨x⟩`. -/
theorem one_le_jbracket (x : ℝ) : 1 ≤ jbracket x := by
  unfold jbracket
  exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg x])

/-- `|x| ≤ ⟨x⟩`. -/
theorem abs_le_jbracket (x : ℝ) : |x| ≤ jbracket x := by
  unfold jbracket
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

/-- `⟨x⟩ ≤ 1 + |x|`. -/
theorem jbracket_le (x : ℝ) : jbracket x ≤ 1 + |x| := by
  unfold jbracket
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_abs x, abs_nonneg x]

/-- `0 < ⟨x⟩`. -/
theorem jbracket_pos (x : ℝ) : 0 < jbracket x := lt_of_lt_of_le one_pos (one_le_jbracket x)

/-- `1 ≤ ⟨Log Q⟩`. -/
theorem one_le_logBracket (Q : ℝ) : 1 ≤ logBracket Q := one_le_jbracket _

/-- `0 < ⟨Log Q⟩`. -/
theorem logBracket_pos (Q : ℝ) : 0 < logBracket Q := jbracket_pos _

/-- `Log Q ≤ ⟨Log Q⟩`. -/
theorem logScale_le_logBracket (Q : ℝ) : (logScale Q : ℝ) ≤ logBracket Q := by
  have := abs_le_jbracket (logScale Q : ℝ)
  rwa [abs_of_nonneg (Nat.cast_nonneg _)] at this

/-- `⟨Log Q⟩ ≤ 1 + Log Q`. -/
theorem logBracket_le (Q : ℝ) : logBracket Q ≤ 1 + logScale Q := by
  have := jbracket_le (logScale Q : ℝ)
  rwa [abs_of_nonneg (Nat.cast_nonneg _)] at this

/-- `2 ^ (Log Q) ≤ Q` for `Q ≥ 1`. -/
theorem two_pow_logScale_le {Q : ℝ} (hQ : 1 ≤ Q) : (2 : ℝ) ^ logScale Q ≤ Q := by
  have h0 : 0 ≤ Real.logb 2 Q := Real.logb_nonneg (by norm_num) hQ
  have h1 : (logScale Q : ℝ) ≤ Real.logb 2 Q := Nat.floor_le h0
  have := (Real.le_logb_iff_rpow_le (by norm_num) (by linarith)).mp h1
  rwa [Real.rpow_natCast] at this

/-- `Q < 2 ^ (Log Q + 1)` for `Q ≥ 1`. -/
theorem lt_two_pow_logScale_succ {Q : ℝ} (hQ : 1 ≤ Q) : Q < (2 : ℝ) ^ (logScale Q + 1) := by
  have h1 : Real.logb 2 Q < (logScale Q : ℝ) + 1 := Nat.lt_floor_add_one _
  have := (Real.logb_lt_iff_lt_rpow (by norm_num) (by linarith)).mp h1
  have h2 : ((logScale Q : ℝ) + 1) = ((logScale Q + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [h2, Real.rpow_natCast] at this
  exact this

/-- `log Q < (Log Q + 1) log 2`. -/
theorem log_lt_logScale_succ_mul {Q : ℝ} (hQ : 1 ≤ Q) :
    Real.log Q < ((logScale Q : ℝ) + 1) * Real.log 2 := by
  have h := Real.log_lt_log (by linarith) (lt_two_pow_logScale_succ hQ)
  rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at h

/-- `Log Q * log 2 ≤ log Q`. -/
theorem logScale_mul_log_two_le {Q : ℝ} (hQ : 1 ≤ Q) :
    (logScale Q : ℝ) * Real.log 2 ≤ Real.log Q := by
  have h := Real.log_le_log (by positivity) (two_pow_logScale_le hQ)
  rwa [Real.log_pow] at h

/-- `log Q ≤ 2 ⟨Log Q⟩` for `Q ≥ 1`. -/
theorem log_le_two_mul_logBracket {Q : ℝ} (hQ : 1 ≤ Q) : Real.log Q ≤ 2 * logBracket Q := by
  have h1 := log_lt_logScale_succ_mul hQ
  have h2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have h3 := logScale_le_logBracket Q
  have h4 := one_le_logBracket Q
  have h5 : (0 : ℝ) ≤ (logScale Q : ℝ) + 1 := by positivity
  nlinarith

/-- Rankin's trick: `r ^ (1 / ⟨Log Q⟩) ≤ 4` for `0 ≤ r ≤ Q`, `Q ≥ 1`. -/
theorem rpow_inv_logBracket_le_four {Q r : ℝ} (hQ : 1 ≤ Q) (hr0 : 0 ≤ r) (hrQ : r ≤ Q) :
    r ^ (1 / logBracket Q) ≤ 4 := by
  have hL := logBracket_pos Q
  have h1 : r ^ (1 / logBracket Q) ≤ Q ^ (1 / logBracket Q) :=
    Real.rpow_le_rpow hr0 hrQ (by positivity)
  refine h1.trans ?_
  rw [Real.rpow_def_of_pos (by linarith)]
  have h2 : Real.log Q * (1 / logBracket Q) ≤ Real.log 4 := by
    rw [mul_one_div, div_le_iff₀ hL]
    have h3 := log_le_two_mul_logBracket hQ
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have h5 := log_lt_logScale_succ_mul hQ
    have h6 := logScale_le_logBracket Q
    have h7 := one_le_logBracket Q
    have h8 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have h9 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [h4]
    nlinarith
  calc Real.exp (Real.log Q * (1 / logBracket Q)) ≤ Real.exp (Real.log 4) :=
        Real.exp_le_exp.mpr h2
    _ = 4 := Real.exp_log (by norm_num)

/-- `Log Q ≥ 3` for `Q ≥ 8`. -/
theorem three_le_logScale {Q : ℝ} (hQ : 8 ≤ Q) : 3 ≤ logScale Q := by
  unfold logScale
  refine Nat.le_floor ?_
  push_cast
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
  norm_num
  exact hQ

/-- `1/2 ≤ log Q / ⟨Log Q⟩` for `Q ≥ 8`. -/
theorem half_le_inv_logBracket_mul_log {Q : ℝ} (hQ : 8 ≤ Q) :
    1 / 2 ≤ (1 / logBracket Q) * Real.log Q := by
  have hQ1 : 1 ≤ Q := by linarith
  have hL := logBracket_pos Q
  have h3 : (3 : ℝ) ≤ logScale Q := by exact_mod_cast three_le_logScale hQ
  have h1 := logScale_mul_log_two_le hQ1
  have h2 := logBracket_le Q
  have h4 := Real.log_two_gt_d9
  rw [one_div_mul_eq_div, le_div_iff₀ hL]
  nlinarith

end PrimeCarleson.Proof.KMTT

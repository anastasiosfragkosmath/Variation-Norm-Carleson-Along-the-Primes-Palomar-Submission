module

public import PrimeCarleson.Proof.Fplus31.PNTSW.LogDeriv

/-!
# The logarithmic derivative of `L₁ = (s-1) ζ(s)` near the `1`-line

Part of the prime number theorem in progressions on the classical zero-free region
(`PNTSW/Main.lean`). The analogue of `PNTSW.LogDeriv.logDeriv_L_rect` for the entire function
`L₁(s) = (s-1) ζ(s)`, `L₁(1) = 1`: with `H = log (T + 4)` and `a = c / H`, `‖L₁'/L₁‖ ≤ 1800 H² / c²`
on `1 - a/2 ≤ re s ≤ 1 + a/4`, `|im s| ≤ T` (`logDeriv_zetaL1_rect`), and the trivial bound on the
line `re s = σ > 1` (`logDeriv_zetaL1_line`). The logarithm of `L₁(1 + a/4 + it)` is
`log (a/4 + it) + ∑ Λ(n)/log n · n^{-s}`.
-/

@[expose] public noncomputable section

open Metric Complex ArithmeticFunction LSeries
open scoped Real

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.PNTSW

/-- `‖log w‖ ≤ |log ‖w‖| + 4`. -/
theorem norm_log_le_aux (w : ℂ) :
    ‖Complex.log w‖ ≤ |Real.log ‖w‖| + 4 := by
  have h1 := Complex.norm_le_abs_re_add_abs_im (Complex.log w)
  rw [Complex.log_re] at h1
  have h2 : |(Complex.log w).im| ≤ π := by rw [Complex.log_im]; exact Complex.abs_arg_le_pi w
  have h3 : π ≤ 4 := Real.pi_le_four
  linarith

/-- The trivial bound for `L₁'/L₁` on `1 < re s ≤ 2`. -/
theorem logDeriv_zetaL1_line {s : ℂ} (hs : 1 < s.re) (hs2 : s.re ≤ 2) :
    ‖deriv zetaL1 s / zetaL1 s‖ ≤ 8 / (s.re - 1) ^ 2 + 1 / (s.re - 1) := by
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hs; simp at hs
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have e : deriv zetaL1 s / zetaL1 s = deriv riemannZeta s / riemannZeta s + 1 / (s - 1) := by
    have := neg_logDeriv_zeta_split hs1 hz
    linear_combination this
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have := logDeriv_L_line (1 : DirichletCharacter ℂ 1) hs hs2
    simpa [DirichletCharacter.LFunction_modOne_eq] using this
  · rw [norm_div, norm_one]
    have h1 : s.re - 1 ≤ ‖s - 1‖ := by
      have := Complex.re_le_norm (s - 1)
      simpa using this
    exact one_div_le_one_div_of_le (by linarith) h1

/-- **The logarithmic derivative of `L₁`** on `1 - a/2 ≤ re s ≤ 1 + a/4`, `|im s| ≤ T`, where
`H = log (T + 4)` and `a = c / H`, from the zero-free region of `L₁`. -/
theorem logDeriv_zetaL1_rect {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (hz : ∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) ≤ s.re → zetaL1 s ≠ 0)
    {T H a : ℝ} (hT : 1 ≤ T) (hH : H = Real.log (T + 4)) (ha : a = c / H) :
    ∀ s : ℂ, 1 - a / 2 ≤ s.re → s.re ≤ 1 + a / 4 → |s.im| ≤ T →
      ‖deriv zetaL1 s / zetaL1 s‖ ≤ 1800 * H ^ 2 / c ^ 2 := by
  have hH1 : 1 < H := by
    have := one_lt_log_mul_add_four (q := 1) le_rfl (T := T) (by linarith)
    rw [hH]; simpa using this
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha2 : a ≤ 1 / 2 := by
    rw [ha, div_le_iff₀ (by linarith)]; linarith
  have hB := logDeriv_rect (F := zetaL1) differentiable_zetaL1 (a := a) (T := T) (M := 2 * H + 2)
    (A := 12 * H / c) ha0 ha2 (by linarith) (by positivity) ?_ ?_ ?_
  · intro s h1 h2 h3
    refine (hB s h1 h2 h3).trans ?_
    have key : (112 * (2 * H + 2) + 120 * (12 * H / c)) / (5 * a / 4) =
        4 * H * (112 * (2 * H + 2) * c + 1440 * H) / (5 * c ^ 2) := by
      rw [ha]; field_simp; ring
    rw [key, div_le_div_iff₀ (by positivity) (by positivity)]
    have h4 : 112 * (2 * H + 2) * c ≤ 224 * H := by
      have := mul_le_mul_of_nonneg_left hc2 (by linarith only [hH1] : (0 : ℝ) ≤ H)
      linarith only [this, hc2, hH1]
    have h5 : 4 * H * (112 * (2 * H + 2) * c + 1440 * H) ≤ 1800 * H ^ 2 * 5 := by
      have := mul_le_mul_of_nonneg_left h4 (by linarith only [hH1] : (0 : ℝ) ≤ 4 * H)
      linarith only [this, sq_nonneg H]
    linarith [mul_le_mul_of_nonneg_right h5 (sq_nonneg c)]
  · intro z hz1 hz2 hz3
    refine hz z ?_
    have hlog : Real.log (|z.im| + 3) ≤ H := by
      rw [hH]
      exact Real.log_le_log (by positivity) (by linarith)
    have hlogpos : 0 < Real.log (|z.im| + 3) := by
      have := log_mul_abs_add_three_gt_one (q := 1) le_rfl z.im
      simpa using (by linarith : (0 : ℝ) < Real.log (((1 : ℕ) : ℝ) * (|z.im| + 3)))
    have : a ≤ c / Real.log (|z.im| + 3) := by
      rw [ha]; exact div_le_div_of_nonneg_left hc.le hlogpos hlog
    linarith
  · intro z hz1 hz2 hz3
    have hre : (1 / 2 : ℝ) < z.re := by linarith
    have hnorm := norm_zetaL1_le (s := z) (by linarith)
    have hzn : ‖z‖ ≤ T + 3 := by
      have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_pos (by linarith : 0 < z.re)] at h1
      linarith
    have hzn1 : ‖z - 1‖ ≤ T + 4 := by
      have := norm_sub_le z 1
      simp at this
      linarith
    have h5 : ‖zetaL1 z‖ ≤ (T + 3) * (1 + 2 * (T + 4)) := by
      refine hnorm.trans ?_
      have hzn0 : 0 ≤ ‖z‖ := norm_nonneg _
      have e1 : ‖z‖ * ‖z - 1‖ / z.re ≤ (T + 3) * (T + 4) / (1 / 2) := by
        refine div_le_div₀ (by positivity) (mul_le_mul hzn hzn1 (norm_nonneg _) (by linarith))
          (by norm_num) hre.le
      linarith
    refine h5.trans ?_
    have hexp : Real.exp (2 * H + 2) = Real.exp 2 * (T + 4) ^ 2 := by
      have e1 : Real.exp H = T + 4 := by rw [hH, Real.exp_log (by positivity)]
      rw [Real.exp_add, show 2 * H = H + H by ring, Real.exp_add, e1]
      ring
    rw [hexp]
    have he : (3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ)
      linarith
    have := mul_le_mul_of_nonneg_right he (sq_nonneg (T + 4))
    linarith only [this, sq_nonneg T, hT]
  · intro t ht
    set z₀ : ℂ := ((1 + a / 4 : ℝ) : ℂ) + t * I with hz₀
    have hre : 1 < z₀.re := by simp [hz₀]; linarith
    have hre' : z₀.re = 1 + a / 4 := by simp [hz₀]
    have hw : z₀ - 1 = ((a / 4 : ℝ) : ℂ) + t * I := by
      apply Complex.ext <;> simp [hz₀]
    have hw0 : z₀ - 1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp [hz₀] at this
      linarith
    have hz1 : z₀ ≠ 1 := fun h => hw0 (by rw [h]; ring)
    refine ⟨Complex.log (z₀ - 1) + LSeries (fun n : ℕ => (Λ n : ℂ) / (Real.log n : ℂ)) z₀, ?_, ?_⟩
    · rw [Complex.exp_add, Complex.exp_log hw0, riemannZeta_eq_exp_LSeries hre, zetaL1_apply hz1]
    · refine (norm_add_le _ _).trans ?_
      have hE := norm_eulerLog_zeta_le hre
      rw [hre'] at hE
      have e : (1 + a / 4) / (1 + a / 4 - 1) + 1 = 4 / a + 2 := by
        have h14 : 1 + a / 4 - 1 = a / 4 := by ring
        rw [h14]; field_simp; ring
      rw [e] at hE
      have hlog := norm_log_le_aux (z₀ - 1)
      -- `|log ‖w‖| ≤ H + 4/a`
      have hwre : (z₀ - 1).re = a / 4 := by simp [hz₀]
      have hwim : (z₀ - 1).im = t := by simp [hz₀]
      have hwlow : a / 4 ≤ ‖z₀ - 1‖ := by
        have := Complex.re_le_norm (z₀ - 1)
        rwa [hwre] at this
      have hwup : ‖z₀ - 1‖ ≤ T + 4 := by
        have := Complex.norm_le_abs_re_add_abs_im (z₀ - 1)
        rw [hwre, hwim, abs_of_pos (by linarith : 0 < a / 4)] at this
        linarith [(abs_le.mp ht).2]
      have hwpos : 0 < ‖z₀ - 1‖ := norm_pos_iff.mpr hw0
      have hlogw : |Real.log ‖z₀ - 1‖| ≤ H + 4 / a := by
        have h4a : 0 ≤ 4 / a := by positivity
        by_cases h1 : 1 ≤ ‖z₀ - 1‖
        · rw [abs_of_nonneg (Real.log_nonneg h1)]
          have : Real.log ‖z₀ - 1‖ ≤ H := by
            rw [hH]; exact Real.log_le_log hwpos hwup
          linarith
        · push Not at h1
          rw [abs_of_neg (Real.log_neg hwpos h1)]
          have h2 : Real.log (a / 4) ≤ Real.log ‖z₀ - 1‖ := Real.log_le_log (by positivity) hwlow
          have h3 : Real.log (4 / a) ≤ 4 / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
          have h4 : Real.log (4 / a) = -Real.log (a / 4) := by
            rw [← Real.log_inv, inv_div]
          linarith
      have hHpos : 0 < H := by linarith
      have h8 : 8 / a = 8 * H / c := by rw [ha]; field_simp
      have h4a : 4 / a = 4 * H / c := by rw [ha]; field_simp
      have hbig : H + 6 ≤ 4 * H / c := by
        rw [le_div_iff₀ hc]
        have := mul_le_mul_of_nonneg_left hc2 (by linarith only [hH1] : (0 : ℝ) ≤ H + 6)
        linarith only [this, hH1]
      have hfin : 4 * H / c + (4 * H / c) + 4 + 2 + H ≤ 12 * H / c := by
        have : 12 * H / c = 8 * H / c + 4 * H / c := by ring
        have h8' : 8 * H / c = 4 * H / c + 4 * H / c := by ring
        linarith
      linarith

end PrimeCarleson.Proof.Fplus31.PNTSW

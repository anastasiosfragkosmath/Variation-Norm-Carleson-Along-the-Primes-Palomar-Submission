module

public import PrimeCarleson.Proof.Fplus31.PNT.Budget

/-!
# The exponent budget of the truncated Perron integral

Part of the prime number theorem in progressions on the classical zero-free region
(`PNTSW/Main.lean`). With `u = √(log y)`, the height `T = exp u`, `H = log (q (T + 4))` with
`u ≤ H ≤ 4u` (this is `log q ≤ u`) and `a = c / H`, the two terms of `PNTSW.Rect.perron_rect_bound`
are `y^{(1 - a/2) + 1}` and `y^{(1 + a/4) + 1} / T`:

* `budget_bound`: `2 B y^{(1-a/2)+1} + B y^{(1+a/4)+1}/e^u ≤ 3 K u²c⁻² y² e^{-cu/8}`
  for `0 ≤ B ≤ K u² / c²`;
* `log_mul_add_four_le`, `le_log_mul_add_four`: `u ≤ log (q (e^u + 4)) ≤ 4 u` for `log q ≤ u`,
  `u ≥ 2`.
-/

@[expose] public noncomputable section

open Filter

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.PNTSW

/-- `y^{2+x} = y² exp (x log y)` for `y > 0`. -/
theorem rpow_eq_sq_mul_exp {y : ℝ} (hy : 0 < y) (x : ℝ) :
    y ^ (2 + x) = y ^ 2 * Real.exp (x * Real.log y) := by
  rw [Real.rpow_add hy, Real.rpow_two, Real.rpow_def_of_pos hy x, mul_comm (Real.log y) x]

/-- `u ≤ log (q (e^u + 4))` for `q ≥ 1`. -/
theorem le_log_mul_add_four {q : ℕ} (hq : 1 ≤ q) (u : ℝ) :
    u ≤ Real.log (q * (Real.exp u + 4)) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h : Real.exp u ≤ q * (Real.exp u + 4) := by
    have := Real.exp_pos u
    nlinarith
  calc u = Real.log (Real.exp u) := (Real.log_exp u).symm
    _ ≤ _ := Real.log_le_log (Real.exp_pos u) h

/-- `log (q (e^u + 4)) ≤ 4 u` if `log q ≤ u` and `u ≥ 2`. -/
theorem log_mul_add_four_le {q : ℕ} (hq : 1 ≤ q) {u : ℝ} (hu : 2 ≤ u) (hqu : Real.log q ≤ u) :
    Real.log (q * (Real.exp u + 4)) ≤ 4 * u := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have he : (0 : ℝ) < Real.exp u := Real.exp_pos u
  rw [Real.log_mul hq'.ne' (by positivity)]
  have h1 : Real.exp u + 4 ≤ 5 * Real.exp u := by
    have : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp (by linarith)
    linarith
  have h2 : Real.log (Real.exp u + 4) ≤ Real.log (5 * Real.exp u) :=
    Real.log_le_log (by positivity) h1
  rw [Real.log_mul (by norm_num) he.ne', Real.log_exp] at h2
  have h3 : Real.log 5 ≤ 4 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
    linarith
  linarith

/-- The two terms of the truncated Perron integral are at most `3 K u² c⁻² y² exp (-c u / 8)`. -/
theorem budget_bound {c u H a y B K : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) (hy : 1 ≤ y) (hu : 2 ≤ u)
    (hlog : Real.log y = u ^ 2) (hH1 : u ≤ H) (hH2 : H ≤ 4 * u) (ha : a = c / H) (hB0 : 0 ≤ B)
    (hB : B ≤ K * u ^ 2 / c ^ 2) :
    2 * B * y ^ ((1 - a / 2) + 1) + B * y ^ ((1 + a / 4) + 1) / Real.exp u ≤
      3 * (K * u ^ 2 / c ^ 2) * y ^ 2 * Real.exp (-(c * u / 8)) := by
  have hy0 : 0 < y := by linarith
  have hu0 : 0 < u := by linarith
  have hH0 : 0 < H := by linarith
  have ha0 : 0 < a := by rw [ha]; positivity
  have h1 : (1 - a / 2) + 1 = 2 + (-(a / 2)) := by ring
  have h2 : (1 + a / 4) + 1 = 2 + a / 4 := by ring
  rw [h1, h2, rpow_eq_sq_mul_exp hy0, rpow_eq_sq_mul_exp hy0, hlog]
  -- `a u² / 2 ≥ c u / 8` and `a u² / 4 ≤ c u / 4`
  have ha4 : c / (4 * u) ≤ a := by rw [ha]; exact div_le_div_of_nonneg_left hc.le hH0 hH2
  have ha1 : a ≤ c / u := by rw [ha]; exact div_le_div_of_nonneg_left hc.le hu0 hH1
  have hlow : c * u / 8 ≤ a * u ^ 2 / 2 := by
    calc c * u / 8 = c / (4 * u) * u ^ 2 / 2 := by field_simp; ring
      _ ≤ a * u ^ 2 / 2 := by gcongr
  have hup : a * u ^ 2 / 4 ≤ c * u / 4 := by
    calc a * u ^ 2 / 4 ≤ c / u * u ^ 2 / 4 := by gcongr
      _ = c * u / 4 := by field_simp
  have e1 : Real.exp (-(a / 2) * u ^ 2) ≤ Real.exp (-(c * u / 8)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have e2 : Real.exp (a / 4 * u ^ 2) / Real.exp u ≤ Real.exp (-(c * u / 8)) := by
    rw [← Real.exp_sub]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hy2 : 0 ≤ y ^ 2 := by positivity
  have hB' : 0 ≤ K * u ^ 2 / c ^ 2 := hB0.trans hB
  calc 2 * B * (y ^ 2 * Real.exp (-(a / 2) * u ^ 2)) +
        B * (y ^ 2 * Real.exp (a / 4 * u ^ 2)) / Real.exp u
      = 2 * B * y ^ 2 * Real.exp (-(a / 2) * u ^ 2) +
        B * y ^ 2 * (Real.exp (a / 4 * u ^ 2) / Real.exp u) := by ring
    _ ≤ 2 * B * y ^ 2 * Real.exp (-(c * u / 8)) + B * y ^ 2 * Real.exp (-(c * u / 8)) := by
        gcongr
    _ = 3 * B * y ^ 2 * Real.exp (-(c * u / 8)) := by ring
    _ ≤ 3 * (K * u ^ 2 / c ^ 2) * y ^ 2 * Real.exp (-(c * u / 8)) := by
        gcongr

end PrimeCarleson.Proof.Fplus31.PNTSW

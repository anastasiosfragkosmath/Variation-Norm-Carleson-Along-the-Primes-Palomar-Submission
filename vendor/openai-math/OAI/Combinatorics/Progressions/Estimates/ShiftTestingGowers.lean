/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/ShiftTestingGowers.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.CorrelationDerivative
public import OAI.Combinatorics.Progressions.Estimates.FixedPartnerPower
public import OAI.Combinatorics.Progressions.Linear.BalancedDualBounds
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {H Ω : Type*} [Fintype H] [Fintype Ω]

theorem square_norm_mean_eq_cross_re (v : H → ℂ) :
    ‖𝔼 h, v h‖ ^ 2 = (𝔼 h, 𝔼 k, v h * star (v k)).re := by
  rw [← Fintype.expect_mul_expect, expect_star, mul_star_re_eq_norm_sq]

theorem mean_square_family_le_cross_norm (v : H → Ω → ℂ) :
    (𝔼 x, ‖𝔼 h, v h x‖ ^ 2) ≤ 𝔼 h, 𝔼 k, ‖𝔼 x, v h x * star (v k x)‖ := by
  simp_rw [square_norm_mean_eq_cross_re]
  rw [← expect_re, Finset.expect_comm]
  have hid (h : H) :
      (𝔼 x, 𝔼 k, v h x * star (v k x)) = 𝔼 k, 𝔼 x, v h x * star (v k x) :=
    Finset.expect_comm _ _ _
  simp_rw [hid, expect_re]
  apply Finset.expect_le_expect
  intro h _
  apply Finset.expect_le_expect
  intro k _
  rw [← expect_re]
  exact Complex.re_le_norm _

theorem finite_family_cauchy_schwarz [Nonempty Ω]
    (B : Ω → ℂ) (v : H → Ω → ℂ) {M : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) :
    ‖𝔼 x, B x * (𝔼 h, v h x)‖ ^ 2 ≤
      M ^ 2 * (𝔼 h, 𝔼 k, ‖𝔼 x, v h x * star (v k x)‖) := by
  have hcs := norm_expect_mul_star_sq_le B (fun x => star (𝔼 h, v h x))
  simp only [star_star, norm_star] at hcs
  have hBM : (𝔼 x, ‖B x‖ ^ 2) ≤ M ^ 2 :=
    (Finset.expect_le_expect (fun x _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hB x) 2)).trans_eq (Fintype.expect_const _)
  exact hcs.trans ((mul_le_mul_of_nonneg_right hBM
    (Finset.expect_nonneg (fun x _ => sq_nonneg _))).trans
      (mul_le_mul_of_nonneg_left (mean_square_family_le_cross_norm v) (sq_nonneg M)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem shift_phase_average (v B : G → ℂ) (L : G → G → ℂ) (a : G → ℂ)
    (ha : ∀ h, a h * (𝔼 x, v x * (B (x + h) * L h x)) =
      (‖𝔼 x, v x * (B (x + h) * L h x)‖ : ℂ)) :
    (𝔼 y, B y * (𝔼 h, a h * v (y - h) * L h (y - h))) =
      ((𝔼 h, ‖𝔼 x, v x * (B (x + h) * L h x)‖) : ℝ) := by
  have hmove (h : G) :
      a h * (𝔼 x, v x * (B (x + h) * L h x)) =
        𝔼 y, B y * (a h * v (y - h) * L h (y - h)) := by
    rw [Finset.mul_expect]
    apply Fintype.expect_equiv (Equiv.addRight h)
    intro x
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    ring
  calc
    _ = 𝔼 h, 𝔼 y, B y * (a h * v (y - h) * L h (y - h)) := by
      simp_rw [Finset.mul_expect]
      rw [Finset.expect_comm]
    _ = 𝔼 h, a h * (𝔼 x, v x * (B (x + h) * L h x)) := by simp_rw [← hmove]
    _ = _ := by simp_rw [ha]; simp [Fintype.expect_eq_sum_div_card]

theorem shift_phase_cross_norm (v : G → ℂ) (L : G → G → ℂ) (a : G → ℂ)
    (ha : ∀ h, ‖a h‖ = 1) (h k : G) :
    ‖𝔼 y, (a h * v (y - h) * L h (y - h)) *
      star (a k * v (y - k) * L k (y - k))‖ =
    ‖𝔼 x, v x * star (v (x + h - k)) * L h x * star (L k (x + h - k))‖ := by
  have hid : (a h * star (a k)) *
      (𝔼 x, v x * star (v (x + h - k)) * L h x * star (L k (x + h - k))) =
      𝔼 y, (a h * v (y - h) * L h (y - h)) *
        star (a k * v (y - k) * L k (y - k)) := by
    rw [Finset.mul_expect]
    apply Fintype.expect_equiv (Equiv.addRight h)
    intro x
    simp only [Equiv.coe_addRight, add_sub_cancel_right, star_mul]
    ring
  rw [← hid, norm_mul, norm_mul, norm_star, ha, ha, one_mul, one_mul]

theorem shifted_test_cauchy_schwarz (v B : G → ℂ) (L : G → G → ℂ)
    {M : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) :
    (𝔼 h, ‖𝔼 x, v x * (B (x + h) * L h x)‖) ^ 2 ≤
      M ^ 2 * (𝔼 h, 𝔼 k,
        ‖𝔼 x, v x * star (v (x + h - k)) * L h x * star (L k (x + h - k))‖) := by
  have hex (h : G) := exists_complex_unit_phase (𝔼 x, v x * (B (x + h) * L h x))
  choose a ha hphase using hex
  have hcs := finite_family_cauchy_schwarz B
    (fun h y => a h * v (y - h) * L h (y - h)) hB
  rw [shift_phase_average v B L a hphase, Complex.norm_real,
    Real.norm_of_nonneg (Finset.expect_nonneg (fun h _ => norm_nonneg _))] at hcs
  simpa only [shift_phase_cross_norm v L a ha] using hcs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_absolute_cauchy_schwarz {H Ω : Type*} [Fintype H] [Fintype Ω]
    [Nonempty Ω] (B : Ω → ℂ) (v : H → Ω → ℂ) {M : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) :
    (𝔼 h, ‖𝔼 x, B x * v h x‖) ^ 2 ≤
      M ^ 2 * (𝔼 h, 𝔼 k, ‖𝔼 x, v h x * star (v k x)‖) := by
  choose a ha hphase using fun h => exists_complex_unit_phase (𝔼 x, B x * v h x)
  have havg : (𝔼 x, B x * (𝔼 h, a h * v h x)) =
      ((𝔼 h, ‖𝔼 x, B x * v h x‖) : ℝ) := by
    calc
      _ = 𝔼 h, a h * (𝔼 x, B x * v h x) := by
        simp_rw [Finset.mul_expect]
        rw [Finset.expect_comm]
        apply Finset.expect_congr rfl
        intro h _
        apply Finset.expect_congr rfl
        intro x _
        ring
      _ = _ := by simp_rw [hphase]; simp [Fintype.expect_eq_sum_div_card]
  have hcross (h k : H) :
      ‖𝔼 x, (a h * v h x) * star (a k * v k x)‖ =
        ‖𝔼 x, v h x * star (v k x)‖ := by
    have hid : (𝔼 x, (a h * v h x) * star (a k * v k x)) =
        (a h * star (a k)) * (𝔼 x, v h x * star (v k x)) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      simp only [star_mul]
      ring
    rw [hid, norm_mul, norm_mul, norm_star, ha, ha, one_mul, one_mul]
  have hcs := finite_family_cauchy_schwarz B (fun h x => a h * v h x) hB
  rw [havg, Complex.norm_real,
    Real.norm_of_nonneg (Finset.expect_nonneg (fun h _ => norm_nonneg _))] at hcs
  simpa only [hcross] using hcs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G ι : Type*} [AddCommGroup G] [Fintype G] [Nonempty ι]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G ι : Type*} [AddCommGroup G] [Fintype G]

end Erdos3

end

end OAI

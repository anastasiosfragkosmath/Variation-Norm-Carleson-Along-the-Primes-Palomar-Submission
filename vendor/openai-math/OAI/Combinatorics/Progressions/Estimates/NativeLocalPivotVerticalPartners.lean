/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/NativeLocalPivotVerticalPartners.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest
public import OAI.Combinatorics.Progressions.Nilpotent.NiltestVerticalBounds
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exp_scaled_norm_le_one {b : ℝ} {z : ℂ} (hz : ‖z‖ ≤ Real.exp b) :
    ‖(Real.exp (-b) : ℂ) * z‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-b) * Real.exp b := mul_le_mul_of_nonneg_left hz (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

theorem finite_double_normalization {X : Type*} (S : Finset X) (f g : X → ℂ) (b : ℝ)
    (hcorr : Real.exp (-b) ≤ ‖𝔼 x ∈ S, f x * g x‖) :
    Real.exp (-(3 * b)) ≤ ‖𝔼 x ∈ S,
      ((Real.exp (-b) : ℂ) * f x) * ((Real.exp (-b) : ℂ) * g x)‖ := by
  have hmean : (𝔼 x ∈ S, ((Real.exp (-b) : ℂ) * f x) * ((Real.exp (-b) : ℂ) * g x)) =
      ((Real.exp (-b) : ℂ) * (Real.exp (-b) : ℂ)) * (𝔼 x ∈ S, f x * g x) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    ring
  rw [hmean, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-(3 * b)) = (Real.exp (-b) * Real.exp (-b)) * Real.exp (-b) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcorr (by positivity)

theorem finite_remove_normalization {X : Type*} (S : Finset X) (f g : X → ℂ)
    {b rho : ℝ} (hb : 0 ≤ b)
    (hcorr : rho ≤ ‖𝔼 x ∈ S, ((Real.exp (-b) : ℂ) * f x) * g x‖) :
    rho ≤ ‖𝔼 x ∈ S, f x * g x‖ := by
  have hmean : (𝔼 x ∈ S, ((Real.exp (-b) : ℂ) * f x) * g x) =
      (Real.exp (-b) : ℂ) * (𝔼 x ∈ S, f x * g x) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    ring
  rw [hmean, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] at hcorr
  exact hcorr.trans (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hb)))

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

end Erdos3

end

end OAI

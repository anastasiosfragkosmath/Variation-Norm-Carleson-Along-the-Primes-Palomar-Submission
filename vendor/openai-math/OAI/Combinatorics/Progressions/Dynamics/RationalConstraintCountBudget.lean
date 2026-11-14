/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Dynamics/RationalConstraintCountBudget.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.BoundedSubmoduleIntersection
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module

theorem rational_height_count_le_cube (H : ℕ) : (2 * H + 1) * (H + 1) ≤ (H + 1) ^ 3 := by
  have h : 2 * H + 1 ≤ (H + 1) ^ 2 := by nlinarith
  calc
    _ ≤ (H + 1) ^ 2 * (H + 1) := Nat.mul_le_mul_right _ h
    _ = _ := by ring

theorem rational_height_count_exp_bound (H N : ℕ) {A : ℝ}
    (hA : 0 ≤ A) (hH : (H : ℝ) ≤ Real.exp A) :
    ((((2 * H + 1) * (H + 1)) ^ N : ℕ) : ℝ) ≤ Real.exp (3 * N * (A + 1)) := by
  have h1 : 1 ≤ Real.exp A := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hA
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hH1 : (H : ℝ) + 1 ≤ Real.exp (A + 1) := by
    calc
      _ ≤ Real.exp A + Real.exp A := add_le_add hH h1
      _ = 2 * Real.exp A := by ring
      _ ≤ Real.exp 1 * Real.exp A := mul_le_mul_of_nonneg_right htwo (Real.exp_pos A).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hcount : (((2 * H + 1) * (H + 1) : ℕ) : ℝ) ≤ Real.exp (3 * (A + 1)) := by
    calc
      _ ≤ ((H + 1 : ℕ) : ℝ) ^ 3 := by exact_mod_cast rational_height_count_le_cube H
      _ ≤ Real.exp (A + 1) ^ 3 := by
        apply pow_le_pow_left₀ (by positivity)
        simpa only [Nat.cast_add, Nat.cast_one] using hH1
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  rw [Nat.cast_pow]
  calc
    _ ≤ Real.exp (3 * (A + 1)) ^ N := pow_le_pow_left₀ (by positivity) hcount N
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem rational_log_height_count_exp_bound (N : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ((((2 * ⌈Real.exp A⌉₊ + 1) * (⌈Real.exp A⌉₊ + 1)) ^ N : ℕ) : ℝ) ≤
      Real.exp (3 * N * (A + 2)) := by
  have he := rational_height_count_exp_bound ⌈Real.exp A⌉₊ N
    (A := A + 1) (by linarith) (ceil_exp_le_exp_add_one hA)
  convert he using 1
  congr 1
  ring

theorem heightBoundedLieSubalgebras_ncard_exp_bound
    {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (e : Basis ι ℚ L) (m : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ((heightBoundedLieSubalgebras e m ⌈Real.exp A⌉₊).ncard : ℝ) ≤
      Real.exp (3 * (m : ℝ) * Fintype.card ι * (A + 2)) := by
  have hc := (finite_card_heightBoundedLieSubalgebras e m ⌈Real.exp A⌉₊).2
  have he := rational_log_height_count_exp_bound (m * Fintype.card ι) hA
  have hr := (Nat.cast_le.mpr hc).trans he
  simpa only [Nat.cast_mul, mul_assoc] using hr

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Geometry/BoxDetectionExponents.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget
@[expose] public section

namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem exp_sub_one_le_half_exp (x : ℝ) : Real.exp (x - 1) ≤ Real.exp x / 2 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  calc
    _ ≤ Real.exp (x - 1) * Real.exp 1 := mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem two_pow_le_exp_of_le (d : ℕ) {p : ℝ} (hd : (d : ℝ) ≤ p) :
    (2 : ℝ) ^ d ≤ Real.exp p := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ (Real.exp 1) ^ d := pow_le_pow_left₀ (by norm_num) htwo d
    _ = Real.exp d := by rw [← Real.exp_nat_mul, mul_one]
    _ ≤ _ := Real.exp_le_exp.mpr hd

theorem retained_exponential_weight (d : ℕ) {p r : ℝ} (hd : (d : ℝ) ≤ p) :
    let L := 2 * r + 2 * p + 6
    Real.exp (-L) ≤ Real.exp (-r) ^ 2 / (2 * Real.exp (p + 1) ^ 2) -
      (2 : ℝ) ^ d * Real.exp (-(L + p)) := by
  let L := 2 * r + 2 * p + 6
  have hloss : (2 : ℝ) ^ d * Real.exp (-(L + p)) ≤ Real.exp (-L) := by
    calc
      _ ≤ Real.exp p * Real.exp (-(L + p)) :=
        mul_le_mul_of_nonneg_right (two_pow_le_exp_of_le d hd) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have he : Real.exp (-r) ^ 2 / (2 * Real.exp (p + 1) ^ 2) =
      Real.exp 4 / 2 * Real.exp (-L) := by
    calc
      _ = (Real.exp (-r) ^ 2 / Real.exp (p + 1) ^ 2) / 2 := by ring
      _ = Real.exp (2 * (-r) - 2 * (p + 1)) / 2 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_sub]
        norm_num
      _ = (Real.exp 4 * Real.exp (-L)) / 2 := by
        rw [← Real.exp_add]
        congr 2
        dsimp [L]
        ring
      _ = _ := by ring
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  change Real.exp (-L) ≤ _
  rw [he]
  nlinarith [Real.exp_pos (-L)]

theorem exp_neg_le_of_pow {x P : ℝ} {n : ℕ} (hx : 0 ≤ x) (hP : 0 ≤ P) (hn : n ≠ 0)
    (h : Real.exp (-P) ≤ x ^ n) : Real.exp (-P) ≤ x := by
  have ht : Real.exp (-P) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hp : ∀ k : ℕ, Real.exp (-P) ^ (k + 1) ≤ Real.exp (-P) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      exact (mul_le_mul ih ht (Real.exp_nonneg _) (Real.exp_nonneg _)).trans_eq (mul_one _)
  cases n with
  | zero => exact False.elim (hn rfl)
  | succ k => exact le_of_pow_le_pow_left₀ (Nat.succ_ne_zero k) hx ((hp k).trans h)

end Erdos3

end

end OAI

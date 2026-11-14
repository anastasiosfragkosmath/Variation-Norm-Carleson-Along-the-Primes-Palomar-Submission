/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/RationalKernelBudget.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Dynamics.RationalHeightBudget
public import OAI.Combinatorics.Progressions.Estimates.RationalSubspaces
@[expose] public section

namespace OAI

section

namespace Erdos3

theorem rationalKernelHeight_le_budget (r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hr : (r : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (rationalKernelHeight r H : ℝ) ≤ Real.exp ((p + 2) ^ 7) := by
  have hsolve := rationalSolveHeight_le_budget r H hp hr hH
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfront : (2 : ℝ) * (r + 1) ≤ Real.exp (1 + (r : ℝ)) := by
    rw [Real.exp_add]
    exact mul_le_mul htwo (Real.add_one_le_exp r) (by positivity) (by positivity)
  have hbase : (rationalSolveHeight r H : ℝ) * H ≤
      Real.exp ((p + 2) ^ 5 + p) := by
    rw [Real.exp_add]
    exact mul_le_mul hsolve hH (Nat.cast_nonneg _) (by positivity)
  have hpower := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    hbase r
  rw [← Real.exp_nat_mul] at hpower
  have hbound : (rationalKernelHeight r H : ℝ) ≤
      Real.exp (1 + (r : ℝ) + (r : ℝ) * ((p + 2) ^ 5 + p)) := by
    unfold rationalKernelHeight
    push_cast
    rw [Real.exp_add]
    exact mul_le_mul hfront hpower (by positivity) (by positivity)
  apply hbound.trans
  apply Real.exp_le_exp.mpr
  calc
    1 + (r : ℝ) + (r : ℝ) * ((p + 2) ^ 5 + p) ≤
        1 + p + p * ((p + 2) ^ 5 + p) := by gcongr
    _ ≤ (p + 2) ^ 7 := by
      have h : 0 ≤ p ^ 7 + 13 * p ^ 6 + 74 * p ^ 5 + 240 * p ^ 4 +
          480 * p ^ 3 + 591 * p ^ 2 + 415 * p + 127 := by positivity
      nlinarith

end Erdos3

end

end OAI

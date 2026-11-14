/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Dynamics/FiniteProductBudget.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sigma_card_le_budget {α : Type*} [Fintype α] {κ : α → Type*}
    [∀ a, Fintype (κ a)] {p : ℝ} (hp : 0 ≤ p)
    (hα : (Fintype.card α : ℝ) ≤ p) (hκ : ∀ a, (Fintype.card (κ a) : ℝ) ≤ p) :
    (Fintype.card (Σ a, κ a) : ℝ) ≤ p ^ 2 := by
  classical
  calc
    _ = ∑ a, (Fintype.card (κ a) : ℝ) := by rw [Fintype.card_sigma, Nat.cast_sum]
    _ ≤ ∑ _a : α, p := Finset.sum_le_sum (fun a _ => hκ a)
    _ = (Fintype.card α : ℝ) * p := by simp
    _ ≤ p * p := mul_le_mul_of_nonneg_right hα hp
    _ = p ^ 2 := by ring

theorem product_denominator_le_budget {α : Type*} [Fintype α] (m : α → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hα : (Fintype.card α : ℝ) ≤ p)
    (hm : ∀ a, (m a : ℝ) ≤ Real.exp p) :
    ((∏ a, m a : ℕ) : ℝ) ≤ Real.exp (p ^ 2) := by
  classical
  rw [Nat.cast_prod]
  calc
    _ ≤ ∏ _a : α, Real.exp p := Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun index _ => hm index)
    _ = Real.exp ((Fintype.card α : ℝ) * p) := by rw [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul]
    _ ≤ Real.exp (p ^ 2) := Real.exp_le_exp.mpr (by nlinarith)

end Erdos3

end

end OAI

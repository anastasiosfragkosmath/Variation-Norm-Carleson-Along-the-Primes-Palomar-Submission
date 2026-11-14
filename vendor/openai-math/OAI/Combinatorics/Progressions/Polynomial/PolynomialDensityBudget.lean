/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialDensityBudget.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib
@[expose] public section

namespace OAI

section

namespace Erdos3

theorem exists_natPolynomial_eval_budget (P : Polynomial ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ p : ℝ, 0 ≤ p →
      P.eval₂ (Nat.castRingHom ℝ) p ≤ (p + N) ^ N := by
  let N := P.eval 1 + P.natDegree + 2
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro p hp
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by dsimp [N]; omega)
  have ht : 1 ≤ p + N := by linarith
  have hcoeff : ((P.eval 1 : ℕ) : ℝ) ≤ p + N := by
    have h : P.eval 1 ≤ N := by dsimp [N]; omega
    exact (Nat.cast_le.mpr h).trans (le_add_of_nonneg_left hp)
  have hsum : (∑ n ∈ P.support, (P.coeff n : ℝ)) = ((P.eval 1 : ℕ) : ℝ) := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    simp only [one_pow, mul_one, Nat.cast_sum]
  calc
    P.eval₂ (Nat.castRingHom ℝ) p = ∑ n ∈ P.support, (P.coeff n : ℝ) * p ^ n := by
      rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
      rfl
    _ ≤ ∑ n ∈ P.support, (P.coeff n : ℝ) * (p + N) ^ P.natDegree := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply (pow_le_pow_left₀ hp (le_add_of_nonneg_right (Nat.cast_nonneg N)) n).trans
      exact pow_le_pow_right₀ ht (Polynomial.le_natDegree_of_mem_supp n hn)
    _ = ((P.eval 1 : ℕ) : ℝ) * (p + N) ^ P.natDegree := by rw [← Finset.sum_mul, hsum]
    _ ≤ (p + N) * (p + N) ^ P.natDegree :=
      mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (by linarith) _)
    _ = (p + N) ^ (P.natDegree + 1) := (pow_succ' _ _).symm
    _ ≤ (p + N) ^ N := pow_le_pow_right₀ ht (by dsimp [N]; omega)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

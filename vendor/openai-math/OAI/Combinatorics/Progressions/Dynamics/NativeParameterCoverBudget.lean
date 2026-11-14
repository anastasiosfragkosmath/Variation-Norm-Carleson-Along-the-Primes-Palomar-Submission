/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Dynamics/NativeParameterCoverBudget.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Nilpotent.BCHSmoothPartitionBudget
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem boxCoverCount_dimension_bound (d : ℕ) (K : ℝ≥0) {B ε p : ℝ}
    (hB0 : 0 ≤ B) (hε : 0 < ε) (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p)
    (hB : B ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p) (hinv : 1 / ε ≤ Real.exp p) :
    (((boxCoverMeshCount B K ε + 1) ^ d : ℕ) : ℝ) ≤ Real.exp (p * (3 * p + 4)) := by
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (3 * p + 4)) ^ d :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (boxCoverMeshCount_add_one_le_exp K hB0 hε hp hB hK hinv) d
    _ = Real.exp ((d : ℝ) * (3 * p + 4)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hd (by positivity))

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_bchBoxCover_count_budget (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d H : ℕ) (B : ℝ≥0) {p ε : ℝ},
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (B : ℝ) ≤ Real.exp ((p + 2) ^ r) → 0 < ε → 1 / ε ≤ Real.exp p →
      (((boxCoverMeshCount B (bchBoxMetricConstant s d H B) ε + 1) ^ d : ℕ) : ℝ) ≤
        Real.exp ((p + C) ^ C) := by
  obtain ⟨A, _, hmetric⟩ := exists_bchBoxMetricConstant_exp_bound s r
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + 2) ^ r + (X + Polynomial.C A) ^ A
  let P := R * (3 * R + 4)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro d H B p ε hp hd hH hB hε hεinv
  let q := p + (p + 2) ^ r + (p + A) ^ A
  have hr : 0 ≤ (p + 2) ^ r := pow_nonneg (by linarith) _
  have hA : 0 ≤ (p + A) ^ A := pow_nonneg (add_nonneg hp (Nat.cast_nonneg A)) _
  have hpq : p ≤ q := (le_add_of_nonneg_right hr).trans (le_add_of_nonneg_right hA)
  have hrq : (p + 2) ^ r ≤ q := (le_add_of_nonneg_left hp).trans (le_add_of_nonneg_right hA)
  have hAq : (p + A) ^ A ≤ q := le_add_of_nonneg_left (add_nonneg hp hr)
  have hsize := boxCoverCount_dimension_bound d (bchBoxMetricConstant s d H B) B.coe_nonneg hε
    (hp.trans hpq) (hd.trans hpq) (hB.trans (Real.exp_le_exp.mpr hrq))
    ((hmetric d H B p hp hd hH hB).trans (Real.exp_le_exp.mpr hAq))
    (hεinv.trans (Real.exp_le_exp.mpr hpq))
  have hfinal : q * (3 * q + 4) ≤ (p + C) ^ C := by
    simpa [P, R, X, q, Polynomial.eval₂_pow] using hbudget p hp
  exact hsize.trans (Real.exp_le_exp.mpr hfinal)

end Erdos3

end

end OAI

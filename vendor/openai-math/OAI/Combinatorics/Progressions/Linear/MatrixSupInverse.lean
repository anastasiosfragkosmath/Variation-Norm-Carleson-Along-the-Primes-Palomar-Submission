/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/MatrixSupInverse.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_det_abs_le_row_bounds (A : Matrix ι ι ℝ) (H : ι → ℝ)
    (hA : ∀ i j, |A i j| ≤ H i) :
    |A.det| ≤ (Fintype.card ι).factorial * ∏ i, H i := by
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, ∏ i, H i := by
      apply Finset.sum_le_sum
      intro σ _
      have hsign : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
        rw [← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one]
      rw [abs_mul, hsign, one_mul, Finset.abs_prod]
      calc
        _ ≤ ∏ i, H (σ i) :=
          Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hA (σ i) i)
        _ = ∏ i, H i := Equiv.prod_comp σ H
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

theorem matrix_adjugate_entry_abs_le (A : Matrix ι ι ℝ) {H : ℝ}
    (hA : ∀ i j, |A i j| ≤ H) (i j : ι) :
    |A.adjugate i j| ≤ (Fintype.card ι).factorial * H ^ (Fintype.card ι - 1) := by
  rw [Matrix.adjugate_apply]
  let K : ι → ℝ := fun k => if k = j then 1 else H
  have hentry : ∀ k l, |(A.updateRow j (Pi.single i 1)) k l| ≤ K k := by
    intro k l
    by_cases hk : k = j
    · subst k
      simp only [Matrix.updateRow_self, K, ite_true, Pi.single_apply]
      split_ifs <;> norm_num
    · simpa only [Matrix.updateRow_ne hk, K, hk, ite_false] using hA k l
  have hprod : (∏ k, K k) = H ^ (Fintype.card ι - 1) := by
    rw [← Finset.mul_prod_erase Finset.univ K (Finset.mem_univ j)]
    have hj : K j = 1 := by simp [K]
    rw [hj, one_mul]
    calc
      (∏ k ∈ Finset.univ.erase j, K k) = ∏ _k ∈ Finset.univ.erase j, H := by
        apply Finset.prod_congr rfl
        intro k hk
        simp only [K, Finset.ne_of_mem_erase hk, ite_false]
      _ = _ := by simp
  simpa only [hprod] using matrix_det_abs_le_row_bounds _ K hentry

theorem matrix_inverse_entry_abs_le (A : Matrix ι ι ℝ) {H κ : ℝ}
    (hA : ∀ i j, |A i j| ≤ H) (hκ : 0 < κ) (hdet : κ ≤ |A.det|)
    (i j : ι) :
    |A⁻¹ i j| ≤ ((Fintype.card ι).factorial * H ^ (Fintype.card ι - 1)) / κ := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_inv]
  have hcof := matrix_adjugate_entry_abs_le A hA i j
  have hinv : |A.det|⁻¹ ≤ κ⁻¹ := inv_anti₀ hκ hdet
  calc
    _ ≤ κ⁻¹ * ((Fintype.card ι).factorial * H ^ (Fintype.card ι - 1)) :=
      mul_le_mul hinv hcof (abs_nonneg _) (inv_nonneg.mpr hκ.le)
    _ = _ := by rw [div_eq_mul_inv]; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Geometry/BoxBlockBudget.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.ProgressionPartitionComposition
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)] (i : ι) (f : X i → ℝ) :
    (𝔼 x : (∀ j, X j), f (x i)) = 𝔼 a, f a := by
  have h := Fintype.expect_equiv (Equiv.piSplitAt i X)
    (fun x => f (x i)) (fun x => f x.1) (fun _ => rfl)
  rw [h]
  simpa using Finset.expect_product' (Finset.univ : Finset (X i))
    (Finset.univ : Finset (∀ j : {j // j ≠ i}, X j)) (fun a _ => f a)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def coordinateExceptional {ι X : Type*} [Fintype ι] [Fintype X]
    (B : Finset X) : Finset (ι → X) := by
  classical
  exact Finset.univ.filter (fun x => ∃ i, x i ∈ B)

theorem not_mem_coordinateExceptional {ι X : Type*} [Fintype ι] [Fintype X]
    (B : Finset X) (x : ι → X) : x ∉ coordinateExceptional B ↔ ∀ i, x i ∉ B := by
  classical
  simp [coordinateExceptional]

theorem coordinateExceptional_density_le {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype X] [Nonempty X] (B : Finset X) :
    ((coordinateExceptional (ι := ι) B).card : ℝ) / Fintype.card (ι → X) ≤
      (Fintype.card ι : ℝ) * (B.card : ℝ) / Fintype.card X := by
  classical
  have hpoint (x : ι → X) : (if ∃ i, x i ∈ B then (1 : ℝ) else 0) ≤
      ∑ i, if x i ∈ B then (1 : ℝ) else 0 := by
    by_cases h : ∃ i, x i ∈ B
    · obtain ⟨i, hi⟩ := h
      rw [ite_eq_left ⟨i, hi⟩]
      calc
        (1 : ℝ) = if x i ∈ B then 1 else 0 := by rw [ite_eq_left hi]
        _ ≤ _ := Finset.single_le_sum
          (f := fun j : ι => if x j ∈ B then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
    · rw [ite_eq_right h]
      exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)
  calc
    _ = 𝔼 x : ι → X, if ∃ i, x i ∈ B then (1 : ℝ) else 0 := by
      simp [coordinateExceptional, Fintype.expect_eq_sum_div_card]
      congr 1
      ext x
      simp
    _ ≤ 𝔼 x : ι → X, ∑ i, if x i ∈ B then (1 : ℝ) else 0 :=
      Finset.expect_le_expect (fun x _ => hpoint x)
    _ = ∑ i, 𝔼 x : ι → X, if x i ∈ B then (1 : ℝ) else 0 := Finset.expect_sum_comm _ _ _
    _ = ∑ _i : ι, (B.card : ℝ) / Fintype.card X := by
      congr 1
      funext i
      rw [expect_coordinate (X := fun _ : ι => X) i (fun x : X => if x ∈ B then (1 : ℝ) else 0)]
      simp [Fintype.expect_eq_sum_div_card, Finset.sum_ite_mem]
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Erdos3

end

section

namespace Erdos3.BoxProgressionPartition

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i))

end Erdos3.BoxProgressionPartition

end

section

namespace Erdos3.BoxProgressionPartition

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i))

end Erdos3.BoxProgressionPartition

end

section

namespace Erdos3

open scoped BigOperators

namespace BoxProgressionPartition

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i))

end BoxProgressionPartition
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

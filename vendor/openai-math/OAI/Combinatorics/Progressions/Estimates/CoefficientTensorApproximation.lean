/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/CoefficientTensorApproximation.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.CocycleHorizontalNormalization
public import OAI.Combinatorics.Progressions.Estimates.GramCovolume
public import OAI.Combinatorics.Progressions.Estimates.LowerTriangularMinor
public import OAI.Combinatorics.Progressions.Linear.BasisImageSection
public import OAI.Combinatorics.Progressions.Linear.SplitSurjectionBasis
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_prod_sub_prod_le_sum_error {I : Type*} (S : Finset I) (f g : I → ℂ)
    {B : ℝ} (hB : 1 ≤ B) (hf : ∀ i ∈ S, ‖f i‖ ≤ B) (hg : ∀ i ∈ S, ‖g i‖ ≤ B) :
    ‖(∏ i ∈ S, f i) - ∏ i ∈ S, g i‖ ≤ B ^ S.card * ∑ i ∈ S, ‖f i - g i‖ := by
  classical
  revert hf hg
  induction S using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert i S hi ih =>
    intro hf hg
    have hrec := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hg j (Finset.mem_insert_of_mem hj))
    have hprod : ‖∏ j ∈ S, g j‖ ≤ B ^ S.card := by
      rw [norm_prod]
      calc
        _ ≤ ∏ _j ∈ S, B := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun j hj => hg j (Finset.mem_insert_of_mem hj))
        _ = _ := by simp
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi,
      Finset.sum_insert hi]
    calc
      _ = ‖f i * ((∏ j ∈ S, f j) - ∏ j ∈ S, g j) +
          (f i - g i) * ∏ j ∈ S, g j‖ := by congr 1; ring
      _ ≤ ‖f i‖ * ‖(∏ j ∈ S, f j) - ∏ j ∈ S, g j‖ +
          ‖f i - g i‖ * ‖∏ j ∈ S, g j‖ := by
        simpa only [norm_mul] using norm_add_le
          (f i * ((∏ j ∈ S, f j) - ∏ j ∈ S, g j)) ((f i - g i) * ∏ j ∈ S, g j)
      _ ≤ B * (B ^ S.card * ∑ j ∈ S, ‖f j - g j‖) + ‖f i - g i‖ * B ^ S.card :=
        add_le_add (mul_le_mul (hf i (Finset.mem_insert_self _ _)) hrec
          (norm_nonneg _) (zero_le_one.trans hB))
          (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))
      _ = B ^ (S.card + 1) * (∑ j ∈ S, ‖f j - g j‖) + ‖f i - g i‖ * B ^ S.card := by
        rw [pow_succ]
        ring
      _ ≤ B ^ (S.card + 1) * (∑ j ∈ S, ‖f j - g j‖) + ‖f i - g i‖ * B ^ (S.card + 1) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hB (Nat.le_succ _)) (norm_nonneg _))
      _ = _ := by ring

theorem mean_prod_error_le {I X : Type*} [Fintype I] [Fintype X]
    (f g : I → X → ℂ) {B ε : ℝ} (hB : 1 ≤ B)
    (hf : ∀ i x, ‖f i x‖ ≤ B) (hg : ∀ i x, ‖g i x‖ ≤ B)
    (herr : ∀ i, (𝔼 x, ‖f i x - g i x‖) ≤ ε) :
    (𝔼 x, ‖(∏ i, f i x) - ∏ i, g i x‖) ≤ B ^ Fintype.card I * ((Fintype.card I : ℝ) * ε) := by
  calc
    _ ≤ 𝔼 x, B ^ Fintype.card I * ∑ i, ‖f i x - g i x‖ :=
      Finset.expect_le_expect (fun x _ => by
        simpa only [Finset.card_univ] using norm_prod_sub_prod_le_sum_error Finset.univ
          (fun i => f i x) (fun i => g i x) hB (fun i _ => hf i x) (fun i _ => hg i x))
    _ = B ^ Fintype.card I * ∑ i, 𝔼 x, ‖f i x - g i x‖ := by
      rw [← Finset.mul_expect, Finset.expect_sum_comm]
    _ ≤ B ^ Fintype.card I * ∑ _ : I, ε :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => herr i))
        (pow_nonneg (zero_le_one.trans hB) _)
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

end OAI

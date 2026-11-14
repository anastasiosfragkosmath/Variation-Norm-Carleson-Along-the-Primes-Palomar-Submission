/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Sampling/NativeGridRightDictionary.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.NativeRationalRepresentatives
@[expose] public section

namespace OAI

section

namespace Erdos3

theorem finite_card_real_grid_box {ι : Type*} [Fintype ι]
    (S : Set (ι → ℝ)) (l N : ℕ) (hl : 0 < l) {B : ℝ}
    (hgrid : S ⊆ realDenominatorGrid l)
    (hbound : ∀ x ∈ S, ∀ i, |x i| ≤ B)
    (hN : (l : ℝ) * B ≤ N) :
    S.Finite ∧ S.ncard ≤ (2 * N + 1) ^ Fintype.card ι := by
  classical
  let z : S → ι → ℤ := fun x => Classical.choose (hgrid x.property)
  have hz (x : S) (i : ι) : (z x i : ℝ) = (l : ℝ) * x.val i :=
    congrFun (Classical.choose_spec (hgrid x.property)) i
  have hzi (x : S) (i : ι) : z x i ∈ Set.Icc (-(N : ℤ)) N := by
    have hb : |(z x i : ℝ)| ≤ (N : ℝ) := by
      rw [hz, abs_mul, abs_of_nonneg (Nat.cast_nonneg l)]
      exact (mul_le_mul_of_nonneg_left (hbound x x.property i) (Nat.cast_nonneg l)).trans hN
    apply abs_le.mp
    exact_mod_cast hb
  let f : S → (ι → Set.Icc (-(N : ℤ)) N) := fun x i => ⟨z x i, hzi x i⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hi : z x i = z y i := congrArg Subtype.val (congrFun hxy i)
    apply mul_left_cancel₀ (show (l : ℝ) ≠ 0 by exact_mod_cast hl.ne')
    rw [← hz, ← hz, hi]
  let : Finite S := Finite.of_injective f hf
  have hcardI : Fintype.card (Set.Icc (-(N : ℤ)) N) = 2 * N + 1 := by
    have h := Int.card_fintype_Icc_of_le (-(N : ℤ)) N (show -(N : ℤ) ≤ N + 1 by omega)
    omega
  refine ⟨Set.toFinite S, ?_⟩
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_fun, hcardI] using hc

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

namespace NativeGridRightDictionary

end NativeGridRightDictionary

end Erdos3.RationalFilteredNilmanifold

end

end OAI

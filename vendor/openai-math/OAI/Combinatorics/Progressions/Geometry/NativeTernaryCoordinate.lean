/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Geometry/NativeTernaryCoordinate.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Lattices.NativeIntegerSelfEquivalence
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def BinaryTensorIndex (I : Type*) : ℕ → Type _
  | 0 => I
  | n + 1 => BinaryTensorIndex I n × BinaryTensorIndex I n

instance BinaryTensorIndex.fintype (I : Type*) [Fintype I] (n : ℕ) : Fintype (BinaryTensorIndex I n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype I)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (BinaryTensorIndex I n × BinaryTensorIndex I n))

variable {σ I : Type*} [DecidableEq σ]

def coordinateTranslatedInput (l : List σ) (x : Option σ → ℤ) (i : σ) : ℤ :=
  x (some i) + if i ∈ l then x none else 0

def coordinateTranslationHom (l : List σ) (j : Option σ) : ((Option σ → ℤ) →+ ℤ) where
  toFun x := match j with
    | none => x none
    | some i => coordinateTranslatedInput l x i
  map_zero' := by cases j <;> simp [coordinateTranslatedInput]
  map_add' x y := by
    cases j with
    | none => rfl
    | some i =>
      simp only [coordinateTranslatedInput, Pi.add_apply]
      split_ifs <;> ring

def coordinateReplaceIndex (i : σ) (j : Option σ) : Option σ :=
  if j = some i then none else j

def coordinateReplaceInput (i : σ) (x : Option σ → ℤ) : Option σ → ℤ :=
  fun j => x (coordinateReplaceIndex i j)

theorem coordinateTranslation_sum (l : List σ) (i : σ) (hi : i ∉ l) (x : Option σ → ℤ) :
    coordinateAdditionInputs i (fun j => coordinateTranslationHom l j x) 0 =
      coordinateTranslatedInput (i :: l) x := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [coordinateAdditionInputs, coordinateTranslationHom, coordinateTranslatedInput, hi]
  · simp [coordinateAdditionInputs, coordinateTranslationHom, coordinateTranslatedInput, hj]

theorem coordinateTranslation_left (l : List σ) (i : σ) (x : Option σ → ℤ) :
    coordinateAdditionInputs i (fun j => coordinateTranslationHom l j x) 1 =
      coordinateTranslatedInput l x := rfl

theorem coordinateTranslation_right (l : List σ) (i : σ) (hi : i ∉ l) (x : Option σ → ℤ) :
    coordinateAdditionInputs i (fun j => coordinateTranslationHom l j x) 2 =
      coordinateTranslatedInput l (coordinateReplaceInput i x) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [coordinateAdditionInputs, coordinateTranslationHom, coordinateTranslatedInput,
      coordinateReplaceInput, coordinateReplaceIndex, hi]
  · simp [coordinateAdditionInputs, coordinateTranslationHom, coordinateTranslatedInput,
      coordinateReplaceInput, coordinateReplaceIndex, hj]

noncomputable def coordinateTranslationExpansion (f : I → (σ → ℤ) → ℂ) :
    (l : List σ) → BinaryTensorIndex I l.length → (Option σ → ℤ) → ℂ
  | [], a, x => f a (fun j => x (some j))
  | i :: l, a, x => coordinateTranslationExpansion f l a.1 x *
      coordinateTranslationExpansion f l a.2 (coordinateReplaceInput i x)

theorem coordinateTranslationExpansion_unit [Fintype I] (f : I → (σ → ℤ) → ℂ)
    (hunit : ∀ x, ∑ i, ‖f i x‖ ^ 2 = 1) (l : List σ) (x : Option σ → ℤ) :
    ∑ a : BinaryTensorIndex I l.length, ‖coordinateTranslationExpansion f l a x‖ ^ 2 = 1 := by
  induction l generalizing x with
  | nil => exact hunit _
  | cons i l ih =>
    change (∑ a : BinaryTensorIndex I l.length × BinaryTensorIndex I l.length,
      ‖coordinateTranslationExpansion f l a.1 x *
        coordinateTranslationExpansion f l a.2 (coordinateReplaceInput i x)‖ ^ 2) = 1
    simp only [Fintype.sum_prod_type, norm_mul, mul_pow, ← Finset.mul_sum, ih, mul_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def TernaryTensorIndex (I : Type*) : ℕ → Type _
  | 0 => I
  | n + 1 => TernaryTensorIndex I n × (TernaryTensorIndex I n × TernaryTensorIndex I n)

variable {σ I : Type*} [DecidableEq σ]

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

theorem exists_coordinate_translation_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p)
      (l : List σ) (i : σ), i ∉ l →
      NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C)
        (fun k x => W.eval k (coordinateTranslatedInput (i :: l) x))
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval k.1 (coordinateTranslatedInput l x) *
            W.eval k.2 (coordinateTranslatedInput l (coordinateReplaceInput i x))) := by
  obtain ⟨C, hC, hadd⟩ := exists_multilinearity_equivalence (σ := σ)
  refine ⟨C, hC, ?_⟩
  intro p W l i hi
  have E := (hadd W i).linearPullbackHom (coordinateTranslationHom l)
  simpa only [coordinateSumVector, coordinateTensorVector,
    coordinateTranslation_sum l i hi, coordinateTranslation_left,
    coordinateTranslation_right l i hi] using E

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/FirstCoefficientDimension.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Linear.RealFirstCoefficientBasis
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι : Type*} (w : σ → ℕ) (ω : ι → ℕ)

def firstCoefficientIndexEmbedding : FirstCoefficientIndex w ω ↪ AdaptedBasisIndex w ω where
  toFun z := ⟨z.val, (Nat.le_add_right _ 1).trans z.property.le⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : AdaptedBasisIndex w ω => z.val) h

variable [Fintype σ] [Fintype ι] (s : ℕ) (hw : ∀ i, 0 < w i) (hω : ∀ i, ω i ≤ s)

@[instance_reducible] noncomputable def firstCoefficientIndexFintype :
    Fintype (FirstCoefficientIndex w ω) := by
  letI := adaptedBasisIndexFintype w ω s hw hω
  exact Fintype.ofInjective (firstCoefficientIndexEmbedding w ω) (firstCoefficientIndexEmbedding w ω).injective

include hw hω in
theorem firstCoefficientIndex_card_le [Fintype (FirstCoefficientIndex w ω)] :
    Fintype.card (FirstCoefficientIndex w ω) ≤ Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s := by
  let := adaptedBasisIndexFintype w ω s hw hω
  exact (Fintype.card_le_of_injective _ (firstCoefficientIndexEmbedding w ω).injective).trans
    (adaptedBasisIndex_card_le w ω s hw hω)

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hw hF

end Erdos3.NilpotentLieFiltration

end

end OAI

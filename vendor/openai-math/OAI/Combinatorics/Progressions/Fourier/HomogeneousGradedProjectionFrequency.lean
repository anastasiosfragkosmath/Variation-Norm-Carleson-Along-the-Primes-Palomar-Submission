/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Fourier/HomogeneousGradedProjectionFrequency.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.GradedPieceRepresentative
public import OAI.Combinatorics.Progressions.Estimates.ProjectedPointwiseCoefficient
public import OAI.Combinatorics.Progressions.Nilpotent.CurrentBracketInductionStep
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module

variable {K V W ι κ : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def gradedFrequency (η : L →ₗ[ℚ] ℚ) : F.AssociatedGraded →ₗ[ℚ] ℚ :=
  η.comp (b.repr.symm.toLinearMap.comp (F.associatedGradedBasis b ω hF).repr.toLinearMap)

theorem gradedFrequency_projection (η : L →ₗ[ℚ] ℚ) (j : ℕ) (x : L) :
    F.gradedFrequency b ω hF η (F.gradedPieceProjection b ω hF j x) =
      η (basisGradeProjection b ω j x) := by
  change η (b.repr.symm ((F.associatedGradedBasis b ω hF).repr
    ((F.associatedGradedBasis b ω hF).repr.symm (b.repr (basisGradeProjection b ω j x))))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

include hF in
theorem basisGradeProjection_top (x : F.layer s) : basisGradeProjection b ω s (x : L) = x := by
  have he : {i | ω i = s} = {i | s ≤ ω i} := by
    ext i
    exact ⟨fun h => h.ge, fun h => le_antisymm (F.adaptedBasis_weight_le_step b ω hF i) h⟩
  change basisCoordinateProjection b {i | ω i = s} (x : L) = x
  rw [he]
  exact basisCoordinateProjection_eq_self b _ _ ((hF s) ▸ x.property)

theorem gradedFrequency_top_piece (η : L →ₗ[ℚ] ℚ) (x : F.layer s) :
    F.gradedFrequency b ω hF η (F.associatedGradedPieceMap s x) = η x := by
  rw [← F.gradedPieceProjection_eq_pieceMap b ω hF, F.gradedFrequency_projection,
    F.basisGradeProjection_top b ω hF x]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (f : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}

variable (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

end Erdos3.NilpotentLieFiltration

end

end OAI

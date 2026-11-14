/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/GradedPieceRepresentative.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Linear.AssociatedGradedBasisIndependence
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_associatedGradedPieceMap_of_pure
    {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (j : ℕ) (x : F.AssociatedGraded)
    (hx : basisGradeProjection (F.associatedGradedBasis e ω hF) ω j x = x) :
    ∃ v : F.layer j, F.associatedGradedPieceMap j v = x := by
  have hm := basisCoordinateProjection_mem_span (F.associatedGradedBasis e ω hF)
    {i | ω i = j} x
  change basisGradeProjection (F.associatedGradedBasis e ω hF) ω j x ∈ _ at hm
  rw [hx, ← F.associatedGradedPieceMap_range e ω hF j] at hm
  exact hm

end Erdos3.NilpotentLieFiltration

end

end OAI

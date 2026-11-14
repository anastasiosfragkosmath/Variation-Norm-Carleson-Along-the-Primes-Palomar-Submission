/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/ShortVectorProjection.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Lattices.DenseIntegerSpan
public import OAI.Combinatorics.Progressions.Lattices.LatticeVoronoiPacking
@[expose] public section

namespace OAI

section

namespace Erdos3

theorem shortVectorSpan_map_eq_top_of_spanning_integer_images
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ)) (H : Finset (ι → ℤ)) (R : ℝ)
    (hspan : Submodule.span ℝ {x : ι → ℝ | ∃ h ∈ H, x = fun i => (h i : ℝ)} = ⊤)
    (hlift : ∀ h ∈ H, ∃ v ∈ Λ, ‖v‖ ≤ R ∧ π v = fun i => (h i : ℝ)) :
    (shortVectorSpan Λ R).map π = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro x ⟨h, hh, rfl⟩
  obtain ⟨v, hv, hnorm, hπ⟩ := hlift h hh
  exact ⟨v, mem_shortVectorSpan Λ R hv hnorm, hπ⟩

end Erdos3

end

end OAI

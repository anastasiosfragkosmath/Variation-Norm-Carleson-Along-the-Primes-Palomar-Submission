/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/DescendedLinearMapBounds.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Geometry.EmbeddingCoordinateHeight
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module

variable {L M Z ι κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] [AddCommGroup Z] [Module ℚ Z]
  [Fintype ι] [Fintype κ]

theorem descended_linear_map_coordinate_height
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (b : Basis ν ℚ Z)
    (π : L →ₗ[ℚ] M) (hπ : Function.Surjective π) (φ : M →ₗ[ℚ] Z)
    {Q H : ℕ} (hQ : 1 ≤ Q)
    (hproj : ∀ i j, RationalHeightLE (f.repr (π (e j)) i) Q)
    (hcomp : ∀ i j, RationalHeightLE (b.repr (φ (π (e j))) i) H) (i : ν) (j : κ) :
    RationalHeightLE (b.repr (φ (f j)) i)
      ((Fintype.card ι + 1) * (rationalSolveHeight (Fintype.card κ) Q * H) ^ Fintype.card ι) := by
  obtain ⟨σ, hσ, hσH⟩ := exists_bounded_linear_section e f π hπ hQ hproj
  have h := linearMap_coordinate_height e b (φ.comp π) (fun j i => hcomp i j)
    (σ (f j)) (fun k => hσH k j) i
  simpa only [LinearMap.comp_apply, hσ (f j)] using h

end Erdos3

end

end OAI

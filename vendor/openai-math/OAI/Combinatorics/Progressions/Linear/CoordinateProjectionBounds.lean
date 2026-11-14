/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/CoordinateProjectionBounds.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis
public import OAI.Combinatorics.Progressions.Sampling.RationalSpanGrid
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module

theorem basisCoordinateProjection_abs_repr_le {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    (b : Basis ι ℝ V) (S : Set ι) (x : V) (i : ι) :
    |b.repr (basisCoordinateProjection b S x) i| ≤ |b.repr x i| := by
  classical
  rw [basisCoordinateProjection_repr]
  split_ifs
  · exact le_rfl
  · simpa only [abs_zero] using abs_nonneg (b.repr x i)

theorem basisCoordinateProjection_norm_le {V ι : Type*} [AddCommGroup V] [Module ℝ V] [Fintype ι]
    (b : Basis ι ℝ V) (S : Set ι) (x : V) :
    ‖b.equivFun (basisCoordinateProjection b S x)‖ ≤ ‖b.equivFun x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact (basisCoordinateProjection_abs_repr_le b S x i).trans (norm_le_pi_norm (b.equivFun x) i)

theorem basisCoordinateProjection_real_grid {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    (b : Basis ι ℝ V) (S : Set ι) (l : ℕ) (x : V) (hx : (fun i => b.repr x i) ∈ realDenominatorGrid l) :
    (fun i => b.repr (basisCoordinateProjection b S x) i) ∈ realDenominatorGrid l := by
  classical
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun i => if i ∈ S then z i else 0, ?_⟩
  funext i
  have hi := congrFun hz i
  change (z i : ℝ) = (l : ℝ) * b.repr x i at hi
  change ((if i ∈ S then z i else 0 : ℤ) : ℝ) = (l : ℝ) * b.repr (basisCoordinateProjection b S x) i
  rw [basisCoordinateProjection_repr]
  by_cases h : i ∈ S <;> simp only [h, ↓reduceIte, Int.cast_zero, mul_zero]
  exact hi

end Erdos3

end

end OAI

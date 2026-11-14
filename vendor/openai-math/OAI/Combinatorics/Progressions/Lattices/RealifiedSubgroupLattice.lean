/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Lattices/RealifiedSubgroupLattice.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.PetalComparisonTree
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def realificationSubgroupHom (K : LieSubalgebra ℚ L) :
    NilpotentLieBCHGroup (ℝ ⊗[ℚ] K) s
      (realification_lowerCentralSeries_eq_bot (lie_subalgebra_lowerCentralSeries_eq_bot hnil K)) →*
      realificationSubgroup (hnil := hnil) K :=
  (realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K)
    (hM := hnil) K.incl).codRestrict _ (realificationMap_incl_mem (hnil := hnil) K)

theorem realificationSubgroupHom_surjective (K : LieSubalgebra ℚ L) :
    Function.Surjective (realificationSubgroupHom (hnil := hnil) K) := by
  intro g
  have hg : g.1 ∈ (realificationMap
      (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) (hM := hnil) K.incl).range := by
    rw [realificationMap_incl_range]
    exact g.2
  obtain ⟨x, hx⟩ := hg
  exact ⟨x, Subtype.ext hx⟩

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

end Erdos3.NilpotentLieBCHGroup

end

end OAI

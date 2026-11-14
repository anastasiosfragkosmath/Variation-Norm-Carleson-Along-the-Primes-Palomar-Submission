/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Geometry/QuotientSubgroupCoordinates.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Nilpotent.BCHSubgroupGridExistence
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem quotient_mem_map_subgroup_iff (I : LieIdeal ℚ L) (U : LieSubalgebra ℚ L)
    (g : NilpotentLieBCHGroup L s hnil) :
    quotientHom I g ∈ (subgroup (hnil := hnil) U).map (quotientHom (hnil := hnil) I) ↔
      g.coord ∈ U.toSubmodule ⊔ I.toSubmodule := by
  constructor
  · intro hg
    obtain ⟨u, hu, heq⟩ := Subgroup.mem_map.mp hg
    have hdiff : g.coord - u.coord ∈ I := by
      apply (lieQuotientMap_eq_zero I _).mp
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg coord heq).symm
    apply Submodule.mem_sup.mpr
    exact ⟨u.coord, hu, g.coord - u.coord, hdiff, by abel⟩
  · intro hg
    obtain ⟨u, hu, v, hv, heq⟩ := Submodule.mem_sup.mp hg
    apply Subgroup.mem_map.mpr
    refine ⟨⟨u⟩, hu, ?_⟩
    apply ext
    change lieQuotientMap I u = lieQuotientMap I g.coord
    rw [← heq, map_add, (lieQuotientMap_eq_zero I v).mpr hv, add_zero]

end Erdos3.NilpotentLieBCHGroup

end

end OAI

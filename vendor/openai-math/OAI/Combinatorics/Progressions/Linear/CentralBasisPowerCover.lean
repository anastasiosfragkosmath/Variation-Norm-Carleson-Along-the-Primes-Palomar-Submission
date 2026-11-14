/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/CentralBasisPowerCover.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Lattices.LatticeOrderedGenerators
@[expose] public section

namespace OAI

section

namespace Erdos3.IsCentralLieBasis

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))

include he

theorem subgroupPowerCover_index_le (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) (m : ℕ) (hm : 0 < m) :
    ((subgroupPowerCover Γ m).subgroupOf Γ).FiniteIndex ∧
      (subgroupPowerCover Γ m).relIndex Γ ≤ m ^ d := by
  obtain ⟨a, ha⟩ := he.exists_surjective_orderedZpowProduct hnil Γ l hl hgrid
  have h := powerSubgroup_index_le_of_ordered_generators a ha m hm
  simpa only [Subgroup.relIndex, subgroupPowerCover_subgroupOf] using h

end Erdos3.IsCentralLieBasis

end

end OAI

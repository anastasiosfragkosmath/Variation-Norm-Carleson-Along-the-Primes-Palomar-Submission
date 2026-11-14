/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Lattices/FilteredLatticePowerIndex.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Linear.CentralBasisPowerCover
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

theorem subgroupPowerCover_index_le (e : Basis ι ℚ L) (Γ : Subgroup F.Group)
    (l : ℕ) (hl : 0 < l) (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (m : ℕ) (hm : 0 < m) :
    ((subgroupPowerCover Γ m).subgroupOf Γ).FiniteIndex ∧
      (subgroupPowerCover Γ m).relIndex Γ ≤ m ^ Fintype.card ι := by
  let : FiniteDimensional ℚ L := Module.Finite.of_basis e
  obtain ⟨b, hb⟩ := F.exists_central_basis
  obtain ⟨N, hN, hgrid⟩ := exists_bchSubgroup_outer_grid_change_basis e b Γ l hl houter
  simpa only [finrank_eq_card_basis e] using
    hb.subgroupPowerCover_index_le F.lowerCentralSeries_eq_bot Γ N hN hgrid m hm

end Erdos3.NilpotentLieFiltration

end

end OAI

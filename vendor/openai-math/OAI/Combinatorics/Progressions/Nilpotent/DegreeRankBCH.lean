/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/DegreeRankBCH.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Polynomial.DegreeRankSunflower
@[expose] public section

namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

def layerIdeal (d i : ℕ) : LieIdeal ℚ L :=
  { F.layer d i with
    lie_mem := by
      intro x y hy
      have hx : x ∈ F.layer 1 0 := by simp only [F.one_eq_top, Submodule.mem_top]
      exact F.lex_antitone (Or.inl (show d < 1 + d by omega)) (F.lie_mem hx hy) }

@[simp] theorem mem_layerIdeal (d i : ℕ) (x : L) :
    x ∈ F.layerIdeal d i ↔ x ∈ F.layer d i := Iff.rfl

abbrev Group := F.associatedDegree.Group

def subgroup (d i : ℕ) : Subgroup F.Group :=
  NilpotentLieBCHGroup.subgroup (F.layerIdeal d i).toLieSubalgebra

@[simp] theorem mem_subgroup (d i : ℕ) (x : F.Group) :
    x ∈ F.subgroup d i ↔ x.coord ∈ F.layer d i := Iff.rfl

theorem subgroup_le_associatedDegree (d i : ℕ) : F.subgroup d i ≤ F.associatedDegree.subgroup d :=
  fun _ hx => F.layer_le_associatedDegree d i hx

end Erdos3.DegreeRankLieFiltration

end

end OAI

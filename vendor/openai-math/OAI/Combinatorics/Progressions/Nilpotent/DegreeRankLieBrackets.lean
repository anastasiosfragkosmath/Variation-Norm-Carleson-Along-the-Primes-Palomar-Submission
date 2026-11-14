/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/DegreeRankLieBrackets.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Polynomial.DegreeRankLayers
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem rank_span_lie_mem {d e r t : ℕ} {x y : L}
    (hx : x ∈ Submodule.span ℚ (F.rankGenerators d r))
    (hy : y ∈ Submodule.span ℚ (F.rankGenerators e t)) :
    ⁅x, y⁆ ∈ F.rankLayer (d + e) (r + t) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨i, hi, a, rfl⟩ := hx
    obtain ⟨j, hj, b, rfl⟩ := hy
    exact F.tree_eval_mem_rankLayer (a.bracket b) (Nat.add_le_add hi hj)
  | zero_left y _ => rw [zero_lie]; exact Submodule.zero_mem _
  | zero_right x _ => rw [lie_zero]; exact Submodule.zero_mem _
  | add_left x y z _ _ _ hx hy => rw [add_lie]; exact Submodule.add_mem _ hx hy
  | add_right x y z _ _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
  | smul_left c x y _ _ h => rw [smul_lie]; exact Submodule.smul_mem _ c h
  | smul_right c x y _ _ h => rw [lie_smul]; exact Submodule.smul_mem _ c h

theorem rankLayer_lie_mem {d e r t : ℕ} {x y : L}
    (hx : x ∈ F.rankLayer d r) (hy : y ∈ F.rankLayer e t) :
    ⁅x, y⁆ ∈ F.rankLayer (d + e) (r + t) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, hc, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
  have hb' : b ∈ F.layer d := F.rankLayer_le_layer d r (F.span_rankGenerators_le_rankLayer d r hb)
  have hz' : z ∈ F.layer e := F.rankLayer_le_layer e t (F.span_rankGenerators_le_rankLayer e t hz)
  have hc' : c ∈ F.layer e := F.antitone (by omega) hc
  have hleft {u v : L} (hu : u ∈ F.layer (d + 1)) (hv : v ∈ F.layer e) :
      ⁅u, v⁆ ∈ F.rankLayer (d + e) (r + t) := by
    apply F.layer_succ_le_rankLayer
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using F.lie_mem hu hv
  have hright : ⁅b, c⁆ ∈ F.rankLayer (d + e) (r + t) := by
    apply F.layer_succ_le_rankLayer
    simpa only [Nat.add_assoc] using F.lie_mem hb' hc
  simp only [add_lie, lie_add]
  exact Submodule.add_mem _ (Submodule.add_mem _ (hleft ha hc') hright)
    (Submodule.add_mem _ (hleft ha hz') (F.rank_span_lie_mem hb hz))

end Erdos3.NilpotentLieFiltration

end

end OAI

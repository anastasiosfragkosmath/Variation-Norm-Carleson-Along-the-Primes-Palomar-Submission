/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/BCHOrderedReduction.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Linear.BoundedAdaptedBasis
@[expose] public section

namespace OAI

section

namespace Erdos3.IsCentralLieBasis

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

include he hnil

theorem bch_remainder_mem_tail (i : ℕ) (a : L) {b : L} (hb : b ∈ basisTail e i) :
    lieBCH s a b - (a + b) ∈ basisTail e (i + 1) :=
  lieBCH_sub_add_mem hnil (he.tailIdeal (i + 1)) a b (he.lie_mem_tail_succ i a hb)

theorem bch_low_coordinate (i : ℕ) (a : L) {b : L} (hb : b ∈ basisTail e i)
    (k : Fin d) (hk : k.val ≤ i) :
    e.repr (lieBCH s a b) k = e.repr a k + e.repr b k := by
  have h := he.bch_remainder_mem_tail hnil i a hb k (Nat.lt_succ_of_le hk)
  rw [map_sub, Finsupp.sub_apply, map_add, Finsupp.add_apply] at h
  exact sub_eq_zero.mp h

end Erdos3.IsCentralLieBasis

end

end OAI

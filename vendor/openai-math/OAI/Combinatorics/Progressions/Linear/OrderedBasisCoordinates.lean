/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/OrderedBasisCoordinates.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.TakeDrop
public import OAI.Combinatorics.Progressions.Nilpotent.BCHOrderedReduction
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module

theorem mem_drop_finRange_iff {d i : ℕ} {j : Fin d} :
    j ∈ (List.finRange d).drop i ↔ i ≤ j.val := by
  rw [List.mem_drop_iff_getElem]
  constructor
  · rintro ⟨k, hk, heq⟩
    have hval : i + k = j.val := by simpa using congrArg Fin.val heq
    omega
  · intro hij
    refine ⟨j.val - i, ?_, ?_⟩
    · simp only [List.length_finRange]
      omega
    · apply Fin.ext
      simp only [List.getElem_finRange, Fin.val_cast]
      omega

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (e : Basis (Fin d) ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

namespace IsCentralLieBasis

variable {e} (he : IsCentralLieBasis e)
include he

end IsCentralLieBasis
end Erdos3

end

section

namespace Erdos3.IsCentralLieBasis

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

include he

end Erdos3.IsCentralLieBasis

end

end OAI

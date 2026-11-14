/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/TopSubspaceAdaptedBasis.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.LowerStepSquare
public import OAI.Combinatorics.Progressions.Linear.BoundedAdaptedBasis
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s : ℕ}

def topSubspaceIdeal (F : NilpotentLieFiltration L s) (K : Submodule ℚ L)
    (hK : K ≤ F.layer s) : LieIdeal ℚ L :=
  { K with
    lie_mem := by
      intro x y hy
      rw [← lie_skew, F.top_layer_central (hK hy) x, neg_zero]
      exact K.zero_mem }

end Erdos3.NilpotentLieFiltration

end

end OAI

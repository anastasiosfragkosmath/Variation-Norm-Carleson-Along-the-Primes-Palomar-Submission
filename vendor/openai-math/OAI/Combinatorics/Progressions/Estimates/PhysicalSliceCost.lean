/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/PhysicalSliceCost.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
@[expose] public section

namespace OAI

section

namespace Erdos3

def PhysicalSubbox {σ : Type*} (parent : σ → ℤ) (H : σ → ℕ)
    (lo : σ → ℤ) (N : σ → ℕ) : Prop :=
  ∀ j, parent j ≤ lo j ∧ lo j + N j ≤ parent j + H j

end Erdos3

end

end OAI

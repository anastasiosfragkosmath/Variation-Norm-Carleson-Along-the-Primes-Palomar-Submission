/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/BasisFamilyLogHeight.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight
@[expose] public section

namespace OAI

section

namespace Erdos3

def BasisFamilyLogHeight {ι κ V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Module.Basis ι ℚ V) (v : κ → V) (p : ℝ) : Prop :=
  ∀ i j, rationalLogHeight (b.repr (v i) j) ≤ p

end Erdos3

end

end OAI

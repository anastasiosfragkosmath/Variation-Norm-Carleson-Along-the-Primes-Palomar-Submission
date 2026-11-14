/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/GowersWeightedDerivative.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.BooleanCubeProduct
@[expose] public section

namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

def derivativeSupport (Q : Finset H) (h : H) : Finset H :=
  Q.filter (fun x ↦ x + h ∈ Q)

end Erdos3

end

end OAI

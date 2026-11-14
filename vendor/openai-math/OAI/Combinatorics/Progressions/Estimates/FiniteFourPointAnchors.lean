/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/FiniteFourPointAnchors.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib
@[expose] public section

namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

variable (G : Type*) [AddCommGroup G]

def fourSparse12Equiv : (G × G × G) ≃ (G × G) × G where
  toFun t := ((t.2.2, t.2.1), t.2.1 - t.1)
  invFun u := (u.1.2 - u.2, u.1.2, u.1.1)
  left_inv := by rintro ⟨a, b, c⟩; simp
  right_inv := by rintro ⟨⟨a, b⟩, h⟩; simp

variable {G} [Fintype G]

end Erdos3

end

end OAI

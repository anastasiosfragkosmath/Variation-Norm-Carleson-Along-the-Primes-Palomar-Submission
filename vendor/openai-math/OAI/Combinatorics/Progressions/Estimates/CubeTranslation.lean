/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/CubeTranslation.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport
@[expose] public section

namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [DecidableEq A]

def translateSupport (a : A) (Q : Finset A) : Finset A := Q.image (fun x ↦ a + x)

theorem mem_translateSupport (a : A) (Q : Finset A) (x : A) :
    x ∈ translateSupport a Q ↔ x - a ∈ Q := by
  rw [translateSupport, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨x - a, hx, by abel⟩

theorem card_translateSupport (a : A) (Q : Finset A) : (translateSupport a Q).card = Q.card :=
  Finset.card_image_of_injective Q (fun _ _ h ↦ add_left_cancel h)

end Erdos3

end

end OAI

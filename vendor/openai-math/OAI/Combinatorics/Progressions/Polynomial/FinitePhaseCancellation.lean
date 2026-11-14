/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/FinitePhaseCancellation.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Fourier.RectangularGridCharacter
@[expose] public section

namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators

theorem circle_character_mul_star (θ : CircleFourier.Circle) :
    character θ * star (character θ) = 1 := by
  rw [← character_neg, ← character_add, add_neg_cancel, character_zero]

end Erdos3

end

end OAI

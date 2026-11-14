/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Dynamics/SharedFreeLowerComparisonBudget.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.SharedFreeComparisonDescent
@[expose] public section

namespace OAI

section

namespace Erdos3

noncomputable def sharedFreeLowerComparisonBudget (s : ℕ) (q p : ℝ) : ℝ :=
  (sharedFreeComparisonModelBudget s q p + rankUnitDescentConstant s) ^ rankUnitDescentConstant s

end Erdos3

end

end OAI

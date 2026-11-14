/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/ResidualErrorAllocation.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic
@[expose] public section

namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.NativeModelingNumerics

theorem mul_exp_le_exp {a b c d : ℝ} (hc : c ≤ Real.exp d) (hab : a + d ≤ b) :
    c * Real.exp a ≤ Real.exp b := by
  calc
    _ ≤ Real.exp d * Real.exp a := mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
    _ = Real.exp (d + a) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3.NativeModelingNumerics

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

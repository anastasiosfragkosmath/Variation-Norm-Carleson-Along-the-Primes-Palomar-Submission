/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/MahlerBasis.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.LinearAlgebra.FreeModule.PID
@[expose] public section

namespace OAI

section

namespace Erdos3.IntegerBasisReduction.Mahler

open scoped BigOperators
open Module

abbrev IntegralPoint (n : ℕ) := Fin n → ℤ

def integralEmbed {n : ℕ} (x : IntegralPoint n) : Fin n → ℝ :=
  fun i ↦ (x i : ℝ)

end Erdos3.IntegerBasisReduction.Mahler

end

end OAI

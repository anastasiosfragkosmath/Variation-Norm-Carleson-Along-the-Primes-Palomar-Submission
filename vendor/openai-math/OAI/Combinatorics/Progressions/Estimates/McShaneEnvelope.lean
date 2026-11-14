/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/McShaneEnvelope.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Tactic
public import Mathlib.Topology.MetricSpace.Lipschitz
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X Y : Type*} [Nonempty X] [PseudoMetricSpace Y]
  (φ : X → Y) (L : ℝ≥0)

noncomputable def mcShaneEnvelope (f : X → ℝ) (y : Y) : ℝ :=
  ⨅ x, f x + L * dist y (φ x)

end Erdos3

end

end OAI

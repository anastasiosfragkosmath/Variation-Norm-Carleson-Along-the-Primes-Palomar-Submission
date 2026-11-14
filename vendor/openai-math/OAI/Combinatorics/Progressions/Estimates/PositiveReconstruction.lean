/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/PositiveReconstruction.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def positiveClip (z : ℂ) : ℂ := (max 0 (min 1 z.re) : ℝ)

end Erdos3

end

end OAI

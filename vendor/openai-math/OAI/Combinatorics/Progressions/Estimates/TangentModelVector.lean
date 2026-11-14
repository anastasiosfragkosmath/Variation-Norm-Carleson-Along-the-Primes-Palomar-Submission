/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/TangentModelVector.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped Manifold

def tangentModelVector {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {x : M} (v : TangentSpace I x) : E := v

end Erdos3

end

end OAI

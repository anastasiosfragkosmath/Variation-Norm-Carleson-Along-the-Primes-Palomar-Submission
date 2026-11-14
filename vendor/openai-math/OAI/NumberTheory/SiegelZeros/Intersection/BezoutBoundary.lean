/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/NumberTheory/SiegelZeros/Intersection/BezoutBoundary.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.NumberTheory.SiegelZeros.Estimates.GeometricBoundary
@[expose] public section

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.W50

open WeightedTorusJets

theorem uniform_exclusion_of_local_isolated_bezout
    (hBezout : W22.LocalIsolatedBezoutStatement ℂ) :
    UniformSiegelZeroExclusion := by
  apply uniform_exclusion_of_actual_cutoff
  intro H N hH hHN _hN d a hd hd1 hd2 ha
  exact W28.actualCutoffSpanning_of_localBezout hBezout H N (by omega) hHN
    d hd hd1 hd2 a ha

end SiegelZerosAwei.W50

end

end SiegelZeros

end OAI

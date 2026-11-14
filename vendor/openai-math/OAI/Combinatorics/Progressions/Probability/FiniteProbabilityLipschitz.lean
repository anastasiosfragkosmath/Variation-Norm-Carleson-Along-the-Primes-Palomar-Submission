/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Probability/FiniteProbabilityLipschitz.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Prod
public import OAI.Combinatorics.Progressions.Estimates.BufferedSiteExpansion
public import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

structure FiniteProbabilityWeights (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1

namespace FiniteProbabilityWeights

variable {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (law : C → FiniteProbabilityWeights Ω)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights
open scoped Classical BigOperators NNReal

end Erdos3.FiniteProbabilityWeights

end

end OAI

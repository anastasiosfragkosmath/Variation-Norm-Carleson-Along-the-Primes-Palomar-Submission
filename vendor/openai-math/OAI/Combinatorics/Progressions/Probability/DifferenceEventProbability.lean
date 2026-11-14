/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Probability/DifferenceEventProbability.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Fourier.LocalBohrAlmostPeriodsRelative
@[expose] public section

namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open scoped BigOperators Pointwise

variable {N : ℕ}

theorem setAverageTranslate_eq_expect (A : Finset (ZMod N)) (f : ZMod N → ℝ) (x : ZMod N) :
    setAverageTranslate A f x = 𝔼 a ∈ A, f (x - a) := by
  rw [setAverageTranslate, Finset.expect_eq_sum_div_card]

noncomputable def differenceEventProbability
    (A₁ A₂ K : Finset (ZMod N)) (t : ZMod N) : ℝ :=
  𝔼 a ∈ A₁, 𝔼 b ∈ A₂, realSetIndicator K (a - b + t)

theorem differenceEventProbability_eq_triple
    (A₁ A₂ K : Finset (ZMod N)) (t : ZMod N) :
    differenceEventProbability A₁ A₂ K t =
      setAverageTranslate (-A₁) (setAverageTranslate A₂ (realSetIndicator K)) t := by
  rw [differenceEventProbability, setAverageTranslate_eq_expect, Finset.expect_neg_index]
  apply Finset.expect_congr rfl
  intro a _
  rw [setAverageTranslate_eq_expect]
  apply Finset.expect_congr rfl
  intro b _
  congr 1
  abel

end Erdos3.CyclicCrootSisask

end

end OAI

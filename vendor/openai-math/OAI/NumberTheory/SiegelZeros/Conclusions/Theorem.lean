/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/NumberTheory/SiegelZeros/Conclusions/Theorem.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.NumberTheory.SiegelZeros.Intersection.BezoutBoundary
@[expose] public section

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets

theorem exists_absolute_real_zero_gap :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ, 0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 →
          c ≤ (1 - β) * Real.log (q : ℝ) := by
  exact SiegelZerosAwei.W50.uniform_exclusion_of_local_isolated_bezout
    (W22.localIsolatedBezout_of_actual_regular_selection ℂ)

end WeightedTorusJets

end

end SiegelZeros

end OAI

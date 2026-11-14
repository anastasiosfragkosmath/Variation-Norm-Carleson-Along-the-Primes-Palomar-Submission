/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/BalancedDualBounds.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib
@[expose] public section

namespace OAI

section

namespace Erdos3

theorem exists_complex_unit_phase (z : ℂ) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ a * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · subst z
    exact ⟨1, by simp, by simp⟩
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  refine ⟨star z / (‖z‖ : ℂ), ?_, ?_⟩
  · simp [hn]
  · calc
      _ = (star z * z) / (‖z‖ : ℂ) := by ring
      _ = ((‖z‖ ^ 2 : ℝ) : ℂ) / (‖z‖ : ℂ) := by
        rw [mul_comm (star z) z]
        change z * (starRingEnd ℂ) z / (‖z‖ : ℂ) = _
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      _ = _ := by
        rw [Complex.ofReal_pow]
        field_simp

end Erdos3

end

end OAI

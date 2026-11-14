/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/ComplexPolarization.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def polarizationPhase : Fin 4 → ℂ := ![1, -1, Complex.I, -Complex.I]

noncomputable def polarizationWeight (k : Fin 4) : ℂ := polarizationPhase k / 4

theorem polarizationPhase_norm (k : Fin 4) : ‖polarizationPhase k‖ = 1 := by
  fin_cases k <;> norm_num [polarizationPhase]

theorem polarizationWeight_norm (k : Fin 4) : ‖polarizationWeight k‖ = (1 : ℝ) / 4 := by
  simp only [polarizationWeight, norm_div, polarizationPhase_norm]
  norm_num

theorem polarizationWeight_cost : (∑ k, ‖polarizationWeight k‖) = 1 := by
  simp only [polarizationWeight_norm, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

theorem complex_mixed_polarization (a b c d : ℂ) :
    a * star d = ∑ k, polarizationWeight k *
      ((a + polarizationPhase k * b) * star (c + polarizationPhase k * d)) := by
  norm_num [Fin.sum_univ_succ, polarizationWeight, polarizationPhase,
    star_add, star_mul, Complex.star_def]
  ring_nf
  norm_num [Complex.I_sq]
  ring

end Erdos3

end

end OAI

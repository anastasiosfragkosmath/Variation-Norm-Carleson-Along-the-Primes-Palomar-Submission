/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/UnitVerticalDifference.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Linear.BinaryLowerRankFamily
@[expose] public section

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct BigOperators NNReal

variable {L I J : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] [Fintype J]
  {s d : ℕ} [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p : ℝ}
  (V : D.UnitVerticalObservable T I p) (U : D.UnitVerticalObservable T J p)

noncomputable def differenceObservable (a : I × J) (x : D.Space) : ℂ :=
  V.observable a.1 x * star (U.observable a.2 x)

theorem differenceObservable_unit (x : D.Space) :
    ∑ a, ‖V.differenceObservable U a x‖ ^ 2 = 1 := by
  simp only [differenceObservable, norm_mul, norm_star, mul_pow, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, U.unit, mul_one, V.unit]

theorem differenceObservable_norm (a : I × J) (x : D.Space) :
    ‖V.differenceObservable U a x‖ ≤ 1 := by
  simpa only [differenceObservable, norm_mul, norm_star, mul_one] using
    mul_le_mul (V.norm a.1 x) (U.norm a.2 x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem differenceObservable_lipschitz (a : I × J) :
    letI := D.metricSpace
    LipschitzWith (V.lipBound + U.lipBound) (V.differenceObservable U a) := by
  let := D.metricSpace
  exact (lipschitz_mul_star_of_bounds (V.observable a.1) (U.observable a.2)
    (Bf := 1) (Bg := 1) (V.lipschitz a.1) (U.lipschitz a.2)
    (V.norm a.1) (U.norm a.2)).weaken (by simp only [one_mul]; exact le_of_eq (add_comm _ _))

variable {r : ℕ} (R : D.DegreeRankStructure r)
  (V : D.UnitVerticalObservable (R.realSubgroup s r) I p)
  (U : D.UnitVerticalObservable (R.realSubgroup s r) J p)
  (hfreq : ∀ x ∈ R.filtration.layer s r, V.frequency x = U.frequency x)

include hfreq in
theorem differenceObservable_rank_invariant (a : I × J) (z : D.RealGroup)
    (hz : z ∈ R.realSubgroup s r) (x : D.Space) :
    V.differenceObservable U a (z • x) = V.differenceObservable U a x := by
  have heq := realifyFunctional_eq_on_submodule (R.filtration.layer s r)
    V.frequency U.frequency hfreq z.coord hz
  let c := CircleFourier.character
    ((realifyFunctional U.frequency z.coord : ℝ) : CircleFourier.Circle)
  have hc : c * star c = 1 := by
    dsimp only [c]
    rw [← CircleFourier.character_neg, ← CircleFourier.character_add,
      add_neg_cancel, CircleFourier.character_zero]
  unfold differenceObservable
  rw [V.vertical a.1 z hz, U.vertical a.2 z hz, heq, star_mul]
  change (c * V.observable a.1 x) * (star (U.observable a.2 x) * star c) = _
  calc
    _ = (c * star c) * (V.observable a.1 x * star (U.observable a.2 x)) := by ring
    _ = _ := by rw [hc, one_mul]

noncomputable def rankDifference :
    D.UnitVerticalObservable (R.realSubgroup s r) (I × J) (p + 2) where
  observable := V.differenceObservable U
  unit := V.differenceObservable_unit U
  norm := V.differenceObservable_norm U
  lipBound := V.lipBound + U.lipBound
  lip_bound := by
    change (V.lipBound : ℝ) + U.lipBound ≤ Real.exp (p + 2)
    calc
      _ ≤ 2 * Real.exp p := by linarith [V.lip_bound, U.lip_bound]
      _ ≤ Real.exp 2 * Real.exp p := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  lipschitz := V.differenceObservable_lipschitz U
  frequency := 0
  height i := by
    have hp := (rationalLogHeight_nonneg (V.frequency (D.basis i))).trans (V.height i)
    simpa [rationalLogHeight] using (show (0 : ℝ) ≤ p + 2 by linarith)
  vertical a z hz x := by
    simpa only [realifyFunctional_zero, AddCircle.coe_zero,
      CircleFourier.character_zero, one_mul] using
      differenceObservable_rank_invariant R V U hfreq a z hz x
  integral _ _ _ := ⟨0, by simp only [realifyFunctional_zero, Int.cast_zero]⟩

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

end OAI

/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/TranslatedShiftTesting.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Geometry.NativeIntervalCoordinate
public import OAI.Combinatorics.Progressions.Nilpotent.NativeNiltestPartition
public import OAI.Combinatorics.Progressions.Nilpotent.NiltestComplement
@[expose] public section

namespace OAI

universe u

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.PositiveCyclicNiltest

open scoped TensorProduct BigOperators

theorem mul {degree N : ℕ} [NeZero N] {p : ℝ} {f g : ZMod N → ℝ}
    (hf : PositiveCyclicNiltest.{u} degree N p f)
    (hg : PositiveCyclicNiltest.{u} degree N p g) (hp : 0 ≤ p) :
    PositiveCyclicNiltest.{u} degree N (productNiltestBudget (raisedNiltestBudget p))
      (fun x => f x * g x) := by
  rcases hf with @⟨L₁, lie₁, alg₁, s₁, dim₁, top₁, add₁, smul₁, t2₁, D₁, hs₁, A, hA, hAc, hevalA⟩
  rcases hg with @⟨L₂, lie₂, alg₂, s₂, dim₂, top₂, add₂, smul₂, t2₂, D₂, hs₂, B, hB, hBc, hevalB⟩
  let K : Bool → Type u := BoolLieFamily L₁ L₂
  let dims : Bool → ℕ := fun b => Bool.rec dim₂ dim₁ b
  let D : ∀ b, RationalFilteredNilmanifold (K b) degree (dims b) := fun b => by
    cases b
    · exact D₂.raiseStep hs₂
    · exact D₁.raiseStep hs₁
  let U : ∀ b, (D b).Niltest (fun _ : Unit => 1) := fun b => by
    cases b
    · exact B.raiseStep hs₂
    · exact A.raiseStep hs₁
  have hUc : ∀ b, (U b).ComplexityLE (raisedNiltestBudget p) := by
    intro b
    cases b
    · exact B.raiseStep_complexity hs₂ hp hBc
    · exact A.raiseStep_complexity hs₁ hp hAc
  have hU : ∀ b, (U b).UnitIntervalValued := by
    intro b
    cases b
    · exact B.raiseStep_unit_interval hs₂ hB
    · exact A.raiseStep_unit_interval hs₁ hA
  have hp' : 0 ≤ raisedNiltestBudget p := hp.trans (le_raisedNiltestBudget p)
  have hcard : (Fintype.card Bool : ℝ) ≤ raisedNiltestBudget p := by
    norm_num only [Fintype.card_bool, Nat.cast_ofNat]
    unfold raisedNiltestBudget
    nlinarith [sq_nonneg (p + 2)]
  let : FiniteDimensional ℚ (∀ b, K b) :=
    (RationalFilteredNilmanifold.productFinBasis D).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ b, K b))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ b, K b)) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ b, K b)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis D)
  let S := RationalFilteredNilmanifold.piNiltest D U hp' hcard hUc
  have hSc := RationalFilteredNilmanifold.piNiltest_complexity D U hp' hcard hUc
  have hSu := RationalFilteredNilmanifold.piNiltest_unit_interval D U hp' hcard hUc hU
  have heval (x : ZMod N) : S.evalCyclic N (fun _ : Unit => x) =
      A.evalCyclic N (fun _ : Unit => x) * B.evalCyclic N (fun _ : Unit => x) := by
    change (RationalFilteredNilmanifold.piNiltest D U hp' hcard hUc).eval
      (fun _ : Unit => (x.val : ℤ)) = _
    rw [RationalFilteredNilmanifold.piNiltest_eval, Fintype.prod_bool]
    change (A.raiseStep hs₁).eval (fun _ : Unit => (x.val : ℤ)) *
      (B.raiseStep hs₂).eval (fun _ : Unit => (x.val : ℤ)) = _
    rw [RationalFilteredNilmanifold.Niltest.raiseStep_eval,
      RationalFilteredNilmanifold.Niltest.raiseStep_eval]
    rfl
  refine .of_test (RationalFilteredNilmanifold.pi D) le_rfl S hSu hSc ?_
  intro x
  rw [heval, Complex.mul_re, (A.unit_interval_evalCyclic hA N (fun _ => x)).1,
    (B.unit_interval_evalCyclic hB N (fun _ => x)).1, zero_mul, sub_zero, hevalA x, hevalB x]

end Erdos3.PositiveCyclicNiltest

end

section

namespace Erdos3

open scoped TensorProduct

theorem exists_interval_circle_partition (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (N : ℕ) [NeZero N] {p ρ : ℝ},
      0 ≤ p → 0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : Fin n → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} 1 N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          ∀ j x y, 0 < A j x → 0 < A j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ := by
  obtain ⟨B, _, hpartition⟩ := RationalFilteredNilmanifold.exists_native_niltest_partition 1 a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + 1 + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p ρ hp hρ hρinv
  let D := RationalTorus.nilmanifold 1
  let G := RationalTorus.intervalOrbit N
  have hD : D.GeometryComplexityLE (p + 1) :=
    RationalTorus.nilmanifold_geometry 1 (by linarith) (by norm_num; linarith)
  have hρinv' : 1 / ρ ≤ Real.exp (((p + 1) + 2) ^ a) :=
    hρinv.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) _))
  obtain ⟨n, hn, hnb, tests, horbit, hunit, hcomplexity, hsum, hdiam⟩ :=
    hpartition D (fun _ : Unit => 1) (by linarith) hD hρ hρinv' G
  have hcost : (p + 1 + B) ^ B ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  let A : Fin n → ZMod N → ℝ := fun j x => ((tests j).evalCyclic N (fun _ : Unit => x)).re
  have heval (j : Fin n) (x : ZMod N) :
      A j x = ((tests j).observable (D.cyclicOrbitPoint G N (fun _ : Unit => x))).re := by
    change ((tests j).observable (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (tests j).orbit))).re = _
    rw [horbit j]
    rfl
  refine ⟨n, hn, hnb.trans (Real.exp_le_exp.mpr hcost), A, ?_, ?_, ?_⟩
  · intro j
    exact .of_test D le_rfl (tests j) (hunit j) ((hcomplexity j).mono hcost) (fun _ => rfl)
  · intro x
    simpa only [heval] using hsum (D.cyclicOrbitPoint G N (fun _ : Unit => x))
  · let := D.metricSpace
    intro j x y hx hy
    have hd := hdiam j _ _ ((heval j x) ▸ hx) ((heval j y) ▸ hy)
    have hp := RationalTorus.intervalCoordinate_lipschitz.dist_le_mul
      (D.cyclicOrbitPoint G N (fun _ : Unit => x)) (D.cyclicOrbitPoint G N (fun _ : Unit => y))
    change dist (RationalTorus.phaseProjection 1 (D.cyclicOrbitPoint G N (fun _ : Unit => x)) 0)
      (RationalTorus.phaseProjection 1 (D.cyclicOrbitPoint G N (fun _ : Unit => y)) 0) ≤
      (1 : ℝ) * dist (D.cyclicOrbitPoint G N (fun _ : Unit => x))
        (D.cyclicOrbitPoint G N (fun _ : Unit => y)) at hp
    rw [RationalTorus.intervalOrbit_phase, RationalTorus.intervalOrbit_phase, one_mul] at hp
    exact hp.trans hd

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

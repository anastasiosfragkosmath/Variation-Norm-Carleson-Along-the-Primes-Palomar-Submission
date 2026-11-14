/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/IdealInvariantNiltestBudget.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Topology.MetricSpace.Lipschitz
public import OAI.Combinatorics.Progressions.Estimates.InteriorIntervalCutoff
public import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

def UnitIntervalValued (T : D.Niltest w) : Prop :=
  ∀ z, (T.observable z).im = 0 ∧ 0 ≤ (T.observable z).re ∧ (T.observable z).re ≤ 1

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d n : ℕ}
  (D : RationalFilteredNilmanifold L s d) (I : LieIdeal ℚ L)
  (hI : D.filtration.layer (t + 1) ≤ I.toSubmodule)
  (Q : RationalFilteredNilmanifold (L ⧸ I) t n)
  (hQF : Q.filtration = D.filtration.quotientLie I hI)

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ I))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ I))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ I))] [T2Space (ℝ ⊗[ℚ] (L ⧸ I))]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {σ K Ξ : Type*} [LieRing K] [LieAlgebra ℚ K] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
  (D : RationalFilteredNilmanifold K s d) {w : σ → ℕ}

noncomputable def cyclicOrbitPoint
    (g : D.filtration.realification.PolynomialOrbit w)
    (N : ℕ) [NeZero N] (x : σ → ZMod N) : D.Space :=
  QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w
    (fun i => ((x i).val : ℤ)) g)

noncomputable def sectionNiltest
    (g : D.filtration.realification.PolynomialOrbit w) (F : D.Space → Ξ → ℝ)
    (hF : ∀ z a, 0 ≤ F z a ∧ F z a ≤ 1) (M : ℝ≥0)
    (hLip : let := D.metricSpace; ∀ a, LipschitzWith M (fun z => F z a))
    (a : Option Ξ) : D.Niltest w where
  orbit := g
  observable := fun z => (frozenRealSection F a z : ℂ)
  normBound := 1
  lipBound := M
  norm_le z := by
    have h := frozenRealSection_unit_interval F hF a z
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.1, NNReal.coe_one] using h.2
  lipschitz := by
    let := D.metricSpace
    apply LipschitzWith.of_dist_le_mul
    intro x y
    cases a with
    | none =>
      change dist (0 : ℂ) 0 ≤ (M : ℝ) * dist x y
      rw [dist_self]
      positivity
    | some a =>
      change dist (F x a : ℂ) (F y a : ℂ) ≤ (M : ℝ) * dist x y
      simpa only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real] using
        (hLip a).dist_le_mul x y

theorem sectionNiltest_unit_interval
    (g : D.filtration.realification.PolynomialOrbit w) (F : D.Space → Ξ → ℝ)
    (hF : ∀ z a, 0 ≤ F z a ∧ F z a ≤ 1) (M : ℝ≥0)
    (hLip : let := D.metricSpace; ∀ a, LipschitzWith M (fun z => F z a)) (a : Option Ξ) :
    (D.sectionNiltest g F hF M hLip a).UnitIntervalValued := by
  intro z
  exact ⟨rfl, frozenRealSection_unit_interval F hF a z⟩

theorem sectionNiltest_complexityLE
    (g : D.filtration.realification.PolynomialOrbit w) (F : D.Space → Ξ → ℝ)
    (hF : ∀ z a, 0 ≤ F z a ∧ F z a ≤ 1) (M : ℝ≥0)
    (hLip : let := D.metricSpace; ∀ a, LipschitzWith M (fun z => F z a))
    (a : Option Ξ) {p : ℝ} (hD : D.GeometryComplexityLE p)
    (hbudget : Real.log (3 + (M : ℝ)) ≤ p) :
    (D.sectionNiltest g F hF M hLip a).ComplexityLE p := by
  refine ⟨hD, ?_⟩
  change Real.log (2 + (1 : ℝ) + (M : ℝ)) ≤ p
  norm_num only [show (2 : ℝ) + 1 = 3 by norm_num]
  exact hbudget

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def withUnitBound (T : D.Niltest w) (hcap : ∀ x, ‖T.observable x‖ ≤ 1) : D.Niltest w :=
  { T with normBound := 1, norm_le := hcap }

theorem withUnitBound_complexity (T : D.Niltest w) (hcap : ∀ x, ‖T.observable x‖ ≤ 1)
    {p : ℝ} (hT : T.ComplexityLE p) : (T.withUnitBound hcap).ComplexityLE (p + 1) := by
  refine ⟨hT.1.mono D (by linarith), ?_⟩
  change Real.log (2 + 1 + (T.lipBound : ℝ)) ≤ p + 1
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  rw [Real.exp_add]
  have h := T.observable_budget hT
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_nonneg p)
  nlinarith [T.normBound.coe_nonneg, T.lipBound.coe_nonneg]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  (T : D.Niltest w) (hT : T.UnitIntervalValued)
  (psi : D.Space → ℝ) (hpsi : ∀ z, 0 ≤ psi z ∧ psi z ≤ 1)
  (K : ℝ≥0) (hLip : letI := D.metricSpace; LipschitzWith K psi)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

end OAI

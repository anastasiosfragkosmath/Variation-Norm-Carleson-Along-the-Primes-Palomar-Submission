/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/NiltestComplement.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.NativeEquivalenceTransitivity
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem realificationLieHom_id_apply {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (x : ℝ ⊗[ℚ] L) : realificationLieHom (LieHom.id : L →ₗ⁅ℚ⁆ L) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

namespace RationalFilteredNilmanifold

open Module
open scoped NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)

noncomputable def raiseStepProjection : (D.raiseStep hst).Space → D.Space :=
  cosetMap (D.raiseStep hst).realLattice D.realLattice
    (NilpotentLieBCHGroup.realificationMap
      (hnil := (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L))
    (NilpotentLieBCHGroup.realificationMap_subgroup (LieHom.id : L →ₗ⁅ℚ⁆ L)
      (D.raiseStep hst).lattice D.lattice (D.raiseStep_lattice_back hst))

theorem raiseStepProjection_mk (x : (D.raiseStep hst).RealGroup) :
    D.raiseStepProjection hst (QuotientGroup.mk x) =
      QuotientGroup.mk (NilpotentLieBCHGroup.realificationMap
        (hnil := (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L) x) := rfl

section Metric

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem raiseStepProjection_lipschitz :
    let := (D.raiseStep hst).metricSpace
    let := D.metricSpace
    LipschitzWith (coordinateLipschitzBound d d 1) (D.raiseStepProjection hst) := by
  let := realificationQuotientMetricSpace (D.raiseStep hst).basis (D.raiseStep hst).lattice
    (D.raiseStep hst).grid (D.raiseStep hst).grid_pos (D.raiseStep hst).outer_grid
  let := realificationQuotientMetricSpace D.basis D.lattice D.grid D.grid_pos D.outer_grid
  have hentry (k i : Fin d) :
      RationalHeightLE (D.basis.repr ((LieHom.id : L →ₗ⁅ℚ⁆ L) ((D.raiseStep hst).basis i)) k) 1 := by
    change RationalHeightLE (D.basis.repr (D.basis i) k) 1
    rw [Basis.repr_self]
    by_cases h : i = k <;> simp [h, RationalHeightLE]
  have h := NilpotentLieBCHGroup.lipschitz_realificationMap_quotient
    (D.raiseStep hst).basis D.basis (LieHom.id : L →ₗ⁅ℚ⁆ L)
    (D.raiseStep hst).lattice D.lattice (D.raiseStep_lattice_back hst)
    (D.raiseStep hst).grid D.grid (D.raiseStep hst).grid_pos D.grid_pos
    (D.raiseStep hst).outer_grid D.outer_grid 1 hentry
  exact h.weaken (by simp only [Fintype.card_fin, Nat.cast_one, le_refl])

end Metric

noncomputable def raiseStepRealOrbit {σ : Type*} {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) :
    (D.raiseStep hst).filtration.realification.PolynomialOrbit w :=
  NilpotentLieFiltration.polynomialOrbitOfLog g.log g.adapted

theorem raiseStepProjection_orbit {σ : Type*} {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    D.raiseStepProjection hst (QuotientGroup.mk
      ((D.raiseStep hst).filtration.realification.polynomialOrbitEval w x
        (D.raiseStepRealOrbit hst g))) =
      QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g) := by
  rw [D.raiseStepProjection_mk]
  apply congrArg (QuotientGroup.mk : D.RealGroup → D.Space)
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom (LieHom.id : L →ₗ⁅ℚ⁆ L)
    (VectorPolynomial.eval (fun i => (x i : ℚ)) g.log) =
      VectorPolynomial.eval (fun i => (x i : ℚ)) g.log
  exact realificationLieHom_id_apply _

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

def raisedNiltestBudget (p : ℝ) : ℝ := p + (p + 2) ^ 2 + 3

theorem le_raisedNiltestBudget (p : ℝ) : p ≤ raisedNiltestBudget p := by
  unfold raisedNiltestBudget
  nlinarith [sq_nonneg (p + 2)]

namespace RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def raiseStep (T : D.Niltest w) (hst : s ≤ t) : (D.raiseStep hst).Niltest w where
  orbit := D.raiseStepRealOrbit hst T.orbit
  observable := fun z => T.observable (D.raiseStepProjection hst z)
  normBound := T.normBound
  lipBound := T.lipBound * coordinateLipschitzBound d d 1
  norm_le z := T.norm_le _
  lipschitz := by
    let := (D.raiseStep hst).metricSpace
    let := D.metricSpace
    exact T.lipschitz.comp (D.raiseStepProjection_lipschitz hst)

theorem raiseStep_eval (T : D.Niltest w) (hst : s ≤ t) (x : σ → ℤ) :
    (T.raiseStep hst).eval x = T.eval x := by
  change T.observable (D.raiseStepProjection hst (QuotientGroup.mk
    ((D.raiseStep hst).filtration.realification.polynomialOrbitEval w x
      (D.raiseStepRealOrbit hst T.orbit)))) = T.eval x
  rw [D.raiseStepProjection_orbit]
  rfl

theorem raiseStep_evalCyclic (T : D.Niltest w) (hst : s ≤ t)
    (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    (T.raiseStep hst).evalCyclic N x = T.evalCyclic N x :=
  T.raiseStep_eval hst _

theorem raiseStep_unit_interval (T : D.Niltest w) (hst : s ≤ t) (hT : T.UnitIntervalValued) :
    (T.raiseStep hst).UnitIntervalValued := fun z => hT (D.raiseStepProjection hst z)

theorem raiseStep_complexity (T : D.Niltest w) (hst : s ≤ t) {p : ℝ}
    (hp : 0 ≤ p) (hT : T.ComplexityLE p) :
    (T.raiseStep hst).ComplexityLE (raisedNiltestBudget p) := by
  refine ⟨GeometryComplexityLE.mono (D.raiseStep hst)
    (D.raiseStep_geometry hst hT.1) (le_raisedNiltestBudget p), ?_⟩
  have hraw := T.observable_budget hT
  have hn : (T.normBound : ℝ) ≤ Real.exp p := by linarith [T.lipBound.coe_nonneg]
  have hl : (T.lipBound : ℝ) ≤ Real.exp p := by linarith [T.normBound.coe_nonneg]
  have hK := coordinateLipschitzBound_le_exp d d 1 hp hT.1.1 hT.1.1
    (by simpa using Real.one_le_exp_iff.mpr hp)
  have hn' : (T.normBound : ℝ) ≤ Real.exp (p + (p + 2) ^ 2) :=
    hn.trans (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (p + 2)]))
  have hl' : (T.lipBound : ℝ) * (coordinateLipschitzBound d d 1 : ℝ) ≤
      Real.exp (p + (p + 2) ^ 2) := by
    rw [Real.exp_add]
    exact mul_le_mul hl hK (by positivity) (Real.exp_nonneg _)
  have hone : 1 ≤ Real.exp (p + (p + 2) ^ 2) := Real.one_le_exp_iff.mpr (by positivity)
  have hfour : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hsum : 2 + (T.normBound : ℝ) +
      (T.lipBound : ℝ) * (coordinateLipschitzBound d d 1 : ℝ) ≤
        Real.exp (raisedNiltestBudget p) := by
    calc
      _ ≤ 4 * Real.exp (p + (p + 2) ^ 2) := by linarith
      _ ≤ Real.exp 3 * Real.exp (p + (p + 2) ^ 2) :=
        mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; unfold raisedNiltestBudget; ring
  change Real.log (2 + (T.normBound : ℝ) +
    (T.lipBound : ℝ) * (coordinateLipschitzBound d d 1 : ℝ)) ≤ raisedNiltestBudget p
  exact (Real.log_le_iff_le_exp (by positivity)).mpr hsum

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem raiseStep_top_vertical (T : D.Niltest w) (hst : s < t)
    (z : (D.raiseStep hst.le).RealGroup)
    (hz : z ∈ (D.raiseStep hst.le).filtration.realification.subgroup t)
    (x : (D.raiseStep hst.le).Space) :
    (T.raiseStep hst.le).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (0 : L →ₗ[ℚ] ℚ) z.coord : ℝ) : CircleFourier.Circle) *
          (T.raiseStep hst.le).observable x := by
  have hz' : z = 1 := by
    apply NilpotentLieBCHGroup.ext
    change z.coord = 0
    change z.coord ∈ D.filtration.realification.layer t at hz
    simpa only [D.filtration.realification.layer_eq_bot_above_step hst,
      Submodule.mem_bot] using hz
  subst z
  simp

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t n : ℕ}

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

universe u

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

inductive PositiveCyclicNiltest.{u} (degree N : ℕ) [NeZero N] (p : ℝ)
    (f : ZMod N → ℝ) : Prop where
  | of_test {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s dim : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s dim) (hdegree : s ≤ degree)
      (T : D.Niltest (fun _ : Unit => 1)) (hpositive : T.UnitIntervalValued)
      (hcomplexity : T.ComplexityLE p)
      (heval : ∀ x, f x = (T.evalCyclic N (fun _ => x)).re) :
      PositiveCyclicNiltest degree N p f

namespace PositiveCyclicNiltest

universe u

theorem unit_interval {degree N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℝ}
    (hf : PositiveCyclicNiltest.{u} degree N p f) (x : ZMod N) :
    0 ≤ f x ∧ f x ≤ 1 := by
  rcases hf with ⟨D, hs, T, hT, hTc, heval⟩
  rw [heval]
  exact (T.unit_interval_evalCyclic hT N (fun _ => x)).2

theorem mono {degree degree' N : ℕ} [NeZero N] {p p' : ℝ} {f : ZMod N → ℝ}
    (hf : PositiveCyclicNiltest.{u} degree N p f) (hdegree : degree ≤ degree')
    (hp : p ≤ p') : PositiveCyclicNiltest.{u} degree' N p' f := by
  rcases hf with ⟨D, hs, T, hT, hTc, heval⟩
  exact .of_test D (hs.trans hdegree) T hT (hTc.mono hp) heval

end PositiveCyclicNiltest
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

universe u

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

end OAI

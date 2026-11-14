/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/CubicAntisymmetricTransfer.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.NativeBinaryAssignments
public import OAI.Combinatorics.Progressions.Geometry.ComparisonProductMetric
public import OAI.Combinatorics.Progressions.Geometry.MissingCoordinateErrorAbsorption
public import OAI.Combinatorics.Progressions.Geometry.NativeCoordinatePairs
public import OAI.Combinatorics.Progressions.Polynomial.BoundedRootDegreeEquivalence
@[expose] public section

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem topInvariant_integer_expansion_of_step {L σ : Type}
    [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s t d : ℕ} (ht : t = s + 1) (D : RationalFilteredNilmanifold L t d)
    {w : σ → ℕ} (T : D.Niltest w) {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    (hinv : ∀ z ∈ D.filtration.realification.subgroup t, ∀ x,
      T.observable (z • x) = T.observable x) :
    Nonempty (NativeIntegerExpansion w s
      ((p + topInvariantIntegerExponent s) ^ topInvariantIntegerExponent s) T.eval) := by
  subst t
  exact topInvariant_integer_expansion D T hp hT hinv

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {σ : Type} {L I : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] [Fintype I]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) {p q v : ℝ}
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  (V : D.UnitVerticalObservable (D.filtration.realification.subgroup s) I v)
  (U : M.SymmetricSquarefreeUnitData p V.frequency q)
  (E : RationalFilteredNilmanifold
    (M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))
    (max s (Fintype.card (ReplicatedIndex bound))) r)
  (hEL : E.lattice = M.comparisonLattice p U.grid U.grid_pos U.stable)

theorem comparisonVerticalProduct_top_invariant (hstep : s = ∑ i, bound i)
    (hEF : E.filtration = M.filtration.comparisonFiltration (fun j : ReplicatedIndex bound => j.1))
    (ε : D.RealGroup) (a : Fin (multidegreeFactorial bound) → I)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount))
    (z : E.RealGroup) (hz : z ∈ E.filtration.realification.subgroup
      (max s (Fintype.card (ReplicatedIndex bound)))) (x : E.Space) :
    M.comparisonVerticalProduct V U E hEL ε a k (z • x) =
      M.comparisonVerticalProduct V U E hEL ε a k x := by
  let π := fun j : ReplicatedIndex bound => j.1
  have hcard : Fintype.card (ReplicatedIndex bound) = s := (replicatedIndex_card bound).trans hstep.symm
  have hzF : z.coord ∈ (M.filtration.comparisonFiltration π).realification.layer s := by
    have hh : z.coord ∈ E.filtration.realification.layer s :=
      E.filtration.realification.antitone (le_max_left s _) hz
    simpa only [hEF] using hh
  let z₁ : D.RealGroup := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot) (M.filtration.comparisonFirst π) z
  let z₂ : (M.squarefreeModel p U.grid U.grid_pos U.stable).RealGroup :=
    realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := (M.squarefreeModel p U.grid U.grid_pos U.stable).filtration.lowerCentralSeries_eq_bot)
      (M.filtration.comparisonSecond π) z
  have hz₁ : z₁ ∈ D.filtration.realification.subgroup s := by
    change realificationLieHom (M.filtration.comparisonFirst π) z.coord ∈ D.filtration.realification.layer s
    rw [← M.ordinary]
    exact M.filtration.comparisonFirst_real_mem_layer π s z.coord hzF
  have hz₂ : z₂ ∈ (M.squarefreeModel p U.grid U.grid_pos U.stable).filtration.realification.subgroup
      (Fintype.card (ReplicatedIndex bound)) := by
    change realificationLieHom (M.filtration.comparisonSecond π) z.coord ∈
      (M.filtration.squarefreeOrdinaryFiltration π).realification.layer (Fintype.card (ReplicatedIndex bound))
    rw [congrArg (fun n => (M.filtration.squarefreeOrdinaryFiltration π).realification.layer n) hcard]
    exact M.filtration.comparisonSecond_real_mem_layer π s z.coord hzF
  have hfreq : realifyFunctional (V.tensorPower (multidegreeFactorial bound)).frequency z₁.coord =
      realifyFunctional U.observable.frequency z₂.coord := by
    change realifyFunctional (multidegreeFactorial bound • V.frequency)
      (realificationLieHom (M.filtration.comparisonFirst π) z.coord) =
      realifyFunctional U.observable.frequency (realificationLieHom (M.filtration.comparisonSecond π) z.coord)
    rw [realifyFunctional_nsmul, U.frequency, nsmul_eq_mul]
    exact M.filtration.realComparisonTop_frequency hstep V.frequency hzF
  have hcomm : Commute z₁ ε := commute_of_lie_eq_zero z₁ ε
    (D.filtration.realification.top_layer_central hz₁ ε.coord)
  have hswap (y : D.Space) : ε • (z₁ • y) = z₁ • (ε • y) := by
    rw [← mul_smul, ← hcomm.eq, mul_smul]
  let c := CircleFourier.character ((realifyFunctional U.observable.frequency z₂.coord : ℝ) : CircleFourier.Circle)
  have hc : c * star c = 1 := by
    change CircleFourier.character ((realifyFunctional U.observable.frequency z₂.coord : ℝ) : CircleFourier.Circle) *
      star (CircleFourier.character ((realifyFunctional U.observable.frequency z₂.coord : ℝ) : CircleFourier.Circle)) = 1
    rw [← CircleFourier.character_neg, ← CircleFourier.character_add,
      add_neg_cancel, CircleFourier.character_zero]
  unfold comparisonVerticalProduct
  rw [M.comparisonFirstSpace_smul, M.comparisonSecondSpace_smul]
  change (V.tensorPower (multidegreeFactorial bound)).observable a
    (ε • (z₁ • M.comparisonFirstSpace p U.grid U.grid_pos U.stable E hEL x)) *
    star (U.observable.observable k (z₂ • M.comparisonSecondSpace p U.grid U.grid_pos U.stable E hEL x)) = _
  rw [hswap, (V.tensorPower (multidegreeFactorial bound)).vertical a z₁ hz₁,
    U.observable.vertical k z₂ hz₂, hfreq, star_mul]
  let u := (V.tensorPower (multidegreeFactorial bound)).observable a
    (ε • M.comparisonFirstSpace p U.grid U.grid_pos U.stable E hEL x)
  let w := U.observable.observable k (M.comparisonSecondSpace p U.grid U.grid_pos U.stable E hEL x)
  change (c * u) * (star w * star c) = u * star w
  calc
    _ = (c * star c) * (u * star w) := by ring
    _ = _ := by rw [hc, one_mul]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData

open scoped TensorProduct

theorem exists_nilcharacter {σ L : Type} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
    {M : D.MultidegreeStructure bound} {p q : ℝ} {η : L →ₗ[ℚ] ℚ}
    [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
    [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
    (U : M.SymmetricSquarefreeUnitData p η q)
    (g : M.filtration.realification.PolynomialOrbit) :
    ∃ W : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex bound => 1) q,
    ∃ e : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound))
        (Fin U.coordinateCount) ≃ Fin W.outputDim,
      W.dim = Fintype.card M.SquarefreeBasisIndex ∧
      (∀ k x, W.eval (e k) x = U.eval g k x) ∧
      ∀ (a : ReplicatedPermutation bound) k x,
        W.eval k (fun j => x ((replicatedPermutation bound a).symm j)) = W.eval k x := by
  classical
  obtain ⟨W, e, hdim, heval⟩ := NativeMultidegreeNilcharacter.exists_of_unit_data
    (M.squarefreeModel p U.grid U.grid_pos U.stable)
    (M.squarefreeModelMultidegree p U.grid U.grid_pos U.stable)
    (by simp) U.complexity
    (M.filtration.polarizeRealOrbit (fun j : ReplicatedIndex bound => j.1) g)
    U.observable U.dimension
  change ∀ k x, W.eval (e k) x = U.eval g k x at heval
  refine ⟨W, e, hdim, heval, ?_⟩
  intro a k x
  have h (y : ReplicatedIndex bound → ℤ) : W.eval k y = U.eval g (e.symm k) y := by
    simpa only [Equiv.apply_symm_apply] using heval (e.symm k) y
  rw [h, h, U.eval_permute]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct BigOperators NNReal

variable {σ L : Type} {I : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] [Fintype I]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) {p q v : ℝ}
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  (V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1)) I v)
  (U : M.SymmetricSquarefreeUnitData p V.frequency q)
  (E : RationalFilteredNilmanifold
    (M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))
    (max (s + 1) (Fintype.card (ReplicatedIndex bound))) r)
  (hEL : E.lattice = M.comparisonLattice p U.grid U.grid_pos U.stable)
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]

include hEL in
theorem comparison_diagonal_expansion
    (hstep : s + 1 = ∑ i, bound i)
    (hEF : E.filtration = M.filtration.comparisonFiltration (fun j : ReplicatedIndex bound => j.1))
    {R : ℝ} (hR : 0 ≤ R) (hD : D.GeometryComplexityLE R) (hE : E.GeometryComplexityLE R)
    (hv : v ≤ R) (hq : q ≤ R)
    (hfirst : ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ R)
    (hsecond : ∀ j k, rationalLogHeight ((M.squarefreeFinBasis p).repr (E.basis j).val.2 k) ≤ R)
    (hc : (multidegreeFactorial bound : ℝ) ≤ Real.exp R)
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup) (A : ℝ≥0)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ)
    (hA : (A : ℝ) ≤ Real.exp R)
    (hε : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x))
    (a : Fin (multidegreeFactorial bound) → I)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount)) :
    Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s (comparisonDescentBudget s R)
      (fun x => (∏ j, V.observable (a j) (QuotientGroup.mk
          (M.filtration.realification.polynomialOrbitEval x g))) *
        star (U.eval (M.filtration.realification.normalizeMultidegreeOrbit g ε γ) k (fun j => x j.1)))) := by
  let := E.metricSpace
  obtain ⟨h, _, hdiag⟩ := M.exists_normalized_comparison_orbit p U.grid U.grid_pos U.stable
    E hEF hEL g ε γ hγ hfactor
  let K := comparisonProductLip (multidegreeFactorial bound) V.lipBound U.observable.lipBound A R
  have hLip : LipschitzWith K (M.comparisonVerticalProduct V U E hEL ε a k) :=
    M.comparisonVerticalProduct_lipschitz V U E hEL hR hD
      (U.complexity.1.mono _ hq) hE hfirst hsecond ε A hε a k
  let T : E.Niltest (fun _ : σ => 1) := {
    orbit := h
    observable := M.comparisonVerticalProduct V U E hEL ε a k
    normBound := 1
    lipBound := K
    norm_le := M.comparisonVerticalProduct_norm V U E hEL ε a k
    lipschitz := hLip }
  have hK : (K : ℝ) ≤ Real.exp ((R + 3) ^ 2 + 3 * R + 1) :=
    comparisonProductLip_le_exp _ _ _ _ hR hc
      (V.lip_bound.trans (Real.exp_le_exp.mpr hv))
      (U.observable.lip_bound.trans (Real.exp_le_exp.mpr hq)) hA
  have hcost : 0 ≤ comparisonProductCost R := by dsimp [comparisonProductCost]; positivity
  have hT : T.ComplexityLE (comparisonProductCost R) := by
    refine ⟨hE.mono E ?_, ?_⟩
    · dsimp [comparisonProductCost]
      nlinarith [sq_nonneg (R + 3)]
    · have hh := niltest_log_bound_of_exp (1 : ℝ≥0) K (a := 0)
        (b := (R + 3) ^ 2 + 3 * R + 1) (by norm_num) (by positivity) (by simp) hK
      simp only [NNReal.coe_one, zero_add] at hh
      change Real.log (2 + (1 : ℝ) + K) ≤ comparisonProductCost R
      dsimp [comparisonProductCost]
      linarith
  have heq : max (s + 1) (Fintype.card (ReplicatedIndex bound)) = s + 1 := by
    rw [replicatedIndex_card, ← hstep, max_self]
  have hexp : Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s
      (comparisonDescentBudget s R) T.eval) :=
    topInvariant_integer_expansion_of_step heq E T hcost hT
      (fun z hz x => M.comparisonVerticalProduct_top_invariant V U E hEL hstep hEF ε a k z hz x)
  have heval : T.eval = (fun x => (∏ j, V.observable (a j) (QuotientGroup.mk
        (M.filtration.realification.polynomialOrbitEval x g))) *
      star (U.eval (M.filtration.realification.normalizeMultidegreeOrbit g ε γ) k (fun j => x j.1))) := by
    funext x
    change M.comparisonVerticalProduct V U E hEL ε a k
      (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval _ x h)) = _
    unfold comparisonVerticalProduct
    rw [(hdiag x).1, (hdiag x).2]
    rfl
  exact heval ▸ hexp

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct BigOperators NNReal

variable {σ L : Type} {I : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] [Fintype I]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) {p q v : ℝ}
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  (V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1)) I v)
  (U : M.SymmetricSquarefreeUnitData p V.frequency q)
  (E : RationalFilteredNilmanifold
    (M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))
    (max (s + 1) (Fintype.card (ReplicatedIndex bound))) r)
  (hEL : E.lattice = M.comparisonLattice p U.grid U.grid_pos U.stable)
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]

include hEL in
theorem comparison_diagonal_equivalence
    (hstep : s + 1 = ∑ i, bound i)
    (hEF : E.filtration = M.filtration.comparisonFiltration (fun j : ReplicatedIndex bound => j.1))
    {R : ℝ} (hR : 0 ≤ R) (hD : D.GeometryComplexityLE R) (hE : E.GeometryComplexityLE R)
    (hv : v ≤ R) (hq : q ≤ R)
    (hfirst : ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ R)
    (hsecond : ∀ j k, rationalLogHeight ((M.squarefreeFinBasis p).repr (E.basis j).val.2 k) ≤ R)
    (hc : (multidegreeFactorial bound : ℝ) ≤ Real.exp R)
    (hI : (Fintype.card I : ℝ) ≤ Real.exp R)
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup) (A : ℝ≥0)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ)
    (hA : (A : ℝ) ≤ Real.exp R)
    (hε : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) :
    NativeIntegerVectorEquivalence s (comparisonEquivalenceBudget s R)
      (fun (a : Fin (multidegreeFactorial bound) → I) x =>
        ∏ j, V.observable (a j) (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)))
      (fun k x => U.eval (M.filtration.realification.normalizeMultidegreeOrbit g ε γ) k (fun j => x j.1)) := by
  obtain ⟨hdesc, hbase, htensor⟩ := comparisonEquivalenceBudget_bounds s hR
  refine ⟨?_, U.dimension.trans ((Real.exp_le_exp.mpr hq).trans (Real.exp_le_exp.mpr hbase)), ?_⟩
  · have hfac : multidegreeFactorial bound ≤ (s + 1).factorial := by
      simpa only [← hstep] using multidegreeFactorial_le_total bound
    have hfacR : (multidegreeFactorial bound : ℝ) ≤ (s + 1).factorial := by exact_mod_cast hfac
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp R) ^ multidegreeFactorial bound :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hI _
      _ = Real.exp ((multidegreeFactorial bound : ℝ) * R) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (((s + 1).factorial : ℝ) * R) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hfacR hR)
      _ ≤ _ := Real.exp_le_exp.mpr htensor
  · intro a k
    obtain ⟨F⟩ := M.comparison_diagonal_expansion V U E hEL hstep hEF hR hD hE hv hq
      hfirst hsecond hc g ε γ A hγ hfactor hA hε a k
    exact ⟨F.mono hdesc⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped TensorProduct BigOperators

theorem exists_controlled_diagonal_comparison (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type} {I : Type*}
      [Fintype σ] [Fintype I] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {t d : ℕ} {bound : σ → ℕ} (D : RationalFilteredNilmanifold L t d)
      (M : D.MultidegreeStructure bound), (∑ i, bound i) = t → t = s + 1 →
      ∀ {p : ℝ}, M.ComplexityLE p →
      ∀ (V : D.UnitVerticalObservable (D.filtration.realification.subgroup t) I p),
      (Fintype.card I : ℝ) ≤ Real.exp p → ∀ g : M.filtration.realification.PolynomialOrbit,
      let P := p + (s + 1).factorial + 1
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))
      letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :=
        IsModuleTopology.isTopologicalAddGroup ℝ _
      letI : T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :=
        realification_moduleTopology_t2 (M.squarefreeFinBasis P)
      ∃ U : M.SymmetricSquarefreeUnitData P V.frequency ((p + C) ^ C),
      ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
        M.filtration.realification.polynomialOrbitEval 0 g = ε * γ ∧
        NativeIntegerVectorEquivalence s ((p + C) ^ C)
          (fun (a : Fin (multidegreeFactorial bound) → I) x =>
            ∏ j, V.observable (a j) (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)))
          (fun k x => U.eval (M.filtration.realification.normalizeMultidegreeOrbit g ε γ) k (fun j => x j.1)) := by
  obtain ⟨a, _, hsymm⟩ := exists_controlled_symmetric_squarefree_unit (s + 1)
  obtain ⟨b, _, hnormal⟩ := exists_controlled_group_normalization (s + 1)
  obtain ⟨c, _, hequivalence⟩ := exists_comparisonEquivalence_cost s
  let X : Polynomial ℕ := Polynomial.X
  let P₀ := X + Polynomial.C (s + 1).factorial + 1
  let Q₀ := (X + Polynomial.C a) ^ a
  let H₀ := P₀ + 1 + Polynomial.C ((s + 1) ^ 2)
  let G₀ := ((P₀ + Q₀ + 4) ^ 2 + H₀ + 6) ^ 11
  let N₀ := (X + Polynomial.C b) ^ b
  let R₀ := X + P₀ + Q₀ + H₀ + G₀ + N₀ + Polynomial.C (s + 1).factorial + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R₀ + Q₀ + (R₀ + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro σ L I _ _ _ _ _ _ _ _ t d bound D M hs ht p hM V hI g
  subst ht
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let P := p + (s + 1).factorial + 1
  let Q := (p + a) ^ a
  let H := comparisonBasisBudget (s + 1) P
  let G := comparisonGeometryBudget (s + 1) P Q
  let N := (p + b) ^ b
  let R := p + P + Q + H + G + N + (s + 1).factorial + 1
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hH : 0 ≤ H := by dsimp [H, comparisonBasisBudget]; positivity
  have hG : 0 ≤ G := by dsimp [G, comparisonGeometryBudget]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hF : 0 ≤ ((s + 1).factorial : ℝ) := Nat.cast_nonneg _
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hpP : p ≤ P := by dsimp [P]; linarith
  have hpR : p ≤ R := by dsimp [R]; linarith
  have hQR : Q ≤ R := by dsimp [R]; linarith
  have hHR : H ≤ R := by dsimp [R]; linarith
  have hGR : G ≤ R := by dsimp [R]; linarith
  have hNR : N ≤ R := by dsimp [R]; linarith
  have hFR : ((s + 1).factorial : ℝ) ≤ R := by dsimp [R]; linarith
  let := moduleTopology ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :=
    realification_moduleTopology_t2 (M.squarefreeFinBasis P)
  obtain ⟨U⟩ := hsymm D M hs hM V.frequency V.height
  obtain ⟨E, hEF, hEL, hE, he⟩ := M.exists_comparison_model (hM.mono M hpP)
    U.grid U.grid_pos U.stable U.complexity.1
  rw [hs] at hE he
  let K := M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 E.basis
  obtain ⟨ε, γ, A, hγ, hfactor, _, hA, hε⟩ := hnormal D p hp hM.1
    (M.filtration.realification.polynomialOrbitEval 0 g)
  have hfirst (j k) : rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ R := by
    have hh := (he j (Sum.inl k)).trans hHR
    simpa only [Basis.prod_repr_inl] using hh
  have hsecond (j k) : rationalLogHeight ((M.squarefreeFinBasis P).repr (E.basis j).val.2 k) ≤ R := by
    have hh := (he j (Sum.inr k)).trans hHR
    simpa only [Basis.prod_repr_inr] using hh
  have hc : (multidegreeFactorial bound : ℝ) ≤ Real.exp R := by
    have hh : multidegreeFactorial bound ≤ (s + 1).factorial := by
      simpa only [hs] using multidegreeFactorial_le_total bound
    exact (Nat.cast_le.mpr hh).trans (hFR.trans (by linarith [Real.add_one_le_exp R]))
  have hcompare := M.comparison_diagonal_equivalence V U E hEL hs.symm hEF hR
    (hM.1.mono D hpR) (hE.mono E hGR) hpR hQR hfirst hsecond hc
    (hI.trans (Real.exp_le_exp.mpr hpR)) g ε γ A hγ hfactor
    (hA.trans (Real.exp_le_exp.mpr hNR)) hε
  have htotal : R + Q + (R + c) ^ c ≤ (p + C) ^ C := by
    simpa [R₀, G₀, H₀, N₀, P₀, Q₀, X, R, G, H, N, P, Q,
      comparisonGeometryBudget, comparisonBasisBudget, Polynomial.eval₂_pow] using hbudget p hp
  have hRc : 0 ≤ (R + c) ^ c := by positivity
  have hQC : Q ≤ (p + C) ^ C := by linarith
  have hcompareC : comparisonEquivalenceBudget s R ≤ (p + C) ^ C :=
    (hequivalence R hR).trans (by linarith)
  exact ⟨U.mono hQC, ε, γ, hγ, hfactor, hcompare.mono hcompareC⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open Module
open RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_factorial_diagonal (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type} [Fintype σ] (bound : σ → ℕ),
      (∑ i, bound i) = s + 1 → ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
      ∃ V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex bound => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.dim ∧
        (∀ (e : ReplicatedPermutation bound) k x,
          V.eval k (fun j => x ((replicatedPermutation bound e).symm j)) = V.eval k x) ∧
        NativeIntegerVectorEquivalence s ((p + C) ^ C)
          (tensorVector W.eval (multidegreeFactorial bound))
          (fun k x => V.eval k (fun j => x j.1)) := by
  obtain ⟨C, hC, hcompare⟩ := exists_controlled_diagonal_comparison s
  refine ⟨C, hC, ?_⟩
  intro σ _ bound hs p W
  classical
  let T : W.model.UnitVerticalObservable
      (W.model.filtration.realification.subgroup (∑ i, bound i)) (Fin W.outputDim) p :=
    { W.vertical with
      vertical := fun i z hz x => W.vertical.vertical i z (W.multi.realSubgroup_top.symm ▸ hz) x
      integral := fun z hz hL => W.vertical.integral z (W.multi.realSubgroup_top.symm ▸ hz) hL }
  let P := p + (s + 1).factorial + 1
  let := moduleTopology ℝ (ℝ ⊗[ℚ] W.multi.filtration.SquarefreeAlgebra
    (fun j : ReplicatedIndex bound => j.1))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] W.multi.filtration.SquarefreeAlgebra
      (fun j : ReplicatedIndex bound => j.1)) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] W.multi.filtration.SquarefreeAlgebra
      (fun j : ReplicatedIndex bound => j.1)) :=
    realification_moduleTopology_t2 (W.multi.squarefreeFinBasis P)
  obtain ⟨U, ε, γ, _, _, hE⟩ := hcompare W.model W.multi rfl hs W.complexity T
    (by simpa only [Fintype.card_fin] using W.output_bound) W.orbit
  obtain ⟨V, e, hdim, heval, hsymm⟩ := U.exists_nilcharacter
    (W.multi.filtration.realification.normalizeMultidegreeOrbit W.orbit ε γ)
  refine ⟨V, ?_, hsymm, ?_⟩
  · rw [hdim]
    simpa only [hs] using W.multi.squarefreeBasisIndex_card_le P
  refine hE.of_coordinate_maps _ _ id e.symm (fun _ _ => rfl) ?_ hE.left_dimension ?_ le_rfl
  · intro k x
    simpa only [Equiv.apply_symm_apply] using heval (e.symm k) (fun j => x j.1)
  · simpa only [Fintype.card_fin] using V.output_bound

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_symmetric_multilinearization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type} [Fintype σ] (bound : σ → ℕ),
      (∑ i, bound i) = s + 1 → ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
      ∃ V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex bound => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.dim ∧
        (∀ (e : ReplicatedPermutation bound) k x,
          V.eval k (fun j => x ((replicatedPermutation bound e).symm j)) = V.eval k x) ∧
        NativeIntegerVectorEquivalence s ((p + C) ^ C)
          W.eval (fun k x => V.eval k (fun j => x j.1)) := by
  obtain ⟨a, _, hroot⟩ := exists_bounded_root_degree_equivalence s (s + 1).factorial
  obtain ⟨b, _, hdiagonal⟩ := exists_factorial_diagonal s
  obtain ⟨c, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  let A₀ := (X + Polynomial.C a) ^ a
  let B₀ := (A₀ + Polynomial.C b) ^ b
  let R₀ := A₀ + B₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (B₀ + (R₀ + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro σ _ bound hs p W
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : multidegreeFactorial bound ≤ (s + 1).factorial := by
    simpa only [hs] using multidegreeFactorial_le_total bound
  obtain ⟨R, hRdim, hER⟩ := hroot (multidegreeFactorial_pos bound) hq bound hs W
  obtain ⟨V, hVdim, hsymm, hEV⟩ := hdiagonal bound hs R
  let A := (p + a) ^ a
  let B := (A + b) ^ b
  let r := A + B
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hr : 0 ≤ r := add_nonneg hA hB
  have hAr : A ≤ r := le_add_of_nonneg_right hB
  have hBr : B ≤ r := le_add_of_nonneg_left hA
  have hE := htrans hr (hER.mono hAr) (hEV.mono hBr)
    (tensorVector_unit R.eval R.unit_eval (multidegreeFactorial bound))
  have hb : B + (r + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, A₀, B₀, R₀, A, B, r, Polynomial.eval₂_pow] using hbudget p hp
  have hc : 0 ≤ (r + c) ^ c := by positivity
  have hBC : B ≤ (p + C) ^ C := by linarith
  have hEC : (r + c) ^ c ≤ (p + C) ^ C := by linarith
  exact ⟨V.mono hBC, hRdim ▸ hVdim, hsymm, hE.mono hEC⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

abbrev CubicReplicatedIndex := ReplicatedIndex (mixedCorrelationDegree 2)

def cubicLeftReplica : CubicReplicatedIndex := ⟨1, ⟨0, by decide⟩⟩

def cubicTrilinearInput (h u v : ℤ) (j : CubicReplicatedIndex) : ℤ :=
  if j.1 = 0 then h else if j.2.val = 0 then u else v

namespace NativeMultidegreeNilcharacter

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff
  NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem map_correlationInput {A B : Type*} (g : A → B) (h n : A) :
    (fun i => g (correlationInput h n i)) = correlationInput (g h) (g n) := by
  funext i
  fin_cases i <;> rfl

namespace NativeCorrelationStructure

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

theorem mixed_correlation_transfer {K : Type*} [Fintype K] {q : ℝ}
    {eta : K → (Fin 2 → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s q W.mixed.eval eta)
    (hunit : ∀ x, ∑ k, ‖eta k x‖ ^ 2 = 1) (h : W.shifts) :
    ∃ (k : K) (a : Fin (E.selectedExpansion (W.selectedWitness h).coordinate.1 k).count),
      Real.exp (-(p + 2 * q)) ≤
        ‖𝔼 x, multiplicativeDerivative f h.val x * star
          (eta k (correlationInput (h.val.val : ℤ) (x.val : ℤ)) *
            W.family.evalCyclic N (W.selectedWitness h).coordinate.2 h.val x *
            (W.selectedWitness h).test.evalCyclic N (fun _ => x) *
            ((E.selectedExpansion (W.selectedWitness h).coordinate.1 k).test a).eval
              (correlationInput (h.val.val : ℤ) (x.val : ℤ)))‖ := by
  have hinput (x : ZMod N) :
      (fun i => ((correlationInput h.val x i).val : ℤ)) =
        correlationInput (h.val.val : ℤ) (x.val : ℤ) :=
    map_correlationInput (fun z : ZMod N => (z.val : ℤ)) h.val x
  have hcorr : Real.exp (-p) ≤
      ‖𝔼 x, (multiplicativeDerivative f h.val x *
          star (W.family.evalCyclic N (W.selectedWitness h).coordinate.2 h.val x) *
          star ((W.selectedWitness h).test.evalCyclic N (fun _ => x))) *
        star (W.mixed.eval (W.selectedWitness h).coordinate.1
          (correlationInput (h.val.val : ℤ) (x.val : ℤ)))‖ := by
    simpa only [nativeCorrelationResidual, NativeMultidegreeNilcharacter.evalCyclic,
      hinput, mul_assoc, mul_left_comm, mul_comm]
      using (W.selectedWitness h).correlation
  obtain ⟨k, a, hka⟩ := E.transfer_sample_correlation Finset.univ
    (fun x : ZMod N => correlationInput (h.val.val : ℤ) (x.val : ℤ))
    (W.selectedWitness h).coordinate.1
    (fun x => multiplicativeDerivative f h.val x *
      star (W.family.evalCyclic N (W.selectedWitness h).coordinate.2 h.val x) *
      star ((W.selectedWitness h).test.evalCyclic N (fun _ => x)))
    (fun x _ => hunit _) hcorr
  refine ⟨k, a, ?_⟩
  simpa only [star_mul, mul_assoc, mul_left_comm, mul_comm] using hka

end NativeCorrelationStructure

theorem exists_multilinearized_correlation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f),
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        ∃ E : NativeIntegerVectorEquivalence s ((p + C) ^ C)
            W.mixed.eval (fun k x => V.eval k (fun j => x j.1)),
          ∀ h : W.shifts,
            ∃ (k : Fin V.outputDim)
              (a : Fin (E.selectedExpansion (W.selectedWitness h).coordinate.1 k).count),
              Real.exp (-(p + 2 * (p + C) ^ C)) ≤
                ‖𝔼 x, multiplicativeDerivative f h.val x * star
                  (V.eval k (fun j => correlationInput (h.val.val : ℤ) (x.val : ℤ) j.1) *
                    W.family.evalCyclic N (W.selectedWitness h).coordinate.2 h.val x *
                    (W.selectedWitness h).test.evalCyclic N (fun _ => x) *
                    ((E.selectedExpansion (W.selectedWitness h).coordinate.1 k).test a).eval
                      (correlationInput (h.val.val : ℤ) (x.val : ℤ)))‖ := by
  obtain ⟨C, hC, hmulti⟩ := NativeMultidegreeNilcharacter.exists_symmetric_multilinearization s
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W
  have hsum : (∑ i, mixedCorrelationDegree s i) = s + 1 := by
    rw [Fin.sum_univ_two]
    change 1 + s = s + 1
    omega
  obtain ⟨V, hdim, hsymm, E⟩ := hmulti (mixedCorrelationDegree s) hsum W.mixed
  exact ⟨V, hdim, hsymm, E, fun h => W.mixed_correlation_transfer E
    (fun x => V.unit_eval (fun j => x j.1)) h⟩

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

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def NativeMultidegreeNilcharacter.cubicAntisymmetricPair {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
    (i j : Fin V.outputDim × Fin V.outputDim) (h n k : ℤ) : ℂ :=
  (star (V.eval i.1 (cubicTrilinearInput h n k)) * V.eval j.1 (cubicTrilinearInput n h k)) *
    (star (V.eval i.2 (cubicTrilinearInput h n k)) * V.eval j.2 (cubicTrilinearInput n h k))

end Erdos3

end

end OAI

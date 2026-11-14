/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/LocalMajorDenseSliceNiltest.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.Complex.Circle
public import OAI.Combinatorics.Progressions.Estimates.VectorApproximationPrecomposition
public import OAI.Combinatorics.Progressions.Estimates.ImageExtensionInverseBounds
public import OAI.Combinatorics.Progressions.Estimates.LowerTriangularMinor
public import OAI.Combinatorics.Progressions.Estimates.RealFiniteZeroExtension
public import OAI.Combinatorics.Progressions.Estimates.UniformCommutingCircleDecomposition
public import OAI.Combinatorics.Progressions.Fourier.QuarticBohrProgression
public import OAI.Combinatorics.Progressions.Geometry.RealCoordinateFunctionals
public import OAI.Combinatorics.Progressions.Lattices.ScaledLatticeCovolume
public import OAI.Combinatorics.Progressions.Fourier.BohrNiltestBudget
@[expose] public section

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def scaleComplex (T : D.Niltest w) (c : ℂ) : D.Niltest w where
  orbit := T.orbit
  observable := fun x => c * T.observable x
  normBound := ‖c‖₊ * T.normBound
  lipBound := ‖c‖₊ * T.lipBound
  norm_le x := by
    simpa only [norm_mul, NNReal.coe_mul, coe_nnnorm] using
      mul_le_mul_of_nonneg_left (T.norm_le x) (norm_nonneg c)
  lipschitz := by
    let := D.metricSpace
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, ← mul_sub, norm_mul, NNReal.coe_mul, coe_nnnorm, mul_assoc] using
      mul_le_mul_of_nonneg_left (T.lipschitz.dist_le_mul x y) (norm_nonneg c)

theorem scaleComplex_eval (T : D.Niltest w) (c : ℂ) (x : σ → ℤ) :
    (T.scaleComplex c).eval x = c * T.eval x := rfl

theorem scaleComplex_evalCyclic (T : D.Niltest w) (c : ℂ) (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    (T.scaleComplex c).evalCyclic N x = c * T.evalCyclic N x := rfl

theorem scaleComplex_norm (T : D.Niltest w) {c : ℂ} (hc : ‖c‖ ≤ 1) :
    (T.scaleComplex c).normBound ≤ T.normBound := by
  change ‖c‖₊ * T.normBound ≤ T.normBound
  exact mul_le_of_le_one_left (by positivity) (by exact_mod_cast hc)

theorem scaleComplex_complexity (T : D.Niltest w) {c : ℂ} (hc : ‖c‖ ≤ 1)
    {p : ℝ} (hT : T.ComplexityLE p) : (T.scaleComplex c).ComplexityLE p := by
  refine ⟨hT.1, ?_⟩
  change Real.log (2 + ‖c‖ * (T.normBound : ℝ) + ‖c‖ * (T.lipBound : ℝ)) ≤ p
  have hn := mul_le_mul_of_nonneg_right hc T.normBound.coe_nonneg
  have hl := mul_le_mul_of_nonneg_right hc T.lipBound.coe_nonneg
  exact (Real.log_le_log (by positivity) (by linarith)).trans hT.2

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct Manifold ContDiff

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def evalReal (T : D.Niltest w) (x : σ → ℝ) : ℂ :=
  T.observable (QuotientGroup.mk (D.filtration.realification.polynomialOrbitRealEval w x T.orbit))

theorem evalReal_integer (T : D.Niltest w) (x : σ → ℤ) :
    T.evalReal (fun i => (x i : ℝ)) = T.eval x := by
  unfold evalReal eval
  rw [NilpotentLieFiltration.polynomialOrbitRealEval_integer]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def expNormalize (T : D.Niltest w) (p : ℝ) : D.Niltest w :=
  T.scaleComplex (Real.exp (-p) : ℂ)

theorem expNormalize_norm (T : D.Niltest w) {p : ℝ} (hT : T.ComplexityLE p) :
    (T.expNormalize p).normBound ≤ 1 := by
  have hb := T.observable_budget hT
  have hl := T.lipBound.coe_nonneg
  have hn : (T.normBound : ℝ) ≤ Real.exp p := by linarith
  change ‖(Real.exp (-p) : ℂ)‖₊ * T.normBound ≤ 1
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_mul, coe_nnnorm, NNReal.coe_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-p))]
  calc
    _ ≤ Real.exp (-p) * Real.exp p := mul_le_mul_of_nonneg_left hn (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

theorem expNormalize_complexity (T : D.Niltest w) {p : ℝ} (hT : T.ComplexityLE p) :
    (T.expNormalize p).ComplexityLE p := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hT.1.1
  apply T.scaleComplex_complexity _ hT
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-p))]
  exact Real.exp_le_one_iff.mpr (by linarith)

theorem expNormalize_eval (T : D.Niltest w) (p : ℝ) (x : σ → ℤ) :
    (T.expNormalize p).eval x = (Real.exp (-p) : ℂ) * T.eval x := rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_bounded_niltest_pair_sum {J σ L K : Type*} [Fintype J] [Nonempty J]
    [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
    {s t d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold K t e) (w : σ → ℕ)
    (gD : D.filtration.realification.PolynomialOrbit w)
    (gE : E.filtration.realification.PolynomialOrbit w)
    (A : J → D.Niltest w) (B : J → E.Niltest w) (c : J → ℂ) {p : ℝ}
    (hAnorm : ∀ j, (A j).normBound ≤ 1) (hBnorm : ∀ j, (B j).normBound ≤ 1)
    (hA : ∀ j, (A j).ComplexityLE p) (hB : ∀ j, (B j).ComplexityLE p)
    (hAg : ∀ j, (A j).orbit = gD) (hBg : ∀ j, (B j).orbit = gE)
    (hc : ∀ j, ‖c j‖ ≤ 2) :
    ∃ N : ℕ, 0 < N ∧ N = 2 * Fintype.card J ∧
      ∃ (A' : Fin N → D.Niltest w) (B' : Fin N → E.Niltest w),
        (∀ j, (A' j).normBound ≤ 1) ∧ (∀ j, (B' j).normBound ≤ 1) ∧
        (∀ j, (A' j).ComplexityLE p) ∧ (∀ j, (B' j).ComplexityLE p) ∧
        (∀ j, (A' j).orbit = gD) ∧ (∀ j, (B' j).orbit = gE) ∧
        ∀ x, ∑ j, (A' j).eval x * (B' j).eval x =
          ∑ j, ((A j).eval x * (B j).eval x) * c j := by
  classical
  let f := (Fintype.equivFin (Bool × J)).symm
  let A' (j : Fin (Fintype.card (Bool × J))) :=
    (A (f j).2).scaleComplex (c (f j).2 / 2)
  let B' (j : Fin (Fintype.card (Bool × J))) := B (f j).2
  refine ⟨Fintype.card (Bool × J), Fintype.card_pos, ?_, A', B', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Fintype.card_prod, Fintype.card_bool]
  · intro j
    exact ((A (f j).2).scaleComplex_norm (norm_complex_half_le_one (hc (f j).2))).trans (hAnorm _)
  · intro j
    exact hBnorm _
  · intro j
    exact (A (f j).2).scaleComplex_complexity (norm_complex_half_le_one (hc (f j).2)) (hA _)
  · intro j
    exact hB _
  · intro j
    exact hAg _
  · intro j
    exact hBg _
  · intro x
    exact (f.sum_comp (fun j => (c j.2 / 2 * (A j.2).eval x) * (B j.2).eval x)).trans
      (sum_double_half_products (fun j => (A j).eval x) (fun j => (B j).eval x) c)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalTorus

instance zeroAlgebraSubsingleton : Subsingleton (Algebra 0) :=
  inferInstanceAs (Subsingleton (Fin 0 → ℚ))

def trivialFiltration (s : ℕ) : NilpotentLieFiltration (Algebra 0) s where
  layer _ := ⊤
  antitone _ _ _ := le_rfl
  one_eq_top := rfl
  lie_mem _ _ := Submodule.mem_top
  terminal := by
    apply le_antisymm _ bot_le
    intro x _
    simpa only [Submodule.mem_bot] using (Subsingleton.elim x 0)

theorem trivialFiltration_basis_layers (s j : ℕ) :
    (trivialFiltration s).layer j = Submodule.span ℚ ((basis 0) '' {_i : Fin 0 | j ≤ (0 : ℕ)}) := by
  ext x
  rw [Subsingleton.elim x 0]
  simp only [Submodule.zero_mem]

theorem trivial_lattice_inner_grid (s : ℕ) :
    scaledIntegerGrid 1 ⊆ bchSubgroupCoordinates (basis 0) (⊤ : Subgroup (trivialFiltration s).Group) := by
  intro x _
  trivial

theorem trivial_lattice_outer_grid (s : ℕ) :
    bchSubgroupCoordinates (basis 0) (⊤ : Subgroup (trivialFiltration s).Group) ⊆ denominatorGrid 1 := by
  intro x _
  exact ⟨0, fun i => Fin.elim0 i⟩

noncomputable def trivialNilmanifold (s : ℕ) : RationalFilteredNilmanifold (Algebra 0) s 0 :=
  (trivialFiltration s).ofAdaptedBasis (basis 0) (fun _ => 0) (trivialFiltration_basis_layers s)
    ⊤ 1 (by omega) (trivial_lattice_inner_grid s) (trivial_lattice_outer_grid s)

theorem trivialNilmanifold_geometry (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (trivialNilmanifold s).GeometryComplexityLE p := by
  apply (trivialFiltration s).ofAdaptedBasis_geometry (basis 0) (fun _ => 0)
    (trivialFiltration_basis_layers s) ⊤ 1 (by omega)
    (trivial_lattice_inner_grid s) (trivial_lattice_outer_grid s) hp (by simpa using hp)
  · simpa only [Nat.cast_one] using Real.one_le_exp hp
  · intro i
    exact Fin.elim0 i

theorem trivialNilmanifold_const_one_complexity (s : ℕ) {σ : Type*} (w : σ → ℕ) {p : ℝ}
    (hp : 2 ≤ p) :
    (RationalFilteredNilmanifold.Niltest.const (trivialNilmanifold s) w 1).ComplexityLE p := by
  refine ⟨trivialNilmanifold_geometry s (by linarith), ?_⟩
  change Real.log (2 + (‖(1 : ℂ)‖₊ : ℝ) + (0 : ℝ)) ≤ p
  simp only [nnnorm_one, NNReal.coe_one, add_zero]
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  norm_num at *
  linarith

end Erdos3.RationalTorus

end

section

namespace Erdos3

open MvPolynomial

variable {U : Type*}

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

variable [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open MvPolynomial PolynomialTranslationLie
open scoped TensorProduct NNReal

def weight : Fin 0 → ℕ := fun _ => 1

variable {s : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra weight s)]

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators TensorProduct

variable {U : Type*} [Fintype U] [DecidableEq U] {n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators TensorProduct

variable {U : Type*} [Fintype U] [DecidableEq U] {n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]

end Erdos3

end

end OAI

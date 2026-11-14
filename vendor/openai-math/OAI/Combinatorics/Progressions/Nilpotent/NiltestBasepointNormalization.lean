/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/NiltestBasepointNormalization.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.ZMod.Basic
public import OAI.Combinatorics.Progressions.Estimates.OrbitBasepointNormalization
public import OAI.Combinatorics.Progressions.Dynamics.RationalLieQuotientBudget
public import OAI.Combinatorics.Progressions.Lattices.RealifiedSubgroupLattice
public import OAI.Combinatorics.Progressions.Nilpotent.FactorwiseBCHCovers
public import OAI.Combinatorics.Progressions.Nilpotent.RealifiedBCHFiniteAtlas
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem basis_reindex_equivFun_symm (b : Basis ι ℚ L) (e : ι ≃ κ) (x : κ → ℚ) :
    (b.reindex e).equivFun.symm x = b.equivFun.symm (fun i => x (e i)) := by
  apply b.equivFun.injective
  funext i
  rw [LinearEquiv.apply_symm_apply]
  have h := congrFun ((b.reindex e).equivFun.apply_symm_apply x) (e i)
  simpa only [Basis.equivFun_apply, Basis.repr_reindex_apply,
    Equiv.symm_apply_apply] using h

theorem bchSubgroupCoordinates_reindex (b : Basis ι ℚ L) (e : ι ≃ κ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (x : κ → ℚ) :
    x ∈ bchSubgroupCoordinates (b.reindex e) Γ ↔
      (fun i => x (e i)) ∈ bchSubgroupCoordinates b Γ := by
  unfold bchSubgroupCoordinates
  simp only [Set.mem_ofPred_eq, basis_reindex_equivFun_symm]

theorem bchSubgroup_inner_grid_reindex (b : Basis ι ℚ L) (e : ι ≃ κ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) {N : ℕ}
    (h : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ) :
    scaledIntegerGrid N ⊆ bchSubgroupCoordinates (b.reindex e) Γ := by
  rintro x ⟨z, rfl⟩
  apply (bchSubgroupCoordinates_reindex b e Γ _).mpr
  exact h ⟨fun i => z (e i), rfl⟩

theorem bchSubgroup_outer_grid_reindex (b : Basis ι ℚ L) (e : ι ≃ κ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) {N : ℕ}
    (h : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    bchSubgroupCoordinates (b.reindex e) Γ ⊆ denominatorGrid N := by
  intro x hx
  obtain ⟨z, hz⟩ := h ((bchSubgroupCoordinates_reindex b e Γ x).mp hx)
  refine ⟨fun i => z (e.symm i), fun i => ?_⟩
  simpa only [Pi.smul_apply, Equiv.apply_symm_apply] using hz (e.symm i)

omit [Fintype ι] [Fintype κ] in
theorem basis_reindex_span_weights (b : Basis ι ℚ L) (e : ι ≃ κ)
    (w : ι → ℕ) (j : ℕ) :
    Submodule.span ℚ ((b.reindex e) '' {i | j ≤ w (e.symm i)}) =
      Submodule.span ℚ (b '' {i | j ≤ w i}) := by
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨e.symm i, hi, (Basis.reindex_apply b e i).symm⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨e i, ?_, ?_⟩
    · simpa only [Set.mem_ofPred_eq, Equiv.symm_apply_apply] using hi
    · simp only [Basis.reindex_apply, Equiv.symm_apply_apply]

omit [Fintype ι] [Fintype κ] in
theorem lieStructureConstants_reindex (b : Basis ι ℚ L) (e : ι ≃ κ) (i j k : κ) :
    lieStructureConstants (b.reindex e) i j k =
      lieStructureConstants b (e.symm i) (e.symm j) (e.symm k) := by
  simp only [lieStructureConstants, Basis.reindex_apply, Basis.repr_reindex_apply]

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Set Manifold
open scoped Manifold ContDiff Topology

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
  (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
  (hc : ∀ i j k, RationalHeightLE (c i j k) H)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
  (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

local notation "G" => NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)

variable (e : Basis ι ℚ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (l : ℕ) (hl : 0 < l) (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)

@[instance_reducible]
noncomputable def realificationQuotientChartedSpace :
    ChartedSpace (ι → ℝ) (G ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) :=
  NilpotentLieBCHGroup.quotientChartedSpace (e.baseChange ℝ) (lieStructureConstants e)
    (fun i j k => (realLieBasis_structure e i j k).symm) hc
    (Γ.map NilpotentLieBCHGroup.realificationHom) l hl
    (NilpotentLieBCHGroup.realification_subgroup_grid e Γ l houter)

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct Manifold ContDiff

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s H₁ H₂ : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct Manifold ContDiff

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℚ L]

structure RationalFilteredNilmanifold (s d : ℕ) where
  filtration : NilpotentLieFiltration L s
  basis : Basis (Fin d) ℚ L
  layerBasis : ∀ i : Fin (s + 1),
    Basis (Fin (Module.finrank ℚ (filtration.layer (i.val + 1)))) ℚ (filtration.layer (i.val + 1))
  lattice : Subgroup filtration.Group
  grid : ℕ
  grid_pos : 0 < grid
  inner_grid : scaledIntegerGrid grid ⊆ bchSubgroupCoordinates basis lattice
  outer_grid : bchSubgroupCoordinates basis lattice ⊆ denominatorGrid grid

noncomputable def rationalLogHeight (q : ℚ) : ℝ :=
  Real.log (max (q.num.natAbs : ℝ) (q.den : ℝ))

namespace RationalFilteredNilmanifold

variable {L} {s d : ℕ} (D : RationalFilteredNilmanifold L s d)

abbrev RealGroup := D.filtration.realification.Group

noncomputable def realLattice : Subgroup D.RealGroup :=
  D.lattice.map NilpotentLieBCHGroup.realificationHom

abbrev Space : Type _ := D.RealGroup ⧸ D.realLattice

def GeometryComplexityLE (p : ℝ) : Prop :=
  (d : ℝ) ≤ p ∧ (D.grid : ℝ) ≤ Real.exp p ∧
  (∀ i j k, rationalLogHeight (lieStructureConstants D.basis i j k) ≤ p) ∧
  (∀ i j k, rationalLogHeight (D.basis.repr (D.layerBasis i j) k) ≤ p)

theorem GeometryComplexityLE.mono {p q : ℝ} (hp : D.GeometryComplexityLE p) (hpq : p ≤ q) :
    D.GeometryComplexityLE q :=
  ⟨hp.1.trans hpq, hp.2.1.trans (Real.exp_le_exp.mpr hpq),
    fun i j k => (hp.2.2.1 i j k).trans hpq,
    fun i j k => (hp.2.2.2 i j k).trans hpq⟩

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

@[instance_reducible]
noncomputable def metricSpace : MetricSpace D.Space :=
  realificationQuotientMetricSpace D.basis D.lattice D.grid D.grid_pos D.outer_grid

theorem realLattice_closed_discrete :
    IsClosed (D.realLattice : Set D.RealGroup) ∧ IsDiscrete (D.realLattice : Set D.RealGroup) :=
  NilpotentLieBCHGroup.realification_subgroup_closed_discrete
    D.basis D.lattice D.grid D.grid_pos D.outer_grid

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d) (hD : D.filtration.layer (s + 1) = ⊥)

noncomputable def dropTop : RationalFilteredNilmanifold L s d where
  filtration := D.filtration.dropTop hD
  basis := D.basis
  layerBasis i := D.layerBasis ⟨i.val, by omega⟩
  lattice := D.lattice.map (NilpotentLieBCHGroup.changeStep D.filtration.lowerCentralSeries_eq_bot
    (D.filtration.dropTop hD).lowerCentralSeries_eq_bot).toMonoidHom
  grid := D.grid
  grid_pos := D.grid_pos
  inner_grid := by
    rw [bchSubgroupCoordinates_changeStep]
    exact D.inner_grid
  outer_grid := by
    rw [bchSubgroupCoordinates_changeStep]
    exact D.outer_grid

theorem dropTop_geometry {p : ℝ} (hp : D.GeometryComplexityLE p) :
    (D.dropTop hD).GeometryComplexityLE p :=
  ⟨hp.1, hp.2.1, hp.2.2.1, fun i j k => hp.2.2.2 ⟨i.val, by omega⟩ j k⟩

theorem dropTop_lattice_back :
    (D.dropTop hD).lattice ≤ D.lattice.comap
      (NilpotentLieBCHGroup.mapOfSteps
        (hL := (D.filtration.dropTop hD).lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L)) := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
  exact hx

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L s d)

structure Niltest (w : σ → ℕ) where
  orbit : D.filtration.realification.PolynomialOrbit w
  observable : D.Space → ℂ
  normBound : ℝ≥0
  lipBound : ℝ≥0
  norm_le : ∀ x, ‖observable x‖ ≤ normBound
  lipschitz : letI := D.metricSpace; LipschitzWith lipBound observable

namespace Niltest

variable {D} {w : σ → ℕ}

noncomputable def const (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ) (c : ℂ) :
    D.Niltest w where
  orbit := 1
  observable := fun _ => c
  normBound := ‖c‖₊
  lipBound := 0
  norm_le _ := le_rfl
  lipschitz := by
    let := D.metricSpace
    exact LipschitzWith.const c

noncomputable def eval (T : D.Niltest w) (x : σ → ℤ) : ℂ :=
  T.observable (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x T.orbit))

@[simp] theorem eval_const (D : RationalFilteredNilmanifold L s d)
    (w : σ → ℕ) (c : ℂ) (x : σ → ℤ) : (const D w c).eval x = c := rfl

theorem norm_eval_le (T : D.Niltest w) (x : σ → ℤ) : ‖T.eval x‖ ≤ T.normBound :=
  T.norm_le _

noncomputable def evalCyclic (T : D.Niltest w) (N : ℕ) [NeZero N] (x : σ → ZMod N) : ℂ :=
  T.eval (fun i => ((x i).val : ℤ))

theorem norm_evalCyclic_le (T : D.Niltest w) (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    ‖T.evalCyclic N x‖ ≤ T.normBound := T.norm_eval_le _

def ComplexityLE (T : D.Niltest w) (p : ℝ) : Prop :=
  D.GeometryComplexityLE p ∧ Real.log (2 + (T.normBound : ℝ) + (T.lipBound : ℝ)) ≤ p

theorem ComplexityLE.mono {T : D.Niltest w} {p q : ℝ}
    (hp : T.ComplexityLE p) (hpq : p ≤ q) : T.ComplexityLE q :=
  ⟨GeometryComplexityLE.mono D hp.1 hpq, hp.2.trans hpq⟩

theorem observable_budget {T : D.Niltest w} {p : ℝ} (hp : T.ComplexityLE p) :
    2 + (T.normBound : ℝ) + (T.lipBound : ℝ) ≤ Real.exp p := by
  have hpos : 0 < 2 + (T.normBound : ℝ) + (T.lipBound : ℝ) := by positivity
  simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr hp.2

theorem eval_budget {T : D.Niltest w} {p : ℝ} (hp : T.ComplexityLE p) (x : σ → ℤ) :
    ‖T.eval x‖ ≤ Real.exp p := by
  have h := observable_budget hp
  have hn := T.norm_eval_le x
  have hl := T.lipBound.coe_nonneg
  linarith

theorem eval_step_zero (D : RationalFilteredNilmanifold L 0 d)
    (T : D.Niltest w) (x : σ → ℤ) :
    T.eval x = T.observable (QuotientGroup.mk (1 : D.RealGroup)) := by
  unfold eval
  rw [NilpotentLieFiltration.polynomialOrbitEval_step_zero]

end Niltest
end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)

noncomputable def raisedLayerBasis (i : Fin (t + 1)) :
    Basis (Fin (Module.finrank ℚ ((D.filtration.raiseStep hst).layer (i.val + 1)))) ℚ
      ((D.filtration.raiseStep hst).layer (i.val + 1)) := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact if hi : i.val < s + 1 then D.layerBasis ⟨i.val, hi⟩ else
    Module.finBasis ℚ ((D.filtration.raiseStep hst).layer (i.val + 1))

theorem raisedLayerBasis_of_lt (i : Fin (t + 1)) (hi : i.val < s + 1) :
    D.raisedLayerBasis hst i = D.layerBasis ⟨i.val, hi⟩ := by
  simp [raisedLayerBasis, hi]
  rfl

noncomputable def raiseStep : RationalFilteredNilmanifold L t d where
  filtration := D.filtration.raiseStep hst
  basis := D.basis
  layerBasis := D.raisedLayerBasis hst
  lattice := D.lattice.map (NilpotentLieBCHGroup.changeStep D.filtration.lowerCentralSeries_eq_bot
    (D.filtration.raiseStep hst).lowerCentralSeries_eq_bot).toMonoidHom
  grid := D.grid
  grid_pos := D.grid_pos
  inner_grid := by
    rw [bchSubgroupCoordinates_changeStep]
    exact D.inner_grid
  outer_grid := by
    rw [bchSubgroupCoordinates_changeStep]
    exact D.outer_grid

theorem raiseStep_geometry {p : ℝ} (hD : D.GeometryComplexityLE p) :
    (D.raiseStep hst).GeometryComplexityLE p := by
  refine ⟨hD.1, hD.2.1, hD.2.2.1, ?_⟩
  intro i j k
  by_cases hi : i.val < s + 1
  · change rationalLogHeight (D.basis.repr (D.raisedLayerBasis hst i j) k) ≤ p
    rw [D.raisedLayerBasis_of_lt hst i hi]
    exact hD.2.2.2 ⟨i.val, hi⟩ j k
  · have hbot : D.filtration.layer (i.val + 1) = ⊥ :=
      D.filtration.layer_eq_bot_above_step (by omega)
    have hrank : Module.finrank ℚ ((D.filtration.raiseStep hst).layer (i.val + 1)) = 0 := by
      rw [NilpotentLieFiltration.raiseStep_layer, hbot]
      simp
    have hj := j.isLt
    change j.val < Module.finrank ℚ ((D.filtration.raiseStep hst).layer (i.val + 1)) at hj
    rw [hrank] at hj
    omega

theorem raiseStep_lattice_back :
    (D.raiseStep hst).lattice ≤ D.lattice.comap
      (NilpotentLieBCHGroup.mapOfSteps
        (hL := (D.filtration.raiseStep hst).lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L)) := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
  exact hx

end Erdos3.RationalFilteredNilmanifold

end

section

open Module
open scoped BigOperators

namespace Erdos3

namespace NilpotentLieFiltration

variable {ι : Type*} {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}

def piLayerEquiv (F : ∀ i, NilpotentLieFiltration (L i) s) (n : ℕ) :
    (∀ i, (F i).layer n) ≃ₗ[ℚ] (pi F).layer n where
  toFun x := ⟨fun i => x i, (mem_pi_layer F n _).mpr (fun i => (x i).property)⟩
  invFun x i := ⟨x.val i, (mem_pi_layer F n _).mp x.property i⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def productFinBasis : Basis (Fin (Fintype.card (Σ i, Fin (d i)))) ℚ (∀ i, L i) :=
  (Pi.basis (fun i => (D i).basis)).reindex (Fintype.equivFin _)

noncomputable def productLayerBasis (j : Fin (s + 1)) :
    Basis (Σ i, Fin (finrank ℚ ((D i).filtration.layer (j.val + 1)))) ℚ
      ((NilpotentLieFiltration.pi (fun i => (D i).filtration)).layer (j.val + 1)) :=
  (Pi.basis (fun i => (D i).layerBasis j)).map
    (NilpotentLieFiltration.piLayerEquiv (fun i => (D i).filtration) (j.val + 1))

noncomputable def productLayerFinBasis (j : Fin (s + 1)) :
    Basis (Fin (finrank ℚ ((NilpotentLieFiltration.pi (fun i => (D i).filtration)).layer (j.val + 1)))) ℚ
      ((NilpotentLieFiltration.pi (fun i => (D i).filtration)).layer (j.val + 1)) :=
  (productLayerBasis D j).reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis (productLayerBasis D j)).symm)

theorem product_inner_grid : scaledIntegerGrid (∏ i, (D i).grid) ⊆
    bchSubgroupCoordinates (productFinBasis D)
      (piBCHSubgroup (fun i => (D i).filtration) (fun i => (D i).lattice)) := by
  classical
  apply bchSubgroup_inner_grid_reindex
  apply piBCHSubgroup_inner_grid
  intro i
  exact (scaledIntegerGrid_subset_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))).trans (D i).inner_grid

theorem product_outer_grid :
    bchSubgroupCoordinates (productFinBasis D)
      (piBCHSubgroup (fun i => (D i).filtration) (fun i => (D i).lattice)) ⊆
        denominatorGrid (∏ i, (D i).grid) := by
  classical
  apply bchSubgroup_outer_grid_reindex
  apply piBCHSubgroup_outer_grid
  intro i
  exact (D i).outer_grid.trans (denominatorGrid_subset_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))

noncomputable def pi : RationalFilteredNilmanifold (∀ i, L i) s (Fintype.card (Σ i, Fin (d i))) where
  filtration := NilpotentLieFiltration.pi (fun i => (D i).filtration)
  basis := productFinBasis D
  layerBasis := productLayerFinBasis D
  lattice := piBCHSubgroup (fun i => (D i).filtration) (fun i => (D i).lattice)
  grid := ∏ i, (D i).grid
  grid_pos := Finset.prod_pos (fun i _ => (D i).grid_pos)
  inner_grid := product_inner_grid D
  outer_grid := product_outer_grid D

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def normalizeBasepoint (T : D.Niltest w) (a γ : D.RealGroup) (A : ℝ≥0)
    (hA : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => a • x)) : D.Niltest w where
  orbit := D.filtration.realification.normalizePolynomialOrbit w T.orbit a γ
  observable := fun x => T.observable (a • x)
  normBound := T.normBound
  lipBound := T.lipBound * A
  norm_le x := T.norm_le (a • x)
  lipschitz := by
    let := D.metricSpace
    exact T.lipschitz.comp hA

theorem normalizeBasepoint_zero (T : D.Niltest w) (a γ : D.RealGroup) (A : ℝ≥0)
    (hA : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => a • x))
    (hg : D.filtration.realification.polynomialOrbitEval w 0 T.orbit = a * γ) :
    D.filtration.realification.polynomialOrbitEval w 0 (T.normalizeBasepoint a γ A hA).orbit = 1 :=
  D.filtration.realification.normalizePolynomialOrbit_zero w T.orbit a γ hg

theorem normalizeBasepoint_eval (T : D.Niltest w) (a γ : D.RealGroup) (A : ℝ≥0)
    (hA : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => a • x))
    (hγ : γ ∈ D.realLattice) (x : σ → ℤ) :
    (T.normalizeBasepoint a γ A hA).eval x = T.eval x := by
  change T.observable (a • QuotientGroup.mk
    (D.filtration.realification.polynomialOrbitEval w x
      (D.filtration.realification.normalizePolynomialOrbit w T.orbit a γ))) = _
  rw [NilpotentLieFiltration.normalizePolynomialOrbit_eval]
  simp only [MulAction.Quotient.smul_mk, smul_eq_mul, ← mul_assoc, mul_inv_cancel, one_mul]
  exact congrArg T.observable (QuotientGroup.mk_mul_of_mem _ (D.realLattice.inv_mem hγ))

theorem normalizeBasepoint_complexity (T : D.Niltest w) (a γ : D.RealGroup) (A : ℝ≥0)
    (hA : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => a • x))
    {p q : ℝ} (hT : T.ComplexityLE p) (hq : 0 ≤ q) (hbound : (A : ℝ) ≤ Real.exp q) :
    (T.normalizeBasepoint a γ A hA).ComplexityLE (p + q) := by
  refine ⟨hT.1.mono D (le_add_of_nonneg_right hq), ?_⟩
  change Real.log (2 + (T.normBound : ℝ) + (T.lipBound : ℝ) * A) ≤ p + q
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  have h1 : 1 ≤ Real.exp q := Real.one_le_exp hq
  calc
    _ ≤ (2 + (T.normBound : ℝ)) * Real.exp q + (T.lipBound : ℝ) * Real.exp q :=
      add_le_add (le_mul_of_one_le_right (by positivity) h1)
        (mul_le_mul_of_nonneg_left hbound T.lipBound.coe_nonneg)
    _ = (2 + (T.normBound : ℝ) + (T.lipBound : ℝ)) * Real.exp q := by ring
    _ ≤ Real.exp p * Real.exp q := mul_le_mul_of_nonneg_right (observable_budget hT) (Real.exp_nonneg _)
    _ = _ := (Real.exp_add _ _).symm

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

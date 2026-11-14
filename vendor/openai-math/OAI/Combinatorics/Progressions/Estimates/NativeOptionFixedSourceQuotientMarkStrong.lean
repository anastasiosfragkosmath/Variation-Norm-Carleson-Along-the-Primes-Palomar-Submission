/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/NativeOptionFixedSourceQuotientMarkStrong.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Linear.ChosenBasisGeometryBounds
public import OAI.Combinatorics.Progressions.Estimates.NativeOptionOriginalOrbit
public import OAI.Combinatorics.Progressions.Nilpotent.NiltestVerticalBounds
@[expose] public section

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}

structure AdaptedModelData (D : RationalFilteredNilmanifold L s d) where
  basis : Basis (Fin (finrank ℚ L)) ℚ L
  weight : Fin (finrank ℚ L) → ℕ
  layers : ∀ j, D.filtration.layer j = Submodule.span ℚ (basis '' {i | j ≤ weight i})
  grid : ℕ
  grid_pos : 0 < grid
  inner : scaledIntegerGrid grid ⊆ bchSubgroupCoordinates basis D.lattice
  outer : bchSubgroupCoordinates basis D.lattice ⊆ denominatorGrid grid

namespace AdaptedModelData

variable {D : RationalFilteredNilmanifold L s d}

noncomputable def model (F : D.AdaptedModelData) : RationalFilteredNilmanifold L s (finrank ℚ L) :=
  D.filtration.ofAdaptedBasis F.basis F.weight F.layers D.lattice F.grid F.grid_pos F.inner F.outer

theorem model_layers (F : D.AdaptedModelData) (j : ℕ) :
    F.model.filtration.layer j = Submodule.span ℚ (F.model.basis '' {i | j ≤ F.weight i}) := F.layers j

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem original_dist_le (F : D.AdaptedModelData) (H : ℕ)
    (hH : ∀ i j, RationalHeightLE (D.basis.repr (F.basis i) j) H) (x y : D.Space) :
    @dist D.Space D.metricSpace.toDist x y ≤
      coordinateLipschitzBound d (finrank ℚ L) H * @dist F.model.Space F.model.metricSpace.toDist x y := by
  have hreal (j i) : |(D.basis.baseChange ℝ).repr ((F.basis.baseChange ℝ) i) j| ≤ (H : ℝ≥0) := by
    rw [Basis.baseChange_apply, Basis.baseChange_repr_tmul]
    simpa only [Rat.smul_def, mul_one, NNReal.coe_natCast] using (hH i j).abs_real_le
  have h := NilpotentLieBCHGroup.basisQuotientDist_change_le
    (F.basis.baseChange ℝ) (D.basis.baseChange ℝ) D.realLattice
    D.realLattice_closed_discrete.1 H hreal x y
  simp only [Fintype.card_fin] at h
  convert h using 1 <;> rfl

end AdaptedModelData

theorem exists_adapted_model_data (D : RationalFilteredNilmanifold L s d)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    ∃ F : D.AdaptedModelData, F.model.GeometryComplexityLE ((p + 3) ^ 11) ∧
      ∀ i j, rationalLogHeight (D.basis.repr (F.basis i) j) ≤ p + 1 := by
  obtain ⟨b, w, N, _, _, hlayers, hb, _, hc, hN, hNp, hin, hout⟩ :=
    D.exists_controlled_adapted_basis hp hD
  let F : D.AdaptedModelData := ⟨b, w, hlayers, N, hN, hin, hout⟩
  have hp1 : 1 ≤ p + 3 := by linarith
  have hpow : p ≤ (p + 3) ^ 11 := by
    calc
      p ≤ p + 3 := by linarith
      _ = (p + 3) ^ 1 := (pow_one _).symm
      _ ≤ (p + 3) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  have hdim : (finrank ℚ L : ℝ) ≤ (p + 3) ^ 11 := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using hD.1.trans hpow
  refine ⟨F, ?_, hb⟩
  exact D.filtration.ofAdaptedBasis_geometry b w hlayers D.lattice N hN hin hout
    (by positivity) hdim
    (hNp.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hp1 (by decide : 9 ≤ 11)))) hc

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_prescribed_adapted_model {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d n : ℕ} (D : RationalFilteredNilmanifold L s d)
    (b : Basis (Fin n) ℚ L) (ω : Fin n → ℕ)
    (hF : ∀ k, D.filtration.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hb : ∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p + 1) :
    ∃ (M : ℕ) (hM : 0 < M)
      (hin : scaledIntegerGrid M ⊆ bchSubgroupCoordinates b D.lattice)
      (hout : bchSubgroupCoordinates b D.lattice ⊆ denominatorGrid M),
      (D.filtration.ofAdaptedBasis b ω hF D.lattice M hM hin hout).GeometryComplexityLE
        ((p + 4) ^ 11) := by
  obtain ⟨hdim, _hinverse, hstructure⟩ := D.basis_geometry_of_forward_height b hp hD hb
  let H := ⌈Real.exp (p + 1)⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp (p + 1)
  have hHp : (H : ℝ) ≤ Real.exp (p + 2) := by
    simpa only [show p + 1 + 1 = p + 2 by ring] using
      ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)
  have hentries : ∀ i j, RationalHeightLE (D.basis.repr (b i) j) H :=
    fun i j => rationalHeightLE_ceil_exp (hb i j)
  have hd : (Fintype.card (Fin d) : ℝ) ≤ p + 2 := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 2 by linarith)
  obtain ⟨M, hM, hMp, hin, hout⟩ := exists_basis_change_grid_exp_bound D.basis b D.lattice
    hH D.grid_pos hentries D.inner_grid D.outer_grid (by linarith : 0 ≤ p + 2) hd
    (hdim.trans (by linarith)) hHp (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
  have hbase : 1 ≤ p + 4 := by linarith
  have hpbig : p ≤ (p + 4) ^ 11 := by
    apply (show p ≤ p + 4 by linarith).trans
    simpa only [pow_one] using pow_le_pow_right₀ hbase (by decide : 1 ≤ 11)
  have hgrid : (M : ℝ) ≤ Real.exp ((p + 4) ^ 11) := by
    have hsmall : (M : ℝ) ≤ Real.exp ((p + 4) ^ 9) := by
      simpa only [show p + 2 + 2 = p + 4 by ring] using hMp
    exact hsmall.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (by decide : 9 ≤ 11)))
  refine ⟨M, hM, hin, hout, ?_⟩
  exact D.filtration.ofAdaptedBasis_geometry b ω hF D.lattice M hM hin hout
    (by positivity) (by simpa only [Fintype.card_fin] using hdim.trans hpbig) hgrid hstructure

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t d e : ℕ}

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t d f : ℕ}

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
    [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
    {s d₀ : ℕ} {d : ι → ℕ}
    (D₀ : RationalFilteredNilmanifold L₀ s d₀)
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    {P : Type*} (observable : P → D₀.Space → ℂ)

section Metric

variable [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    [TopologicalSpace (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
    [T2Space (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]

end Metric

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {Pivot : Type v} [Fintype Pivot]
    {L M : Type u} {Partner : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [∀ a, LieRing (Partner a)] [∀ a, LieAlgebra ℚ (Partner a)]
    {s d f dQ : ℕ} {dp : Pivot → ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (Mmark : RationalFilteredNilmanifold M s f)
    (ideal : LieIdeal ℚ L)
    (hkill : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hkill)
    (atoms : ∀ a, RationalFilteredNilmanifold (Partner a) s (dp a))
    (φ : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ ideal, φ x = 0)
    (hφ : ∀ k, ∀ x ∈ D.filtration.layer k, φ x ∈ Mmark.filtration.layer k)
    (source : (optionProduct Q atoms).AdaptedModelData)

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {Pivot : Type v} [Fintype Pivot]
    {L M : Type u} {Partner : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [∀ a, LieRing (Partner a)] [∀ a, LieAlgebra ℚ (Partner a)]
    {s d f dQ : ℕ} {dp : Pivot → ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (Mmark : RationalFilteredNilmanifold M s f)
    (ideal : LieIdeal ℚ L)
    (hkill : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hkill)
    (atoms : ∀ a, RationalFilteredNilmanifold (Partner a) s (dp a))
    (φ : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ ideal, φ x = 0)
    (source : (optionProduct Q atoms).AdaptedModelData)
    (hsurj : ∀ k, ∀ y ∈ Mmark.filtration.layer k,
      ∃ x ∈ D.filtration.layer k, φ x = y)

end Erdos3.RationalFilteredNilmanifold

end

end OAI

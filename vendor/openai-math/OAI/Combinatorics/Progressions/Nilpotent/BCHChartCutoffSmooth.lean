/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/BCHChartCutoffSmooth.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import OAI.Combinatorics.Progressions.Estimates.RightCosetEDistance
public import OAI.Combinatorics.Progressions.Geometry.LieCoordinateSmooth
public import OAI.Combinatorics.Progressions.Linear.RationalSpanCoordinates
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥} [TopologicalSpace L]

instance : TopologicalSpace (NilpotentLieBCHGroup L s hnil) :=
  TopologicalSpace.induced coord inferInstance

@[fun_prop]
theorem continuous_coord : Continuous (coord : NilpotentLieBCHGroup L s hnil → L) :=
  continuous_induced_dom

@[fun_prop]
theorem continuous_mk : Continuous (fun x : L => (⟨x⟩ : NilpotentLieBCHGroup L s hnil)) :=
  continuous_induced_rng.mpr continuous_id

def coordHomeomorph : NilpotentLieBCHGroup L s hnil ≃ₜ L where
  toFun := coord
  invFun x := ⟨x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_coord
  continuous_invFun := continuous_mk

instance [ContractibleSpace L] : ContractibleSpace (NilpotentLieBCHGroup L s hnil) :=
  (coordHomeomorph (hnil := hnil)).contractibleSpace

theorem isTopologicalGroup_of_continuous_lie [IsTopologicalAddGroup L] [ContinuousConstSMul ℚ L]
    (hlie : Continuous (fun z : L × L => ⁅z.1, z.2⁆)) :
    IsTopologicalGroup (NilpotentLieBCHGroup L s hnil) where
  continuous_mul := by
    change Continuous (fun z : NilpotentLieBCHGroup L s hnil × NilpotentLieBCHGroup L s hnil =>
      (⟨lieBCH s z.1.coord z.2.coord⟩ : NilpotentLieBCHGroup L s hnil))
    have hcoords : Continuous
        (fun z : NilpotentLieBCHGroup L s hnil × NilpotentLieBCHGroup L s hnil =>
          (z.1.coord, z.2.coord)) :=
      (continuous_coord.comp continuous_fst).prodMk (continuous_coord.comp continuous_snd)
    have hbch : Continuous
        (fun z : NilpotentLieBCHGroup L s hnil × NilpotentLieBCHGroup L s hnil =>
          lieBCH s z.1.coord z.2.coord) :=
      Continuous.comp
        (g := fun z : L × L => lieBCH s z.1 z.2)
        (f := fun z : NilpotentLieBCHGroup L s hnil × NilpotentLieBCHGroup L s hnil =>
          (z.1.coord, z.2.coord))
        (continuous_lieBCH (L := L) hlie s) hcoords
    exact (continuous_mk (hnil := hnil)).comp hbch
  continuous_inv := by
    change Continuous (fun z : NilpotentLieBCHGroup L s hnil =>
      (⟨-z.coord⟩ : NilpotentLieBCHGroup L s hnil))
    exact (continuous_mk (hnil := hnil)).comp (continuous_coord (hnil := hnil)).neg

section Real

variable [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L] [FiniteDimensional ℝ L]

instance : IsTopologicalGroup (NilpotentLieBCHGroup L s hnil) := by
  let : ContinuousConstSMul ℚ L := ⟨fun q => by
    simpa only [algebraMap_smul] using
      (continuous_const_smul (algebraMap ℚ ℝ q) : Continuous (fun x : L => algebraMap ℚ ℝ q • x))⟩
  exact isTopologicalGroup_of_continuous_lie continuous_lie_finiteDimensional

end Real

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Topology

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def basisHomeomorph (e : Basis ι ℝ L) :
    NilpotentLieBCHGroup L s hnil ≃ₜ (ι → ℝ) :=
  (coordHomeomorph (hnil := hnil)).trans e.equivFunL.toHomeomorph

@[simp]
theorem basisHomeomorph_apply (e : Basis ι ℝ L) (g : NilpotentLieBCHGroup L s hnil) :
    basisHomeomorph e g = e.equivFun g.coord := rfl

theorem closed_discrete_subgroup_of_grid (e : Basis ι ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l) :
    IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)) ∧
      IsDiscrete (Γ : Set (NilpotentLieBCHGroup L s hnil)) := by
  let f := basisHomeomorph (hnil := hnil) e
  have hsub : (Γ : Set (NilpotentLieBCHGroup L s hnil)) ⊆ f ⁻¹' realDenominatorGrid l :=
    fun g hg => hgrid g hg
  have hd : IsDiscrete (f ⁻¹' realDenominatorGrid l) :=
    (isDiscrete_realDenominatorGrid l hl).preimage f.continuous.continuousOn f.injective
  have hc : IsClosed (f ⁻¹' realDenominatorGrid l) :=
    (isClosed_realDenominatorGrid l).preimage f.continuous
  exact ⟨isClosed_of_subset_discrete_closed hsub hd hc, hd.mono hsub⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]

noncomputable def realLieSubalgebraOverRat (K : LieSubalgebra ℝ L) : LieSubalgebra ℚ L :=
  { K.toSubmodule.restrictScalars ℚ with lie_mem' := K.lie_mem }

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def realLieSubgroup (K : LieSubalgebra ℝ L) : Subgroup (NilpotentLieBCHGroup L s hnil) :=
  subgroup (realLieSubalgebraOverRat K)

variable [TopologicalSpace L]

variable [IsTopologicalAddGroup L] [ContinuousSMul ℝ L]

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

def coordinateBox (e : Basis ι ℝ L) (B : ℝ) : Set (NilpotentLieBCHGroup L s hnil) :=
  {g | ∀ i, |e.repr g.coord i| ≤ B}

variable [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

@[instance_reducible]
noncomputable def basisChartedSpace (e : Basis ι ℝ L) :
    ChartedSpace (ι → ℝ) (NilpotentLieBCHGroup L s hnil) :=
  (basisHomeomorph (hnil := hnil) e).isOpenEmbedding.singletonChartedSpace

variable (e : Basis ι ℝ L)

theorem isManifold_basis (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    IsManifold 𝓘(ℝ, ι → ℝ) n (NilpotentLieBCHGroup L s hnil) :=
  (basisHomeomorph e).isOpenEmbedding.isManifold_singleton

theorem contMDiff_basisHomeomorph (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) n (basisHomeomorph (hnil := hnil) e) :=
  contMDiff_isOpenEmbedding (basisHomeomorph e).isOpenEmbedding

theorem contMDiff_basisHomeomorph_symm (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) n (basisHomeomorph (hnil := hnil) e).symm := by
  let := basisChartedSpace (hnil := hnil) e
  apply ContMDiff.of_comp_isOpenEmbedding (basisHomeomorph e).isOpenEmbedding
  have heq : (basisHomeomorph (hnil := hnil) e) ∘ (basisHomeomorph e).symm = id :=
    funext (fun x => (basisHomeomorph e).apply_symm_apply x)
  rw [heq]
  exact contMDiff_id

variable [IsScalarTower ℚ ℝ L]

theorem lieGroup_basis (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    LieGroup 𝓘(ℝ, ι → ℝ) n (NilpotentLieBCHGroup L s hnil) := by
  let := basisChartedSpace (hnil := hnil) e
  refine
    { __ := isManifold_basis (hnil := hnil) e n
      contMDiff_mul := ?_
      contMDiff_inv := ?_ }
  · apply ContMDiff.of_comp_isOpenEmbedding (basisHomeomorph e).isOpenEmbedding
    have hcoords : ContMDiff (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ))
        𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) n
        (fun z : NilpotentLieBCHGroup L s hnil × NilpotentLieBCHGroup L s hnil =>
          (basisHomeomorph e z.1, basisHomeomorph e z.2)) :=
      ((contMDiff_basisHomeomorph e n).comp contMDiff_fst).prodMk_space
        ((contMDiff_basisHomeomorph e n).comp contMDiff_snd)
    have hbch := (contDiff_coordinateBCH (n := n) e s).contMDiff.comp hcoords
    convert hbch using 1; try rfl
    funext z
    simp only [Function.comp_apply, basisHomeomorph_apply, LinearEquiv.symm_apply_apply]
    rfl
  · apply ContMDiff.of_comp_isOpenEmbedding (basisHomeomorph e).isOpenEmbedding
    have hneg := (contDiff_neg (𝕜 := ℝ) (F := ι → ℝ) (n := n)).contMDiff.comp
      (contMDiff_basisHomeomorph (hnil := hnil) e n)
    have heq : (basisHomeomorph (hnil := hnil) e) ∘ (fun z => z⁻¹) =
        (fun z => -z) ∘ (basisHomeomorph e) := by
      funext z i
      change e.equivFun (-z.coord) i = -(e.equivFun z.coord i)
      simp only [map_neg, Pi.neg_apply]
    rw [heq]
    exact hneg

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]

local notation "E" => ℝ ⊗[ℚ] L
local notation "G" => NilpotentLieBCHGroup E s (realification_lowerCentralSeries_eq_bot hnil)

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] in

theorem realification_layer_reduction_in_cell {κ : Type*} [Fintype κ] (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ) (n : ℕ) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = (LieModule.lowerCentralSeries ℚ L L n).toSubmodule) :
    ∀ g : G, g.coord ∈ LieModule.lowerCentralSeries ℚ E E n →
      ∃ r ∈ (fun x : E => (⟨x⟩ : G)) ''
        boundedSpanCell (fun j => rationalLieInclusion (v j)) (rationalSpanGridStep e v l : ℝ),
      ∃ w ∈ Γ.map NilpotentLieBCHGroup.realificationHom,
        (r⁻¹ * g * w⁻¹).coord ∈ LieModule.lowerCentralSeries ℚ E E (n + 1) := by
  classical
  let m := rationalSpanGridStep e v l
  have hm : 0 < m := rationalSpanGridStep_pos e v l hl
  let vR : κ → E := fun j => rationalLieInclusion (v j)
  intro g hg
  have hspanreal : (LieModule.lowerCentralSeries ℚ E E n : Set E) =
      (Submodule.span ℝ (Set.range vR) : Set E) := realification_layer_eq_span n v hspan
  have hgspan : g.coord ∈ Submodule.span ℝ (Set.range vR) :=
    (Set.ext_iff.mp hspanreal g.coord).mp hg
  obtain ⟨r, hr, z, hdecomp⟩ := exists_bounded_span_remainder vR (m : ℝ)
    (by exact_mod_cast hm) g.coord hgspan
  let wQ : L := ∑ j, ((z j : ℚ) * (m : ℚ)) • v j
  have hwQ : (⟨wQ⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ := by
    have h := hinner (rationalSpanGridStep_combination e v l z)
    change (⟨e.equivFun.symm (e.equivFun wQ)⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ at h
    simpa only [LinearEquiv.symm_apply_apply] using h
  have hdecomp' : g.coord = r + rationalLieInclusion wQ := by
    change g.coord = r + rationalLieInclusion (∑ j, ((z j : ℚ) * (m : ℚ)) • v j)
    rw [rationalLieInclusion_integer_combination v z m]
    exact hdecomp
  have hrLayer : r ∈ LieModule.lowerCentralSeries ℚ E E n :=
    (Set.ext_iff.mp hspanreal r).mpr (boundedSpanCell_subset_span vR (m : ℝ) hr)
  have hwLayer : rationalLieInclusion wQ ∈ LieModule.lowerCentralSeries ℚ E E n := by
    have h := (LieModule.lowerCentralSeries ℚ E E n).sub_mem hg hrLayer
    rwa [hdecomp', add_sub_cancel_left] at h
  have hbracket : ⁅r, rationalLieInclusion wQ⁆ ∈ LieModule.lowerCentralSeries ℚ E E (n + 1) := by
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (by simp) hwLayer
  refine ⟨⟨r⟩, ⟨r, hr, rfl⟩, NilpotentLieBCHGroup.realificationHom ⟨wQ⟩,
    Subgroup.mem_map.mpr ⟨⟨wQ⟩, hwQ, rfl⟩, ?_⟩
  have hg' : g = (⟨r + rationalLieInclusion wQ⟩ : G) := NilpotentLieBCHGroup.ext hdecomp'
  rw [hg']
  exact NilpotentLieBCHGroup.additive_remainder_mem (realification_lowerCentralSeries_eq_bot hnil)
    (LieModule.lowerCentralSeries ℚ E E (n + 1)) r (rationalLieInclusion wQ) hbracket

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem realificationHom_coordinates (e : Basis ι ℚ L) (g : NilpotentLieBCHGroup L s hnil) :
    (e.baseChange ℝ).equivFun (realificationHom g).coord = fun i => (e.repr g.coord i : ℝ) := by
  funext i
  exact rationalLieInclusion_coordinates e g.coord i

theorem realification_subgroup_grid (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    ∀ g ∈ Γ.map realificationHom,
      (e.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid l := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
  rw [realificationHom_coordinates, real_cast_mem_denominatorGrid_iff]
  apply hgrid
  change (⟨e.equivFun.symm (e.equivFun a.coord)⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ
  simpa only [LinearEquiv.symm_apply_apply] using ha

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem realification_subgroup_closed_discrete (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    IsClosed (Γ.map realificationHom : Set
      (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))) ∧
    IsDiscrete (Γ.map realificationHom : Set
      (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))) :=
  closed_discrete_subgroup_of_grid (e.baseChange ℝ) (Γ.map realificationHom) l hl
    (realification_subgroup_grid e Γ l hgrid)

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Set Manifold
open scoped Manifold ContDiff Topology

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Set Manifold
open scoped Manifold ContDiff Topology

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

end OAI

/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/RealifiedBCHFiniteAtlas.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import OAI.Combinatorics.Progressions.Estimates.ImageRepresentatives
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
  (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
  (hc : ∀ i j k, RationalHeightLE (c i j k) H)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
  (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)

noncomputable def quotientCoordinateChart (z : NilpotentLieBCHGroup L s hnil) :
    OpenPartialHomeomorph (ι → ℝ) (NilpotentLieBCHGroup L s hnil ⧸ Γ) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let f := fun v : ι → ℝ => (QuotientGroup.mk (z * (basisHomeomorph e).symm v) : _ ⧸ Γ)
  let U := {v : ι → ℝ | ∀ i, |v i| < bchInjectivityRadius s (Fintype.card ι) H l}
  have hi : Set.InjOn f U := (quotient_coordinate_injOn e c hstructure hc Γ l hl hgrid z).mono
    (fun _ hx i => (hx i).le)
  have hf : Continuous f := QuotientGroup.continuous_mk.comp
    (continuous_const.mul (basisHomeomorph e).symm.continuous)
  have ho : IsOpenMap f := QuotientGroup.isOpenMap_coe.comp
    ((Homeomorph.mulLeft z).isOpenMap.comp (basisHomeomorph e).symm.isOpenMap)
  have hU : IsOpen U := by
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt (continuous_apply i).abs continuous_const)
  exact OpenPartialHomeomorph.ofContinuousOpen (hi.toPartialEquiv f U) hf.continuousOn ho hU

theorem quotientCoordinateChart_target (z : NilpotentLieBCHGroup L s hnil) :
    (quotientCoordinateChart e c hstructure hc Γ l hl hgrid z).target =
      (fun v : ι → ℝ => (QuotientGroup.mk (z * (basisHomeomorph e).symm v) : _ ⧸ Γ)) ''
        {v : ι → ℝ | ∀ i, |v i| < bchInjectivityRadius s (Fintype.card ι) H l} := rfl

theorem quotientCoordinateChart_center_mem (z : NilpotentLieBCHGroup L s hnil) :
    (QuotientGroup.mk z : _ ⧸ Γ) ∈ (quotientCoordinateChart e c hstructure hc Γ l hl hgrid z).target := by
  have hzero : (basisHomeomorph (hnil := hnil) e).symm 0 = 1 := by
    apply (basisHomeomorph e).injective
    simp only [Homeomorph.apply_symm_apply, basisHomeomorph_apply, coord_one, map_zero]
  rw [quotientCoordinateChart_target]
  refine ⟨0, ?_, ?_⟩
  · intro i
    simpa only [Pi.zero_apply, abs_zero] using bchInjectivityRadius_pos s (Fintype.card ι) H l
  · simp only [hzero, mul_one]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct NNReal

namespace NilpotentLieBCHGroup

end NilpotentLieBCHGroup

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Set Manifold
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
  (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
  (hc : ∀ i j k, RationalHeightLE (c i j k) H)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
  (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)

@[instance_reducible]
noncomputable def quotientChartedSpace : ChartedSpace (ι → ℝ) (NilpotentLieBCHGroup L s hnil ⧸ Γ) where
  atlas := Set.range (fun z => (quotientCoordinateChart e c hstructure hc Γ l hl hgrid z).symm)
  chartAt := fun x => (quotientCoordinateChart e c hstructure hc Γ l hl hgrid x.out).symm
  mem_chart_source := fun x => by
    simpa only [OpenPartialHomeomorph.symm_source, QuotientGroup.out_eq'] using
      quotientCoordinateChart_center_mem e c hstructure hc Γ l hl hgrid x.out
  chart_mem_atlas := fun x => ⟨x.out, rfl⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Set Manifold
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem shifted_center_power_bound (A B : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    ((p + A) + B) ^ B ≤ (p + (A + B + 2 : ℕ)) ^ (A + B + 2) := by
  have hbase : (p + A) + B ≤ p + (A + B + 2 : ℕ) := by push_cast; linarith
  apply (pow_le_pow_left₀ (by positivity) hbase B).trans
  exact pow_le_pow_right₀
    (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) A, Nat.cast_nonneg (α := ℝ) B]) (by omega)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

end Erdos3

end

end OAI

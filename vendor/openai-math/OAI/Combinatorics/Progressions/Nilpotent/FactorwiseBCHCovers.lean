/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/FactorwiseBCHCovers.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.Group.Subgroup.Finite
public import OAI.Combinatorics.Progressions.Estimates.ControlledSurjectiveReconstruction
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)]
  [∀ a, LieAlgebra ℚ (M a)] {s : ℕ}

noncomputable def piBCHSubgroup (F : ∀ a, NilpotentLieFiltration (M a) s)
    (Δ : ∀ a, Subgroup (F a).Group) : Subgroup (NilpotentLieFiltration.pi F).Group :=
  ⨅ a, (Δ a).comap (map (hM := (F a).lowerCentralSeries_eq_bot) (liePiEval a))

theorem mem_piBCHSubgroup (F : ∀ a, NilpotentLieFiltration (M a) s)
    (Δ : ∀ a, Subgroup (F a).Group) (g : (NilpotentLieFiltration.pi F).Group) :
    g ∈ piBCHSubgroup F Δ ↔ ∀ a, (⟨g.coord a⟩ : (F a).Group) ∈ Δ a := by
  simp only [piBCHSubgroup, Subgroup.mem_iInf, Subgroup.mem_comap]
  rfl

variable [Fintype α] {κ : α → Type*} [∀ a, Fintype (κ a)]

theorem pi_basis_equivFun_symm_apply (f : ∀ a, Basis (κ a) ℚ (M a))
    (x : (Σ a, κ a) → ℚ) (a : α) :
    (Pi.basis f).equivFun.symm x a = (f a).equivFun.symm (fun i => x ⟨a, i⟩) := by
  apply (f a).equivFun.injective
  funext i
  change (Pi.basis f).equivFun ((Pi.basis f).equivFun.symm x) ⟨a, i⟩ = _
  simp only [LinearEquiv.apply_symm_apply]

theorem piBCHSubgroup_coordinates (F : ∀ a, NilpotentLieFiltration (M a) s)
    (f : ∀ a, Basis (κ a) ℚ (M a)) (Δ : ∀ a, Subgroup (F a).Group)
    (x : (Σ a, κ a) → ℚ) :
    x ∈ bchSubgroupCoordinates (Pi.basis f) (piBCHSubgroup F Δ) ↔
      ∀ a, (fun i => x ⟨a, i⟩) ∈ bchSubgroupCoordinates (f a) (Δ a) := by
  change (⟨(Pi.basis f).equivFun.symm x⟩ : (NilpotentLieFiltration.pi F).Group) ∈
    piBCHSubgroup F Δ ↔ _
  rw [mem_piBCHSubgroup]
  simp only [pi_basis_equivFun_symm_apply, bchSubgroupCoordinates, Set.mem_ofPred_eq]

theorem piBCHSubgroup_inner_grid (F : ∀ a, NilpotentLieFiltration (M a) s)
    (f : ∀ a, Basis (κ a) ℚ (M a)) (Δ : ∀ a, Subgroup (F a).Group) (m : ℕ)
    (hin : ∀ a, scaledIntegerGrid m ⊆ bchSubgroupCoordinates (f a) (Δ a)) :
    scaledIntegerGrid m ⊆ bchSubgroupCoordinates (Pi.basis f) (piBCHSubgroup F Δ) := by
  rintro x ⟨z, rfl⟩
  apply (piBCHSubgroup_coordinates F f Δ _).mpr
  intro a
  exact hin a ⟨fun i => z ⟨a, i⟩, rfl⟩

theorem piBCHSubgroup_outer_grid (F : ∀ a, NilpotentLieFiltration (M a) s)
    (f : ∀ a, Basis (κ a) ℚ (M a)) (Δ : ∀ a, Subgroup (F a).Group) (m : ℕ)
    (hout : ∀ a, bchSubgroupCoordinates (f a) (Δ a) ⊆ denominatorGrid m) :
    bchSubgroupCoordinates (Pi.basis f) (piBCHSubgroup F Δ) ⊆ denominatorGrid m := by
  intro x hx
  have h := (piBCHSubgroup_coordinates F f Δ x).mp hx
  choose z hz using fun a => hout a (h a)
  exact ⟨fun i => z i.1 i.2, fun i => hz i.1 i.2⟩

end Erdos3

end

section

namespace Erdos3

open NilpotentLieBCHGroup

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)] [∀ a, LieAlgebra ℚ (M a)]
  [DecidableEq α] {s : ℕ}

def liePiSingle (a : α) : M a →ₗ⁅ℚ⁆ (∀ a, M a) where
  toLinearMap := LinearMap.single ℚ M a
  map_lie' {x y} := by
    ext i
    change Pi.single a ⁅x, y⁆ i = ⁅Pi.single a x i, Pi.single a y i⁆
    by_cases hi : i = a
    · subst i
      simp only [Pi.single_eq_same]
    · simp only [Pi.single_eq_of_ne hi, lie_zero]

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

variable {α : Type*} [Fintype α] [DecidableEq α] {M : α → Type*}
  [∀ a, LieRing (M a)] [∀ a, LieAlgebra ℚ (M a)] {s : ℕ}
  (F : ∀ a, NilpotentLieFiltration (M a) s)
  {κ : α → Type*} [∀ a, Fintype (κ a)] (f : ∀ a, Basis (κ a) ℚ (M a))

end Erdos3

end

end OAI

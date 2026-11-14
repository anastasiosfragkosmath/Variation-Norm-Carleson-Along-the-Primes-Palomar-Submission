/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/ControlledSurjectiveReconstruction.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Dynamics.ReconstructionBudget
public import OAI.Combinatorics.Progressions.Lattices.FilteredLatticePowerIndex
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

theorem exists_sharp_normal_cover (e : Basis ι ℚ L) (Γ Λ₀ : Subgroup F.Group)
    (l m₀ : ℕ) (hl : 0 < l) (hm₀ : 0 < m₀)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (htarget : scaledIntegerGrid m₀ ⊆ bchSubgroupCoordinates e Λ₀) :
    ∃ Λ : Subgroup F.Group,
      Λ ≤ Λ₀ ∧ Λ ≤ Γ ∧ (Λ.subgroupOf Γ).Characteristic ∧ (Λ.subgroupOf Γ).Normal ∧
      (Λ.subgroupOf Γ).FiniteIndex ∧ Λ.relIndex Γ ≤ (l * m₀) ^ Fintype.card ι ∧
      scaledIntegerGrid ((l * m₀) * l) ⊆ bchSubgroupCoordinates e Λ ∧
      bchSubgroupCoordinates e Λ ⊆ denominatorGrid ((l * m₀) * l) := by
  let m := l * m₀
  obtain ⟨hfinite, hindex⟩ := F.subgroupPowerCover_index_le e Γ l hl houter m
    (Nat.mul_pos hl hm₀)
  exact ⟨subgroupPowerCover Γ m,
    subgroupPowerCover_le_of_grid e Γ Λ₀ l m₀ m houter htarget dvd_rfl,
    subgroupPowerCover_le Γ m, inferInstance, inferInstance, hfinite, hindex,
    subgroupPowerCover_grid e Γ l m hinner houter⟩

theorem exists_normal_cover_exp_quadratic (e : Basis ι ℚ L) (Γ Λ₀ : Subgroup F.Group)
    (l m₀ : ℕ) (hl : 0 < l) (hm₀ : 0 < m₀)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (htarget : scaledIntegerGrid m₀ ⊆ bchSubgroupCoordinates e Λ₀)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hlb : (l : ℝ) ≤ Real.exp p) (hm₀b : (m₀ : ℝ) ≤ Real.exp p) :
    ∃ Λ : Subgroup F.Group,
      Λ ≤ Λ₀ ∧ Λ ≤ Γ ∧ (Λ.subgroupOf Γ).Characteristic ∧ (Λ.subgroupOf Γ).Normal ∧
      (Λ.subgroupOf Γ).FiniteIndex ∧ (Λ.relIndex Γ : ℝ) ≤ Real.exp (2 * p ^ 2) ∧
      ∃ ℓ : ℕ, 0 < ℓ ∧ (ℓ : ℝ) ≤ Real.exp ((p + 2) ^ 2) ∧
        scaledIntegerGrid ℓ ⊆ bchSubgroupCoordinates e Λ ∧
        bchSubgroupCoordinates e Λ ⊆ denominatorGrid ℓ := by
  obtain ⟨Λ, hΛ₀, hΛ, hchar, hnormal, hfinite, hindex, hin, hout⟩ :=
    F.exists_sharp_normal_cover e Γ Λ₀ l m₀ hl hm₀ hinner houter htarget
  refine ⟨Λ, hΛ₀, hΛ, hchar, hnormal, hfinite, ?_, (l * m₀) * l,
    Nat.mul_pos (Nat.mul_pos hl hm₀) hl, powerCover_grid_allowance_le_exp l m₀ hp hlb hm₀b,
    hin, hout⟩
  exact (Nat.cast_le.mpr hindex).trans (powerCover_index_allowance_le_exp l m₀ _ hp hlb hm₀b hd)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

end Erdos3

end

end OAI

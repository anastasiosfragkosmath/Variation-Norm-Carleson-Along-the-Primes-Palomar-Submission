/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Lattices/SourceLatticeCover.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Linear.RationalTaggedSpanProjection
@[expose] public section

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup

noncomputable def withLattice {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (Λ : Subgroup D.filtration.Group)
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N) :
    RationalFilteredNilmanifold L s d :=
  { D with lattice := Λ, grid := N, grid_pos := hN, inner_grid := hin, outer_grid := hout }

theorem withLattice_geometry {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (Λ : Subgroup D.filtration.Group)
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)
    {p q : ℝ} (hD : D.GeometryComplexityLE p) (hpq : p ≤ q) (hNb : (N : ℝ) ≤ Real.exp q) :
    (D.withLattice Λ N hN hin hout).GeometryComplexityLE q :=
  ⟨hD.1.trans hpq, hNb, fun i j k => (hD.2.2.1 i j k).trans hpq,
    fun i j k => (hD.2.2.2 i j k).trans hpq⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
  (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)
  (Λ : Subgroup (D.raiseStep hst).filtration.Group)

variable (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
  (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped Matrix

theorem bchSubgroupCoordinates_comap_ofSteps
    {ι κ L M : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}
    (b : Basis ι ℚ L) (e : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    (Γ : Subgroup (NilpotentLieBCHGroup M t hM)) :
    bchSubgroupCoordinates b (Γ.comap (mapOfSteps (hL := hL) φ)) =
      (LinearMap.toMatrix b e φ.toLinearMap).mulVec ⁻¹' bchSubgroupCoordinates e Γ := by
  ext x
  change ((⟨φ (b.equivFun.symm x)⟩ : NilpotentLieBCHGroup M t hM) ∈ Γ) ↔
    ((⟨e.equivFun.symm (LinearMap.toMatrix b e φ.toLinearMap *ᵥ x)⟩ :
      NilpotentLieBCHGroup M t hM) ∈ Γ)
  rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply]
  rfl

namespace RationalFilteredNilmanifold

theorem exists_native_source_cover :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M] {s t d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∃ Λ : Subgroup D.filtration.Group,
        Λ ≤ D.lattice ∧ (Λ.subgroupOf D.lattice).Characteristic ∧
        (Λ.subgroupOf D.lattice).Normal ∧ (Λ.subgroupOf D.lattice).FiniteIndex ∧
        (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          (D.withLattice Λ N hN hin hout).GeometryComplexityLE ((p + C) ^ C) ∧
          Λ ≤ E.lattice.comap (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ) := by
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + 2) ^ 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + 2 * R ^ 2 + (R + 2) ^ 2)
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ s t d e D E φ p hp hD hE hφ
  classical
  let A := LinearMap.toMatrix D.basis E.basis φ.toLinearMap
  have hAb : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power A hp 1
      (by simpa only [Fintype.card_fin] using hE.1)
      (by simpa only [Fintype.card_fin] using hD.1)
    intro i j
    have h := ((rationalLogHeight_le_iff _ p).mp (hφ i j)).2
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact h.trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  let N₀ := E.grid * matrixDenominator A
  let Λ₀ := E.lattice.comap (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ)
  have hN₀ : 0 < N₀ := Nat.mul_pos E.grid_pos (matrixDenominator_pos A)
  have hgrid : scaledIntegerGrid N₀ ⊆ bchSubgroupCoordinates D.basis Λ₀ := by
    rw [bchSubgroupCoordinates_comap_ofSteps
      (hL := D.filtration.lowerCentralSeries_eq_bot) D.basis E.basis φ E.lattice]
    intro x hx
    exact E.inner_grid (matrix_mulVec_fine_grid A E.grid hx)
  let r := p + (p + 2) ^ 3
  have hpr : p ≤ r := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hr : 0 ≤ r := hp.trans hpr
  have hN₀b : (N₀ : ℝ) ≤ Real.exp r := by
    rw [show (N₀ : ℝ) = (E.grid : ℝ) * matrixDenominator A by exact Nat.cast_mul _ _]
    exact (mul_le_mul hE.2.1 hAb (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  obtain ⟨Λ, htarget, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hNb, hin, hout⟩ :=
    D.filtration.exists_normal_cover_exp_quadratic D.basis D.lattice Λ₀
      D.grid N₀ D.grid_pos hN₀ D.inner_grid D.outer_grid hgrid hr
      (by simpa only [Fintype.card_fin] using hD.1.trans hpr)
      (hD.2.1.trans (Real.exp_le_exp.mpr hpr)) hN₀b
  have htotal : r + 2 * r ^ 2 + (r + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [X, R, r, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := by nlinarith [sq_nonneg r, sq_nonneg (r + 2)]
  have hiC : 2 * r ^ 2 ≤ (p + C) ^ C := by nlinarith [sq_nonneg (r + 2)]
  have hgC : (r + 2) ^ 2 ≤ (p + C) ^ C := by nlinarith [sq_nonneg r]
  exact ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hiC),
    N, hN, hin, hout,
    D.withLattice_geometry Λ N hN hin hout hD (hpr.trans hrC)
      (hNb.trans (Real.exp_le_exp.mpr hgC)), htarget⟩

end RationalFilteredNilmanifold
end Erdos3

end

end OAI

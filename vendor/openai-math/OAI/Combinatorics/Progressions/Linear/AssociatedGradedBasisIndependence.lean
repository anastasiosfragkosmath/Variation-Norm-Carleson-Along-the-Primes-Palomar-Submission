/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/AssociatedGradedBasisIndependence.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Polynomial.RealCoordinatePolynomialSymbol
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def gradedPieceProjection (j : ℕ) : L →ₗ[ℚ] F.AssociatedGraded :=
  (F.associatedGradedBasis b ω hlayers).repr.symm.toLinearMap.comp
    (b.repr.toLinearMap.comp (basisGradeProjection b ω j))

theorem gradedPieceProjection_coordinate (j : ℕ) (v : L) (i : ι) :
    (F.associatedGradedBasis b ω hlayers).repr (F.gradedPieceProjection b ω hlayers j v) i =
      if ω i = j then b.repr v i else 0 := by
  simp only [gradedPieceProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, basisGradeProjection_repr]

theorem gradedPieceProjection_eq_pieceMap (j : ℕ) (v : F.layer j) :
    F.gradedPieceProjection b ω hlayers j v = F.associatedGradedPieceMap j v := by
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  ext i
  rw [F.gradedPieceProjection_coordinate, F.associatedGradedPieceMap_coordinate]
  simp only [eq_comm]

theorem gradedRefiltrationLayer_eq_inf_comap (U : LieSubalgebra ℚ F.AssociatedGraded) (j : ℕ) :
    F.gradedRefiltrationLayer U j =
      F.layer j ⊓ U.toSubmodule.comap (F.gradedPieceProjection b ω hlayers j) := by
  ext v
  rw [F.mem_gradedRefiltrationLayer, Submodule.mem_inf, Submodule.mem_comap]
  constructor
  · rintro ⟨hv, hU⟩
    exact ⟨hv, (F.gradedPieceProjection_eq_pieceMap b ω hlayers j ⟨v, hv⟩).symm ▸ hU⟩
  · rintro ⟨hv, hU⟩
    exact ⟨hv, F.gradedPieceProjection_eq_pieceMap b ω hlayers j ⟨v, hv⟩ ▸ hU⟩

theorem real_gradedPieceProjection_coordinate (j : ℕ) (v : ℝ ⊗[ℚ] L) (i : ι) :
    ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr
      ((F.gradedPieceProjection b ω hlayers j).baseChange ℝ v) i =
      if ω i = j then (b.baseChange ℝ).repr v i else 0 := by
  induction v using TensorProduct.inductionOn with
  | tmul a v =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      F.gradedPieceProjection_coordinate, Basis.baseChange_repr_tmul]
    split_ifs <;> simp only [zero_smul]
  | add v z hv hz =>
    simp only [map_add, Finsupp.add_apply, hv, hz]
    split_ifs <;> simp only [add_zero]

theorem realGradedSymbolPolynomial_coefficient_of_polynomial
    (w : σ → ℕ) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (α : σ →₀ ℕ) :
    coefficients (F.realGradedSymbolPolynomial b ω hlayers w
      (F.realSymbolOfPolynomial b ω hlayers w p)) α =
        (F.gradedPieceProjection b ω hlayers (Finsupp.weight w α)).baseChange ℝ (coefficients p α) := by
  apply ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr.injective
  ext i
  rw [F.real_gradedPieceProjection_coordinate]
  by_cases h : Finsupp.weight w α = ω i
  · rw [ite_eq_left h.symm]
    exact (F.realGradedSymbolPolynomial_coordinate b ω hlayers w _ ⟨(α, i), h⟩).trans
      (F.realSymbolOfPolynomial_coordinate b ω hlayers w p ⟨(α, i), h⟩)
  · rw [ite_eq_right (Ne.symm h)]
    exact F.realGradedSymbolPolynomial_coordinate_of_ne b ω hlayers w _ α i h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hb : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hb : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

end Erdos3.NilpotentLieFiltration

end

end OAI

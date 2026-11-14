/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/ReducedSquareSymbol.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Polynomial.SquarePolynomialCoordinates
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s)

theorem quotientLie_mem_iff (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
    (j : ℕ) (x : L) :
    lieQuotientMap I x ∈ (F.quotientLie I hI).layer j ↔ x ∈ F.layer j ⊔ I.toSubmodule := by
  change x ∈ ((F.layer j).map I.toSubmodule.mkQ).comap I.toSubmodule.mkQ ↔ _
  rw [Submodule.comap_map_mkQ, sup_comm]

noncomputable def quotientGradedMap (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule) :
    F.AssociatedGraded →ₗ⁅ℚ⁆ (F.quotientLie I hI).AssociatedGraded :=
  F.associatedGradedMap (F.quotientLie I hI) (lieQuotientMap I)
    (fun _ _ hx => F.quotientLie_mem I hI hx)

@[simp] theorem quotientGradedMap_piece (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
    (j : ℕ) (x : F.layer j) :
    F.quotientGradedMap I hI (F.associatedGradedPieceMap j x) =
      (F.quotientLie I hI).associatedGradedPieceMap j
        ⟨lieQuotientMap I x, F.quotientLie_mem I hI x.property⟩ :=
  F.associatedGradedMap_piece _ _ _ j x

theorem quotientGradedMap_piece_eq_zero_iff (I : LieIdeal ℚ L)
    (hI : F.layer (t + 1) ≤ I.toSubmodule) (j : ℕ) (x : F.layer j) :
    F.quotientGradedMap I hI (F.associatedGradedPieceMap j x) = 0 ↔
      (x : L) ∈ F.layer (j + 1) ⊔ I.toSubmodule := by
  rw [F.quotientGradedMap_piece, associatedGradedPieceMap_eq_zero_iff,
    F.quotientLie_mem_iff]

variable (F : NilpotentLieFiltration L (s + 1))

noncomputable def quotientTopGradedMap : F.AssociatedGraded →ₗ⁅ℚ⁆ F.quotientTop.AssociatedGraded :=
  F.quotientGradedMap (F.layerIdeal (s + 1)) le_rfl

theorem quotientTopGradedMap_piece_eq_zero_iff (j : ℕ) (hj : j ≤ s) (x : F.layer j) :
    F.quotientTopGradedMap (F.associatedGradedPieceMap j x) = 0 ↔ (x : L) ∈ F.layer (j + 1) := by
  have hle : (F.layerIdeal (s + 1)).toSubmodule ≤ F.layer (j + 1) :=
    F.antitone (Nat.add_le_add_right hj 1)
  have h := F.quotientGradedMap_piece_eq_zero_iff (F.layerIdeal (s + 1)) (t := s) le_rfl j x
  rw [sup_eq_left.mpr hle] at h
  convert h using 1
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

variable (h : σ → ℚ) (e m : L)
  (p : F.adaptedLieSubalgebra (fun _ : σ => 1))

theorem normalizedRelativeLog_shifted :
    F.normalizedRelativeLog h e m p ∈ F.shiftedAdaptedIdeal (fun _ : σ => 1) := by
  apply (F.polynomialSymbolMap_eq_zero_iff (fun _ => 1) _).mp
  change F.polynomialSymbolMap (fun _ => 1)
    (lieBCH s (F.normalizedShiftAdapted h (-e) (-m) p) (-p)) = 0
  rw [map_lieBCH, map_neg]
  have he : F.polynomialSymbolMap (fun _ => 1) (F.normalizedShiftAdapted h (-e) (-m) p) =
      F.polynomialSymbolMap (fun _ => 1) p := by
    apply (F.polynomialSymbolMap_eq_iff (fun _ => 1) _ _).mpr
    exact F.normalizedShiftLog_sub_coefficient_mem (fun _ => 1) (by simp) h (-e) (-m)
      ((F.mem_adaptedSubmodule (fun _ => 1) _).mp p.property)
  rw [he]
  exact congrArg NilpotentLieBCHGroup.coord
    (mul_inv_cancel (⟨F.polynomialSymbolMap (fun _ => 1) p⟩ :
      F.PolynomialSymbolGroup (fun _ : σ => 1)))

theorem normalizedRelativeLog_horizontal
    (hzero : coefficients (normalizedShiftLog s h (-e) (-m) p.val - p.val) 0 ∈ F.layer 2) :
    coefficients (F.normalizedRelativeLog h e m p).val 0 ∈ F.layer 2 := by
  apply (lieQuotientMap_eq_zero (F.layerIdeal 2) _).mp
  rw [← eval_zero_eq_coefficient]
  change lieQuotientMap (F.layerIdeal 2)
    (eval (0 : σ → ℚ) ((F.adaptedLieSubalgebra (fun _ => 1)).incl
      (lieBCH s (F.normalizedShiftAdapted h (-e) (-m) p) (-p)))) = 0
  rw [map_lieBCH, eval_lieBCH, F.horizontal_bch, map_neg, map_neg, map_neg]
  have hz := (lieQuotientMap_eq_zero (F.layerIdeal 2) _).mpr hzero
  rw [← eval_zero_eq_coefficient, map_sub, map_sub] at hz
  rw [sub_eq_add_neg] at hz
  exact hz

theorem normalizedRelativeLog_mem
    (hzero : coefficients (normalizedShiftLog s h (-e) (-m) p.val - p.val) 0 ∈ F.layer 2) :
    F.normalizedRelativeLog h e m p ∈ F.normalizedRelativeSubmodule (fun _ : σ => 1) :=
  ⟨F.normalizedRelativeLog_shifted h e m p, F.normalizedRelativeLog_horizontal h e m p hzero⟩

variable [Fintype σ]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

noncomputable def reducedSquareGradedDiagonalPiece (j : ℕ) :
    F.layer j →ₗ[ℚ] F.squareFiltration.quotientTop.AssociatedGraded :=
  F.squareFiltration.quotientTopGradedMap.toLinearMap.comp (F.squareGradedDiagonalPiece j)

noncomputable def reducedSquareGradedRelativePiece (j : ℕ) (hj : 1 ≤ j) :
    F.layer (j + 1) →ₗ[ℚ] F.squareFiltration.quotientTop.AssociatedGraded :=
  F.squareFiltration.quotientTopGradedMap.toLinearMap.comp (F.squareGradedRelativePiece j hj)

theorem reducedSquareGradedDiagonalPiece_eq_zero_iff (j : ℕ) (hj : j ≤ s) (x : F.layer j) :
    F.reducedSquareGradedDiagonalPiece j x = 0 ↔ (x : L) ∈ F.layer (j + 1) := by
  change F.squareFiltration.quotientTopGradedMap
    (F.squareFiltration.associatedGradedPieceMap j (F.squareDiagonalLayer j x)) = 0 ↔ _
  rw [F.squareFiltration.quotientTopGradedMap_piece_eq_zero_iff j hj]
  exact (F.squareFiltration.associatedGradedPieceMap_eq_zero_iff j _).symm.trans
    (F.squareGradedDiagonalPiece_eq_zero_iff j x)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

variable [Fintype σ] (h : σ → ℚ) (e m : L)
  (p : F.adaptedLieSubalgebra (fun _ : σ => 1))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def reducedSquarePolynomialMap :
    F.squareFiltration.adaptedLieSubalgebra w →ₗ⁅ℚ⁆
      F.squareFiltration.quotientTop.adaptedLieSubalgebra w :=
  F.squareFiltration.filteredPolynomialMap F.squareFiltration.quotientTop
    (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)))
    (fun _ _ hx => F.squareFiltration.quotientLie_mem _ le_rfl hx) w

noncomputable def reducedSquareSymbolMap :
    F.squareFiltration.PolynomialSymbol w →ₗ⁅ℚ⁆ F.squareFiltration.quotientTop.PolynomialSymbol w :=
  F.squareFiltration.filteredPolynomialSymbolMap F.squareFiltration.quotientTop
    (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)))
    (fun _ _ hx => F.squareFiltration.quotientLie_mem _ le_rfl hx) w

@[simp] theorem reducedSquareSymbolMap_symbol (r : F.squareFiltration.adaptedLieSubalgebra w) :
    F.reducedSquareSymbolMap w (F.squareFiltration.polynomialSymbolMap w r) =
      F.squareFiltration.quotientTop.polynomialSymbolMap w (F.reducedSquarePolynomialMap w r) := rfl

variable [Fintype σ] (h : σ → ℚ) (e m : L)
  (p : F.adaptedLieSubalgebra (fun _ : σ => 1))

end Erdos3.NilpotentLieFiltration

end

end OAI

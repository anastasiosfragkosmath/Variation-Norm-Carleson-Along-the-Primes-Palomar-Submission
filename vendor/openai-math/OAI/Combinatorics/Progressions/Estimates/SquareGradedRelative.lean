/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/SquareGradedRelative.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Polynomial.RankPolynomialFactorization
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial

noncomputable def unitMonomial (n : ℕ) : Unit →₀ ℕ := Finsupp.single () n

@[simp] theorem weight_unitMonomial (n : ℕ) :
    Finsupp.weight (fun _ : Unit => 1) (unitMonomial n) = n := by
  simp [unitMonomial, Finsupp.weight_single]

@[simp] theorem unitMonomial_weight (α : Unit →₀ ℕ) :
    unitMonomial (Finsupp.weight (fun _ : Unit => 1) α) = α := by
  have h : α = Finsupp.single () (α ()) := by
    apply Finsupp.ext
    intro i
    cases i
    simp
  rw [h]
  simp [unitMonomial, Finsupp.weight_single]

theorem unitMonomial_injective : Function.Injective unitMonomial := by
  intro m n h
  have hh := congrArg (Finsupp.weight (fun _ : Unit => 1)) h
  simpa only [weight_unitMonomial] using hh

@[simp] theorem unitMonomial_add (m n : ℕ) :
    unitMonomial (m + n) = unitMonomial m + unitMonomial n :=
  Finsupp.single_add _ _ _

namespace NilpotentLieFiltration

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

abbrev AssociatedGraded (F : NilpotentLieFiltration L s) :=
  F.PolynomialSymbol (fun _ : Unit => 1)

noncomputable def associatedGradedIndexEquiv (ω : ι → ℕ) :
    SymbolBasisIndex (fun _ : Unit => 1) ω ≃ ι where
  toFun z := z.val.2
  invFun i := ⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact (congrArg unitMonomial z.property.symm).trans (unitMonomial_weight z.val.1)
    · rfl
  right_inv _ := rfl

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def associatedGradedBasis : Basis ι ℚ F.AssociatedGraded :=
  (F.polynomialSymbolBasis b ω hlayers (fun _ : Unit => 1)).reindex (associatedGradedIndexEquiv ω)

@[simp] theorem associatedGradedBasis_apply (i : ι) :
    F.associatedGradedBasis b ω hlayers i =
      F.polynomialSymbolBasis b ω hlayers (fun _ : Unit => 1)
        ⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩ := by
  rw [associatedGradedBasis, Basis.reindex_apply]
  rfl

theorem associatedGradedBasis_repr (x : F.AssociatedGraded) (i : ι) :
    (F.associatedGradedBasis b ω hlayers).repr x i =
      (F.polynomialSymbolBasis b ω hlayers (fun _ : Unit => 1)).repr x
        ⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩ := by
  rw [associatedGradedBasis, Basis.repr_reindex_apply]
  rfl

theorem associatedGradedBasis_bracket (i j k : ι) :
    (F.associatedGradedBasis b ω hlayers).repr
      ⁅F.associatedGradedBasis b ω hlayers i, F.associatedGradedBasis b ω hlayers j⁆ k =
      if ω i + ω j = ω k then b.repr ⁅b i, b j⁆ k else 0 := by
  classical
  rw [F.associatedGradedBasis_repr, F.associatedGradedBasis_apply,
    F.associatedGradedBasis_apply, F.polynomialSymbolBasis_bracket]
  simp only [← unitMonomial_add, unitMonomial_injective.eq_iff]

noncomputable def associatedGradedFiltration : NilpotentLieFiltration F.AssociatedGraded s :=
  F.polynomialSymbolFiltration (fun _ : Unit => 1)

theorem associatedGradedFiltration_layer (j : ℕ) :
    F.associatedGradedFiltration.layer j =
      Submodule.span ℚ (F.associatedGradedBasis b ω hlayers '' {i | j ≤ ω i}) := by
  rw [associatedGradedFiltration, F.polynomialSymbolFiltration_layer b ω hlayers]
  congr 1
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.val.2, hz, ?_⟩
    rw [F.associatedGradedBasis_apply]
    congr 1
    exact (associatedGradedIndexEquiv ω).left_inv z
  · rintro ⟨i, hi, rfl⟩
    refine ⟨⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩, hi, ?_⟩
    exact (F.associatedGradedBasis_apply b ω hlayers i).symm

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def gradedMonomialLinear (j : ℕ) :
    F.layer j →ₗ[ℚ] F.adaptedLieSubalgebra (fun _ : Unit => 1) where
  toFun v := ⟨monomial (unitMonomial j) (v : L),
    F.monomial_mem_adaptedSubmodule (fun _ : Unit => 1) (unitMonomial j)
      (by simpa only [weight_unitMonomial] using v.property)⟩
  map_add' x y := by
    apply Subtype.ext
    exact TensorProduct.tmul_add _ _ _
  map_smul' a x := by
    apply Subtype.ext
    exact TensorProduct.tmul_smul a _ _

@[simp] theorem gradedMonomialLinear_coe (j : ℕ) (v : F.layer j) :
    (F.gradedMonomialLinear j v : VectorPolynomial Unit ℚ L) = monomial (unitMonomial j) (v : L) := rfl

noncomputable def associatedGradedPieceMap (j : ℕ) : F.layer j →ₗ[ℚ] F.AssociatedGraded :=
  (F.polynomialSymbolMap (fun _ : Unit => 1)).toLinearMap.comp (F.gradedMonomialLinear j)

@[simp] theorem associatedGradedPieceMap_apply (j : ℕ) (v : F.layer j) :
    F.associatedGradedPieceMap j v =
      F.polynomialSymbolMap (fun _ : Unit => 1) (F.gradedMonomialLinear j v) := rfl

theorem associatedGradedPieceMap_eq_zero_iff (j : ℕ) (v : F.layer j) :
    F.associatedGradedPieceMap j v = 0 ↔ (v : L) ∈ F.layer (j + 1) := by
  rw [F.associatedGradedPieceMap_apply, F.polynomialSymbolMap_eq_zero_iff]
  simp only [F.gradedMonomialLinear_coe, coefficients_monomial]
  constructor
  · intro h
    simpa only [Finsupp.single_eq_same, weight_unitMonomial] using h (unitMonomial j)
  · intro h α
    by_cases hα : unitMonomial j = α
    · subst α
      simpa only [Finsupp.single_eq_same, weight_unitMonomial] using h
    · rw [Finsupp.single_eq_of_ne (Ne.symm hα)]
      exact Submodule.zero_mem _

theorem associatedGradedPieceMap_lie (i j : ℕ) (u : F.layer i) (v : F.layer j) :
    ⁅F.associatedGradedPieceMap i u, F.associatedGradedPieceMap j v⁆ =
      F.associatedGradedPieceMap (i + j) ⟨⁅(u : L), (v : L)⁆, F.lie_mem u.property v.property⟩ := by
  simp only [F.associatedGradedPieceMap_apply]
  rw [← LieHom.map_lie]
  apply congrArg (F.polynomialSymbolMap (fun _ : Unit => 1))
  apply Subtype.ext
  change ⁅monomial (unitMonomial i) (u : L), monomial (unitMonomial j) (v : L)⁆ = _
  rw [lie_monomial, ← unitMonomial_add]
  rfl

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem associatedGradedPieceMap_coordinate (j : ℕ) (v : F.layer j) (i : ι) :
    (F.associatedGradedBasis b ω hlayers).repr (F.associatedGradedPieceMap j v) i =
      if j = ω i then b.repr (v : L) i else 0 := by
  classical
  rw [F.associatedGradedBasis_repr, F.associatedGradedPieceMap_apply,
    F.polynomialSymbolBasis_repr_map]
  simp only [F.gradedMonomialLinear_coe, coefficients_monomial]
  by_cases h : j = ω i
  · simp [h]
  · have h' : unitMonomial j ≠ unitMonomial (ω i) := fun he => h (unitMonomial_injective he)
    simp [h, h']

theorem associatedGradedPieceMap_basis (j : ℕ) (i : ι) (hi : j ≤ ω i) (he : j = ω i) :
    F.associatedGradedPieceMap j
      ⟨b i, by rw [hlayers]; exact Submodule.subset_span ⟨i, hi, rfl⟩⟩ =
        F.associatedGradedBasis b ω hlayers i := by
  classical
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  ext k
  rw [F.associatedGradedPieceMap_coordinate]
  simp only [Basis.repr_self, Finsupp.single_apply]
  by_cases h : i = k
  · subst k
    simp only [he, ite_true]
  · simp only [h, ite_false, ite_self]

theorem associatedGradedPieceMap_range (j : ℕ) :
    LinearMap.range (F.associatedGradedPieceMap j) =
      Submodule.span ℚ (F.associatedGradedBasis b ω hlayers '' {i | ω i = j}) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [basis_mem_span_image_iff]
    intro i hi
    rw [F.associatedGradedPieceMap_coordinate]
    exact ite_eq_right (Ne.symm hi)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨⟨b i, ?_⟩, ?_⟩
    · rw [hlayers]
      exact Submodule.subset_span ⟨i, hi.symm.le, rfl⟩
    · exact F.associatedGradedPieceMap_basis b ω hlayers j i hi.symm.le hi.symm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (U : LieSubalgebra ℚ F.AssociatedGraded)

noncomputable def gradedRefiltrationLayer (j : ℕ) : Submodule ℚ L :=
  (U.toSubmodule.comap (F.associatedGradedPieceMap j)).map (F.layer j).subtype

theorem mem_gradedRefiltrationLayer (j : ℕ) (v : L) :
    v ∈ F.gradedRefiltrationLayer U j ↔
      ∃ hv : v ∈ F.layer j, F.associatedGradedPieceMap j ⟨v, hv⟩ ∈ U := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩
  · rintro ⟨hv, hU⟩
    exact ⟨⟨v, hv⟩, hU, rfl⟩

theorem mem_gradedRefiltrationLayer_iff (j : ℕ) (v : F.layer j) :
    (v : L) ∈ F.gradedRefiltrationLayer U j ↔ F.associatedGradedPieceMap j v ∈ U := by
  rw [F.mem_gradedRefiltrationLayer]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨v.property, h⟩⟩

theorem gradedRefiltrationLayer_le (j : ℕ) : F.gradedRefiltrationLayer U j ≤ F.layer j := by
  intro v hv
  exact ((F.mem_gradedRefiltrationLayer U j v).mp hv).choose

theorem layer_succ_le_gradedRefiltrationLayer (j : ℕ) :
    F.layer (j + 1) ≤ F.gradedRefiltrationLayer U j := by
  intro v hv
  rw [F.mem_gradedRefiltrationLayer]
  refine ⟨F.antitone (Nat.le_succ j) hv, ?_⟩
  rw [(F.associatedGradedPieceMap_eq_zero_iff j _).mpr hv]
  exact U.zero_mem

theorem gradedRefiltrationLayer_antitone : Antitone (F.gradedRefiltrationLayer U) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hlt | rfl
  · exact (F.gradedRefiltrationLayer_le U j).trans
      ((F.antitone hlt).trans (F.layer_succ_le_gradedRefiltrationLayer U i))
  · exact le_rfl

theorem gradedRefiltrationLayer_lie_mem {i j : ℕ} {v z : L}
    (hv : v ∈ F.gradedRefiltrationLayer U i) (hz : z ∈ F.gradedRefiltrationLayer U j) :
    ⁅v, z⁆ ∈ F.gradedRefiltrationLayer U (i + j) := by
  obtain ⟨hv, hUv⟩ := (F.mem_gradedRefiltrationLayer U i v).mp hv
  obtain ⟨hz, hUz⟩ := (F.mem_gradedRefiltrationLayer U j z).mp hz
  rw [F.mem_gradedRefiltrationLayer]
  refine ⟨F.lie_mem hv hz, ?_⟩
  rw [← F.associatedGradedPieceMap_lie i j ⟨v, hv⟩ ⟨z, hz⟩]
  exact U.lie_mem hUv hUz

theorem gradedRefiltrationLayer_terminal : F.gradedRefiltrationLayer U (s + 1) = ⊥ :=
  bot_unique ((F.gradedRefiltrationLayer_le U (s + 1)).trans F.terminal.le)

noncomputable def gradedRefiltrationSubalgebra : LieSubalgebra ℚ L :=
  { F.gradedRefiltrationLayer U 1 with
    lie_mem' := fun hv hz => F.gradedRefiltrationLayer_antitone U (by decide : 1 ≤ 1 + 1)
      (F.gradedRefiltrationLayer_lie_mem U hv hz) }

noncomputable def gradedRefiltration :
    NilpotentLieFiltration (F.gradedRefiltrationSubalgebra U) s where
  layer j := (F.gradedRefiltrationLayer U j).comap (F.gradedRefiltrationSubalgebra U).incl.toLinearMap
  antitone := fun _ _ hij _ hv => F.gradedRefiltrationLayer_antitone U hij hv
  one_eq_top := by
    apply top_unique
    intro v _
    exact v.property
  lie_mem := fun hv hz => F.gradedRefiltrationLayer_lie_mem U hv hz
  terminal := by
    apply bot_unique
    intro v hv
    change v = 0
    apply Subtype.ext
    exact (Submodule.mem_bot ℚ).mp ((F.gradedRefiltrationLayer_terminal U) ▸ hv)

@[simp] theorem mem_gradedRefiltration_layer (j : ℕ) (v : F.gradedRefiltrationSubalgebra U) :
    v ∈ (F.gradedRefiltration U).layer j ↔ (v : L) ∈ F.gradedRefiltrationLayer U j := Iff.rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def squareDiagonalLayer (j : ℕ) : F.layer j →ₗ[ℚ] F.squareFiltration.layer j where
  toFun x := ⟨⟨(x, x), (F.mem_squareLieSubalgebra _).mpr (by simp)⟩,
    x.property, x.property, by simp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def squareRelativeLayer (j : ℕ) (hj : 1 ≤ j) :
    F.layer (j + 1) →ₗ[ℚ] F.squareFiltration.layer j where
  toFun x := ⟨⟨(x, 0), (F.mem_squareLieSubalgebra _).mpr (by
    simpa only [sub_zero] using F.antitone (Nat.add_le_add_right hj 1) x.property)⟩,
    F.antitone (Nat.le_succ j) x.property, (F.layer j).zero_mem, by
      change (x : L) - 0 ∈ F.layer (j + 1)
      simpa only [sub_zero] using x.property⟩
  map_add' _ _ := by apply Subtype.ext; apply Subtype.ext; simp
  map_smul' _ _ := by apply Subtype.ext; apply Subtype.ext; simp

noncomputable def squareGradedDiagonalPiece (j : ℕ) :
    F.layer j →ₗ[ℚ] F.squareFiltration.AssociatedGraded :=
  (F.squareFiltration.associatedGradedPieceMap j).comp (F.squareDiagonalLayer j)

noncomputable def squareGradedRelativePiece (j : ℕ) (hj : 1 ≤ j) :
    F.layer (j + 1) →ₗ[ℚ] F.squareFiltration.AssociatedGraded :=
  (F.squareFiltration.associatedGradedPieceMap j).comp (F.squareRelativeLayer j hj)

theorem squareGradedDiagonalPiece_eq_zero_iff (j : ℕ) (x : F.layer j) :
    F.squareGradedDiagonalPiece j x = 0 ↔ (x : L) ∈ F.layer (j + 1) := by
  change F.squareFiltration.associatedGradedPieceMap j (F.squareDiagonalLayer j x) = 0 ↔ _
  rw [F.squareFiltration.associatedGradedPieceMap_eq_zero_iff]
  change ((x : L) ∈ F.layer (j + 1) ∧ (x : L) ∈ F.layer (j + 1) ∧
    (x : L) - x ∈ F.layer (j + 1 + 1)) ↔ _
  simp only [sub_self, Submodule.zero_mem, and_true, and_self]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem squareGradedPiece_decomposition (j : ℕ) (hj : 1 ≤ j)
    (x : F.squareFiltration.layer j) :
    F.squareFiltration.associatedGradedPieceMap j x =
      F.squareGradedDiagonalPiece j ⟨x.val.val.2, x.property.2.1⟩ +
      F.squareGradedRelativePiece j hj ⟨x.val.val.1 - x.val.val.2, x.property.2.2⟩ := by
  change F.squareFiltration.associatedGradedPieceMap j x =
    F.squareFiltration.associatedGradedPieceMap j (F.squareDiagonalLayer j _) +
      F.squareFiltration.associatedGradedPieceMap j (F.squareRelativeLayer j hj _)
  rw [← map_add]
  apply congrArg (F.squareFiltration.associatedGradedPieceMap j)
  apply Subtype.ext
  apply Subtype.ext
  change x.val.val = (x.val.val.2, x.val.val.2) + (x.val.val.1 - x.val.val.2, 0)
  apply Prod.ext
  · change x.val.val.1 = x.val.val.2 + (x.val.val.1 - x.val.val.2)
    abel
  · exact (add_zero _).symm

end Erdos3.NilpotentLieFiltration

end

end OAI

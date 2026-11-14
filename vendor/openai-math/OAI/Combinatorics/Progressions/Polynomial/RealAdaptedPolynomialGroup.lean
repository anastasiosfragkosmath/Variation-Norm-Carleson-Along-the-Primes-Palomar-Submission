/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/RealAdaptedPolynomialGroup.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.PetalComparisonTree
public import OAI.Combinatorics.Progressions.Estimates.RealSymbolRepresentativeSplitting
@[expose] public section

namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

variable {σ R L M : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

noncomputable def mapLie (f : L →ₗ⁅R⁆ M) :
    VectorPolynomial σ R L →ₗ⁅R⁆ VectorPolynomial σ R M where
  toLinearMap := map f.toLinearMap
  map_lie' {p q} :=
    (LieAlgebra.ExtendScalars.map (AlgHom.id R (MvPolynomial σ R)) f).map_lie p q

end VectorPolynomial

namespace NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (f : L →ₗ⁅ℚ⁆ M) (hf : ∀ j, ∀ x ∈ F.layer j, f x ∈ G.layer j)
  (w : σ → ℕ)

noncomputable def filteredPolynomialMap :
    F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ G.adaptedLieSubalgebra w :=
  { ((VectorPolynomial.map f.toLinearMap).comp (F.adaptedLieSubalgebra w).incl.toLinearMap).codRestrict
      (G.adaptedLieSubalgebra w).toSubmodule (by
        intro p α
        change coefficients (VectorPolynomial.map f.toLinearMap p.val) α ∈ _
        rw [coefficients_map]
        exact hf _ _ (p.property α)) with
    map_lie' {p q} := by
      apply Subtype.ext
      exact (VectorPolynomial.mapLie f).map_lie p.val q.val }

@[simp] theorem filteredPolynomialMap_coe (p : F.adaptedLieSubalgebra w) :
    (F.filteredPolynomialMap G f hf w p : VectorPolynomial σ ℚ M) =
      VectorPolynomial.map f.toLinearMap p.val := rfl

theorem filteredPolynomialMap_mem_shiftedIdeal {p : F.adaptedLieSubalgebra w}
    (hp : p ∈ F.shiftedAdaptedIdeal w) :
    F.filteredPolynomialMap G f hf w p ∈ G.shiftedAdaptedIdeal w := by
  intro α
  change coefficients (VectorPolynomial.map f.toLinearMap p.val) α ∈ _
  rw [coefficients_map]
  exact hf _ _ (hp α)

noncomputable def filteredPolynomialSymbolMap : F.PolynomialSymbol w →ₗ⁅ℚ⁆ G.PolynomialSymbol w :=
  { toLinearMap := (F.shiftedAdaptedIdeal w).toSubmodule.liftQ
      ((G.polynomialSymbolMap w).toLinearMap.comp (F.filteredPolynomialMap G f hf w).toLinearMap) (by
        intro p hp
        exact (lieQuotientMap_eq_zero (G.shiftedAdaptedIdeal w) _).mpr
          (F.filteredPolynomialMap_mem_shiftedIdeal G f hf w hp))
    map_lie' {x y} := by
      obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
      obtain ⟨q, rfl⟩ := F.polynomialSymbolMap_surjective w y
      change G.polynomialSymbolMap w (F.filteredPolynomialMap G f hf w ⁅p, q⁆) =
        ⁅G.polynomialSymbolMap w (F.filteredPolynomialMap G f hf w p),
          G.polynomialSymbolMap w (F.filteredPolynomialMap G f hf w q)⁆
      rw [LieHom.map_lie, LieHom.map_lie] }

@[simp] theorem filteredPolynomialSymbolMap_symbol (p : F.adaptedLieSubalgebra w) :
    F.filteredPolynomialSymbolMap G f hf w (F.polynomialSymbolMap w p) =
      G.polynomialSymbolMap w (F.filteredPolynomialMap G f hf w p) := rfl

noncomputable def associatedGradedMap : F.AssociatedGraded →ₗ⁅ℚ⁆ G.AssociatedGraded :=
  F.filteredPolynomialSymbolMap G f hf (fun _ : Unit => 1)

@[simp] theorem associatedGradedMap_piece (j : ℕ) (x : F.layer j) :
    F.associatedGradedMap G f hf (F.associatedGradedPieceMap j x) =
      G.associatedGradedPieceMap j ⟨f x, hf j x x.property⟩ := by
  change G.polynomialSymbolMap (fun _ : Unit => 1)
    (F.filteredPolynomialMap G f hf (fun _ : Unit => 1) (F.gradedMonomialLinear j x)) = _
  apply congrArg (G.polynomialSymbolMap (fun _ : Unit => 1))
  apply Subtype.ext
  exact VectorPolynomial.map_monomial f.toLinearMap (unitMonomial j) x

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (f : L →ₗ⁅ℚ⁆ M) (hf : ∀ j, ∀ x ∈ F.layer j, f x ∈ G.layer j)
  (w : σ → ℕ)

@[simp] theorem filteredPolynomialMap_coefficient (p : F.adaptedLieSubalgebra w)
    (α : σ →₀ ℕ) :
    coefficients (F.filteredPolynomialMap G f hf w p).val α = f (coefficients p.val α) :=
  coefficients_map f.toLinearMap p.val α

theorem filteredPolynomialMap_surjective
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, f x = y) :
    Function.Surjective (F.filteredPolynomialMap G f hf w) := by
  classical
  intro q
  let v (α : σ →₀ ℕ) : L := if coefficients q.val α = 0 then 0 else
    Classical.choose (hsurj (Finsupp.weight w α) (coefficients q.val α) (q.property α))
  have hv (α : σ →₀ ℕ) : f (v α) = coefficients q.val α := by
    dsimp only [v]
    split_ifs with hz
    · rw [map_zero, hz]
    · exact (Classical.choose_spec (hsurj _ _ (q.property α))).2
  have hmem (α : σ →₀ ℕ) : v α ∈ F.layer (Finsupp.weight w α) := by
    dsimp only [v]
    split_ifs
    · exact Submodule.zero_mem _
    · exact (Classical.choose_spec (hsurj _ _ (q.property α))).1
  let c : (σ →₀ ℕ) →₀ L := Finsupp.onFinset (coefficients q.val).support v (by
    intro α hα
    apply Finsupp.mem_support_iff.mpr
    intro hz
    exact hα (by simp only [v, hz, ite_true]))
  let p : F.adaptedLieSubalgebra w := ⟨coefficients.symm c, by
    intro α
    simpa only [LinearEquiv.apply_symm_apply, c, Finsupp.onFinset_apply] using hmem α⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [F.filteredPolynomialMap_coefficient G f hf w]
  simpa only [p, LinearEquiv.apply_symm_apply, c, Finsupp.onFinset_apply] using hv α

theorem filteredPolynomialSymbolMap_surjective
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, f x = y) :
    Function.Surjective (F.filteredPolynomialSymbolMap G f hf w) := by
  intro y
  obtain ⟨q, rfl⟩ := G.polynomialSymbolMap_surjective w y
  obtain ⟨p, rfl⟩ := F.filteredPolynomialMap_surjective G f hf w hsurj q
  exact ⟨F.polynomialSymbolMap w p, rfl⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
  (w : σ → ℕ)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (I : LieIdeal ℚ L)
    (hI : F.layer (t + 1) ≤ I.toSubmodule) {w : σ → ℕ}

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def realAdaptedPolynomialMap :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
  VectorPolynomial.realificationLieEquiv.toLieHom.comp
    (LieAlgebra.ExtendScalars.map (AlgHom.id ℚ ℝ) (F.adaptedLieSubalgebra w).incl)

@[simp] theorem realAdaptedPolynomialMap_coefficient_tmul
    (a : ℝ) (p : F.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (F.realAdaptedPolynomialMap w (a ⊗ₜ[ℚ] p)) α =
      a ⊗ₜ[ℚ] coefficients (p : VectorPolynomial σ ℚ L) α := by
  change coefficients (VectorPolynomial.realificationLieEquiv
    (a ⊗ₜ[ℚ] (p : VectorPolynomial σ ℚ L))) α = _
  have hc := coefficients_realificationLieEquiv_tmul a (p : VectorPolynomial σ ℚ L) α
  convert hc using 2

theorem realAdaptedPolynomialMap_adapted (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realification.Adapted w (F.realAdaptedPolynomialMap w x) := by
  rw [F.realification.adapted_iff_coefficients]
  intro α
  induction x using TensorProduct.inductionOn with
  | tmul a p =>
    rw [F.realAdaptedPolynomialMap_coefficient_tmul]
    exact LieSubmodule.tmul_mem_baseChange_of_mem a (p.property α)
  | add x y hx hy =>
    rw [map_add, map_add, Finsupp.add_apply]
    exact Submodule.add_mem _ hx hy

noncomputable def realAdaptedPolynomialTensor :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) →ₗ⁅ℚ⁆ F.realification.adaptedLieSubalgebra w where
  toLinearMap := (F.realAdaptedPolynomialMap w).toLinearMap.codRestrict
    (F.realification.adaptedSubmodule w) (fun x =>
      (F.realification.mem_adaptedSubmodule w _).mpr (F.realAdaptedPolynomialMap_adapted w x))
  map_lie' {x y} := by
    apply Subtype.ext
    exact (F.realAdaptedPolynomialMap w).map_lie x y

@[simp] theorem realAdaptedPolynomialTensor_coe (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    (F.realAdaptedPolynomialTensor w x : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) =
      F.realAdaptedPolynomialMap w x := rfl

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realAdaptedPolynomialTensor_coordinates
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
    (z : {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2}) :
    (b.baseChange ℝ).repr (coefficients (F.realAdaptedPolynomialMap w x) z.val.1) z.val.2 =
      ((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr x z := by
  induction x using TensorProduct.inductionOn with
  | tmul a p =>
    rw [F.realAdaptedPolynomialMap_coefficient_tmul, Basis.baseChange_repr_tmul,
      Basis.baseChange_repr_tmul, F.adaptedMonomialBasis_repr]
  | add x y hx hy =>
    simp only [map_add, Finsupp.add_apply, hx, hy]

include b ω hlayers in
theorem realAdaptedPolynomialTensor_surjective :
    Function.Surjective (F.realAdaptedPolynomialTensor w) := by
  intro p
  let c := supportedCoordinates (b.baseChange ℝ)
    {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 ≤ ω z.2}
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
  let x := ((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr.symm c
  refine ⟨x, ?_⟩
  apply Subtype.ext
  apply coefficients.injective
  ext α
  apply (b.baseChange ℝ).repr.injective
  ext i
  by_cases h : Finsupp.weight w α ≤ ω i
  · have hc := F.realAdaptedPolynomialTensor_coordinates w b ω hlayers x ⟨(α, i), h⟩
    change (b.baseChange ℝ).repr (coefficients (F.realAdaptedPolynomialMap w x) α) i = _
    rw [hc]
    change (((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr
      (((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr.symm c)) ⟨(α, i), h⟩ = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  · have hleft := (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mp
      ((F.realification.adapted_iff_coefficients w _).mp
        (F.realAdaptedPolynomialMap_adapted w x) α) i h
    have hright := (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mp (p.property α) i h
    exact hleft.trans hright.symm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realAdaptedMonomialBasis_bracket_support (u v z : AdaptedBasisIndex w ω)
    (h : ((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr
      ⁅(F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ u,
        (F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ v⁆ z ≠ 0) :
    u.val.1 + v.val.1 = z.val.1 := by
  classical
  by_contra hn
  apply h
  rw [realLieBasis_structure]
  change (((F.adaptedMonomialBasis b ω hlayers w).repr
    ⁅F.adaptedMonomialBasis b ω hlayers w u,
      F.adaptedMonomialBasis b ω hlayers w v⁆ z : ℚ) : ℝ) = 0
  simp only [F.adaptedMonomialBasis_bracket, hn, ite_false, Rat.cast_zero]

noncomputable def scaledRealAdaptedMonomialBasis (T : σ → ℝ) (hT : ∀ i, 0 < T i) :
    Basis (AdaptedBasisIndex w ω) ℝ (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :=
  inverseScaledBasis ((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ)
    (fun z => monomialScale T z.val.1) (fun z => monomialScale_pos T hT z.val.1)

theorem scaledRealAdaptedMonomialBasis_repr (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) (z : AdaptedBasisIndex w ω) :
    (F.scaledRealAdaptedMonomialBasis b ω hlayers w T hT).repr x z =
      monomialScale T z.val.1 *
        ((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr x z :=
  inverseScaledBasis_repr _ _ _ _ _

theorem scaledRealAdaptedMonomialBasis_structure (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (u v z : AdaptedBasisIndex w ω) :
    (F.scaledRealAdaptedMonomialBasis b ω hlayers w T hT).repr
      ⁅F.scaledRealAdaptedMonomialBasis b ω hlayers w T hT u,
        F.scaledRealAdaptedMonomialBasis b ω hlayers w T hT v⁆ z =
      (lieStructureConstants (F.adaptedMonomialBasis b ω hlayers w) u v z : ℝ) := by
  apply Eq.trans (inverseScaledBasis_bracket _ _ _ ?_ u v z)
  · exact realLieBasis_structure _ u v z
  · intro i j k h
    have he := F.realAdaptedMonomialBasis_bracket_support b ω hlayers w i j k h
    rw [← he, monomialScale_add]

theorem scaledRealAdaptedMonomialBasis_bound_iff (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) (z : AdaptedBasisIndex w ω) (M : ℝ) :
    |(F.scaledRealAdaptedMonomialBasis b ω hlayers w T hT).repr x z| ≤ M ↔
      |((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr x z| ≤
        M / monomialScale T z.val.1 := by
  rw [F.scaledRealAdaptedMonomialBasis_repr, abs_mul,
    abs_of_pos (monomialScale_pos T hT z.val.1), le_div_iff₀ (monomialScale_pos T hT z.val.1)]
  rw [mul_comm]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

theorem realFilteredPolynomialMap_polynomial
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    G.realAdaptedPolynomialMap w ((F.filteredPolynomialMap G φ hφ w).toLinearMap.baseChange ℝ x) =
      VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ)
        (F.realAdaptedPolynomialMap w x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r p =>
    apply coefficients.injective
    ext α
    rw [LinearMap.baseChange_tmul, G.realAdaptedPolynomialMap_coefficient_tmul,
      coefficients_map, F.realAdaptedPolynomialMap_coefficient_tmul]
    change r ⊗ₜ[ℚ] coefficients (F.filteredPolynomialMap G φ hφ w p).val α =
      r ⊗ₜ[ℚ] φ (coefficients p.val α)
    rw [F.filteredPolynomialMap_coefficient]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

abbrev RealAdaptedPolynomialGroup := (F.adaptedPolynomialFiltration w).realification.Group

noncomputable def realAdaptedPolynomialGroupHom :
    F.RealAdaptedPolynomialGroup w →* (F.realification.adaptedPolynomialFiltration w).Group :=
  NilpotentLieBCHGroup.map (F.realAdaptedPolynomialTensor w)

@[simp] theorem realAdaptedPolynomialGroupHom_log (g : F.RealAdaptedPolynomialGroup w) :
    ((F.realAdaptedPolynomialGroupHom w g).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) =
      F.realAdaptedPolynomialMap w g.coord := rfl

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include b ω hlayers in
theorem realAdaptedPolynomialGroupHom_surjective : Function.Surjective (F.realAdaptedPolynomialGroupHom w) := by
  intro g
  obtain ⟨x, hx⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hlayers g.coord
  exact ⟨⟨x⟩, NilpotentLieBCHGroup.ext hx⟩

noncomputable def realAdaptedPolynomialGroupLift (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.RealAdaptedPolynomialGroup w :=
  (F.realAdaptedPolynomialGroupHom_surjective w b ω hlayers g).choose

@[simp] theorem realAdaptedPolynomialGroupHom_lift
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.realAdaptedPolynomialGroupHom w (F.realAdaptedPolynomialGroupLift w b ω hlayers g) = g :=
  (F.realAdaptedPolynomialGroupHom_surjective w b ω hlayers g).choose_spec

theorem realAdaptedPolynomialGroupHom_coordinate (g : F.RealAdaptedPolynomialGroup w)
    (z : AdaptedBasisIndex w ω) :
    (b.baseChange ℝ).repr (coefficients
      ((F.realAdaptedPolynomialGroupHom w g).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.val.1) z.val.2 =
      ((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr g.coord z :=
  F.realAdaptedPolynomialTensor_coordinates w b ω hlayers g.coord z

end Erdos3.NilpotentLieFiltration

end

end OAI

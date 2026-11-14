/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/FastCoefficientImage.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.SortedPositiveWeights
public import OAI.Combinatorics.Progressions.Linear.CommonKernelRangeEquiv
public import OAI.Combinatorics.Progressions.Linear.SquareBasisGeometry
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

abbrev FirstCoefficientModule (F : NilpotentLieFiltration L s) (w : σ → ℕ) :=
  (F.shiftedPolynomialIdeal w 1) ⧸
    (F.shiftedPolynomialIdeal w 2).toSubmodule.comap (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype

noncomputable def firstCoefficientMap (F : NilpotentLieFiltration L s) (w : σ → ℕ) :
    (F.shiftedPolynomialIdeal w 1) →ₗ[ℚ] F.FirstCoefficientModule w :=
  ((F.shiftedPolynomialIdeal w 2).toSubmodule.comap
    (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype).mkQ

theorem firstCoefficientMap_eq_zero_iff (F : NilpotentLieFiltration L s) (w : σ → ℕ)
    (p : F.shiftedPolynomialIdeal w 1) :
    F.firstCoefficientMap w p = 0 ↔
      ∀ α, coefficients (p.val : VectorPolynomial σ ℚ L) α ∈ F.layer (Finsupp.weight w α + 2) :=
  Submodule.Quotient.mk_eq_zero _

abbrev FirstCoefficientIndex (w : σ → ℕ) (ω : ι → ℕ) :=
  {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 + 1 = ω z.2}

def firstCoefficientSurvivorEquiv (w : σ → ℕ) (ω : ι → ℕ) :
    {z : ShiftedMonomialIndex w ω 1 //
      ¬ Finsupp.weight w z.val.val.1 + 2 ≤ ω z.val.val.2} ≃ FirstCoefficientIndex w ω where
  toFun z := ⟨z.val.val.val, by
    have h : Finsupp.weight w z.val.val.val.1 + 1 ≤ ω z.val.val.val.2 := z.val.property
    have hn : ¬ Finsupp.weight w z.val.val.val.1 + 2 ≤ ω z.val.val.val.2 := z.property
    omega⟩
  invFun z := ⟨⟨⟨z.val, by have h := z.property; omega⟩, z.property.le⟩, by
    change ¬ Finsupp.weight w z.val.1 + 2 ≤ ω z.val.2
    have h := z.property
    omega⟩
  left_inv z := by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def firstCoefficientBasis (w : σ → ℕ) :
    Basis (FirstCoefficientIndex w ω) ℚ (F.FirstCoefficientModule w) :=
  (supportedQuotientBasis (F.shiftedMonomialBasis b ω hF w 1)
    ((F.shiftedPolynomialIdeal w 2).toSubmodule.comap
      (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype)
    {z | Finsupp.weight w z.val.val.1 + 2 ≤ ω z.val.val.2}
    (F.shiftedPolynomial_next_eq_span b ω hF w 1)).reindex (firstCoefficientSurvivorEquiv w ω)

theorem firstCoefficientBasis_repr_map (w : σ → ℕ) (p : F.shiftedPolynomialIdeal w 1)
    (z : FirstCoefficientIndex w ω) :
    (F.firstCoefficientBasis b ω hF w).repr (F.firstCoefficientMap w p) z =
      b.repr (coefficients (p.val : VectorPolynomial σ ℚ L) z.val.1) z.val.2 := by
  rw [firstCoefficientBasis, Basis.repr_reindex_apply]
  change (supportedQuotientBasis _ _ _ _).repr
    (((F.shiftedPolynomialIdeal w 2).toSubmodule.comap
      (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype).mkQ p) _ = _
  rw [supportedQuotientBasis_repr_mk, F.shiftedMonomialBasis_repr]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem firstCoefficientMap_surjective : Function.Surjective (F.firstCoefficientMap w) :=
  Submodule.mkQ_surjective _

noncomputable def firstCoefficientHorizontal : F.FirstCoefficientModule w →ₗ[ℚ] L ⧸ F.layer 2 :=
  ((F.shiftedPolynomialIdeal w 2).toSubmodule.comap
    (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype).liftQ
    (((F.layer 2).mkQ.comp (F.adaptedCoefficientMap w 0)).comp
      (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype) (by
        intro p hp
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        change coefficients p.val.val 0 ∈ F.layer 2
        have h := hp 0
        change coefficients p.val.val 0 ∈ F.layer (Finsupp.weight w 0 + 2) at h
        simpa only [map_zero, Nat.zero_add] using h)

@[simp] theorem firstCoefficientHorizontal_map (p : F.shiftedPolynomialIdeal w 1) :
    F.firstCoefficientHorizontal w (F.firstCoefficientMap w p) =
      (F.layer 2).mkQ (coefficients p.val.val 0) := rfl

noncomputable def firstCoefficientConstant : L →ₗ[ℚ] F.FirstCoefficientModule w :=
  (F.firstCoefficientMap w).comp
    ((F.adaptedConstantLieHom w).toLinearMap.codRestrict
      (F.shiftedPolynomialIdeal w 1).toSubmodule (F.adaptedConstant_mem_shiftedIdeal w))

@[simp] theorem firstCoefficientHorizontal_constant (x : L) :
    F.firstCoefficientHorizontal w (F.firstCoefficientConstant w x) = (F.layer 2).mkQ x := by
  change (F.layer 2).mkQ (coefficients (monomial 0 x) 0) = _
  simp only [coefficients_monomial, Finsupp.single_eq_same]

noncomputable def firstCoefficientHorizontalSection : (L ⧸ F.layer 2) →ₗ[ℚ] F.FirstCoefficientModule w :=
  (F.layer 2).liftQ (F.firstCoefficientConstant w) (by
    intro x hx
    change F.firstCoefficientMap w ⟨F.adaptedConstant w x, F.adaptedConstant_mem_shiftedIdeal w x⟩ = 0
    apply (F.firstCoefficientMap_eq_zero_iff w _).mpr
    exact F.adaptedConstant_mem_shiftedPolynomialIdeal w 2 hx)

@[simp] theorem firstCoefficientHorizontalSection_mk (x : L) :
    F.firstCoefficientHorizontalSection w ((F.layer 2).mkQ x) = F.firstCoefficientConstant w x := rfl

theorem firstCoefficientHorizontal_section (x : L ⧸ F.layer 2) :
    F.firstCoefficientHorizontal w (F.firstCoefficientHorizontalSection w x) = x := by
  obtain ⟨v, rfl⟩ := (F.layer 2).mkQ_surjective x
  rw [F.firstCoefficientHorizontalSection_mk, F.firstCoefficientHorizontal_constant]

noncomputable def normalizedFirstCoefficientMap :
    F.normalizedRelativeSubmodule w →ₗ[ℚ] F.FirstCoefficientModule w :=
  (F.firstCoefficientMap w).comp
    ((F.normalizedRelativeSubmodule w).subtype.codRestrict
      (F.shiftedPolynomialIdeal w 1).toSubmodule (fun p => p.property.1))

theorem normalizedFirstCoefficientMap_eq_zero_iff (p : F.normalizedRelativeSubmodule w) :
    F.normalizedFirstCoefficientMap w p = 0 ↔ p.val ∈ F.shiftedPolynomialIdeal w 2 :=
  F.firstCoefficientMap_eq_zero_iff w _

theorem normalizedFirstCoefficientMap_range :
    LinearMap.range (F.normalizedFirstCoefficientMap w) = LinearMap.ker (F.firstCoefficientHorizontal w) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).mpr p.property.2
  · intro hx
    obtain ⟨p, rfl⟩ := F.firstCoefficientMap_surjective w x
    have hp : coefficients p.val.val 0 ∈ F.layer 2 := (Submodule.Quotient.mk_eq_zero _).mp hx
    exact ⟨⟨p.val, p.property, hp⟩, rfl⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

theorem firstCoefficientIndex_grade_pos {σ ι : Type*} (ω : ι → ℕ)
    (z : FirstCoefficientIndex (fun _ : σ => 1) ω) : 1 ≤ ω z.val.2 := by
  have h := z.property
  omega

theorem firstCoefficientIndex_zero_iff_grade_one {σ ι : Type*} (ω : ι → ℕ)
    (z : FirstCoefficientIndex (fun _ : σ => 1) ω) :
    z.val.1 = 0 ↔ ω z.val.2 = 1 := by
  constructor
  · intro hz
    have h := z.property
    simpa only [hz, map_zero, zero_add] using h.symm
  · intro hz
    apply Finsupp.ext
    intro i
    change z.val.1 i = 0
    by_contra hi
    have hw := Finsupp.le_weight_of_ne_zero' (fun _ : σ => (1 : ℕ)) hi
    have h := z.property
    omega

theorem exists_sorted_firstCoefficient_rows {σ ι : Type*} {d : ℕ}
    (ω : ι → ℕ) (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω) :
    ∃ (e : Equiv.Perm (Fin d)) (a : ℕ), a ≤ d ∧
      Monotone (fun i => ω (rows (e i)).val.2) ∧
      ∀ i, i.val < a ↔ (rows (e i)).val.1 = 0 := by
  obtain ⟨e, a, ha, hm, hi⟩ := exists_sorted_positive_weights
    (fun i => ω (rows i).val.2) (fun i => firstCoefficientIndex_grade_pos ω (rows i))
  refine ⟨e, a, ha, hm, ?_⟩
  intro i
  exact (hi i).trans (firstCoefficientIndex_zero_iff_grade_one ω (rows (e i))).symm

theorem sorted_firstCoefficient_scale_bounds {σ ι : Type*} {d a : ℕ}
    (ω : ι → ℕ) (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (hzero : ∀ i, i.val < a ↔ (rows i).val.1 = 0)
    (T : σ → ℝ) (Tmin : ℝ) (hmin : 1 ≤ Tmin) (hT : ∀ i, Tmin ≤ T i) :
    (∀ i, i.val < a → monomialScale T (rows i).val.1 = 1) ∧
      (∀ i, a ≤ i.val → Tmin ≤ monomialScale T (rows i).val.1) := by
  constructor
  · intro i hi
    rw [(hzero i).mp hi, monomialScale_zero]
  · intro i hi
    apply le_monomialScale_of_ne_zero T hmin hT
    intro hz
    exact (not_lt_of_ge hi) ((hzero i).mpr hz)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem reducedSquareSndSymbolKernel_lift {x : F.squareFiltration.quotientTop.PolynomialSymbol w}
    (hx : F.reducedSquareSndSymbolMap w x = 0) :
    ∃ y : F.squareFiltration.PolynomialSymbol w,
      F.squareSndSymbolMap w y = 0 ∧ F.reducedSquareSymbolMap w y = x := by
  obtain ⟨y, rfl⟩ := F.reducedSquareSymbolMap_surjective w x
  refine ⟨y - F.squareDiagonalSymbolMap w (F.squareSndSymbolMap w y), ?_, ?_⟩
  · rw [map_sub, F.squareSndSymbolMap_diagonal, sub_self]
  · rw [map_sub, ← F.reducedSquareDiagonalSymbolMap_quotient,
      ← F.reducedSquareSndSymbolMap_quotient, hx, map_zero, sub_zero]

theorem reducedSquareSndSymbolKernel_lie_eq_zero (hw : ∀ i, 0 < w i)
    {x y : F.squareFiltration.quotientTop.PolynomialSymbol w}
    (hx : F.reducedSquareSndSymbolMap w x = 0) (hy : F.reducedSquareSndSymbolMap w y = 0) :
    ⁅x, y⁆ = 0 := by
  obtain ⟨a, ha, rfl⟩ := F.reducedSquareSndSymbolKernel_lift w hx
  obtain ⟨b, hb, rfl⟩ := F.reducedSquareSndSymbolKernel_lift w hy
  rw [← LieHom.map_lie, F.squareSndSymbolKernel_lie_eq_zero w hw ha hb, map_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

variable (hw : ∀ i, 0 < w i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

noncomputable def reducedRelativeSquareSymbolMap :
    F.normalizedRelativeSubmodule w →ₗ[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w :=
  (F.reducedSquareSymbolMap w).toLinearMap.comp (F.relativeSquareSymbolMap w hw)

@[simp] theorem reducedRelativeSquareSymbolMap_apply (p : F.normalizedRelativeSubmodule w) :
    F.reducedRelativeSquareSymbolMap w hw p =
      F.reducedSquareSymbolMap w (F.relativeSquareSymbolMap w hw p) := rfl

@[simp] theorem reducedRelativeSquareSymbolMap_projection (p : F.normalizedRelativeSubmodule w) :
    F.reducedSquareSndSymbolMap w (F.reducedRelativeSquareSymbolMap w hw p) = 0 := by
  rw [F.reducedRelativeSquareSymbolMap_apply, F.reducedSquareSndSymbolMap_quotient,
    F.squareSndSymbolMap_relative, map_zero]

theorem reducedRelativeSquareSymbolMap_range :
    LinearMap.range (F.reducedRelativeSquareSymbolMap w hw) =
      (F.reducedSquareSndSymbolMap w).ker.toSubmodule := by
  apply le_antisymm
  · rintro x ⟨p, rfl⟩
    exact F.reducedRelativeSquareSymbolMap_projection w hw p
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := F.reducedSquareSndSymbolKernel_lift w hx
    have hr : y ∈ LinearMap.range (F.relativeSquareSymbolMap w hw) := by
      rw [F.relativeSquareSymbolMap_range w hw]
      exact hy
    obtain ⟨p, rfl⟩ := hr
    exact ⟨p, rfl⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

noncomputable def reducedSquareDifference :
    (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] L :=
  (F.squareFiltration.layerIdeal (s + 1)).toSubmodule.liftQ
    (F.squareFst.toLinearMap - F.squareSnd.toLinearMap) (by
      intro x hx
      change x.val.1 - x.val.2 = 0
      exact sub_eq_zero.mpr ((F.mem_squareFiltration_top x).mp hx).2)

@[simp] theorem reducedSquareDifference_mk (x : F.squareLieSubalgebra) :
    F.reducedSquareDifference (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)) x) =
      x.val.1 - x.val.2 := rfl

theorem reducedSquareDifference_mem_layer (j : ℕ)
    (x : F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1))
    (hx : x ∈ F.squareFiltration.quotientTop.layer j) :
    F.reducedSquareDifference x ∈ F.layer (j + 1) := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact hy.2.2

theorem reducedRelativeSquareSymbolMap_eq_zero_iff (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : F.normalizedRelativeSubmodule w) :
    F.reducedRelativeSquareSymbolMap w hw p = 0 ↔ p.val ∈ F.shiftedPolynomialIdeal w 2 := by
  constructor
  · intro hp α
    change coefficients p.val.val α ∈ F.layer (Finsupp.weight w α + 2)
    change F.squareFiltration.quotientTop.polynomialSymbolMap w
      (F.reducedSquarePolynomialMap w (F.relativeSquareLift w hw p)) = 0 at hp
    have hα := (F.squareFiltration.quotientTop.polynomialSymbolMap_eq_zero_iff w _).mp hp α
    have hd := F.reducedSquareDifference_mem_layer (Finsupp.weight w α + 1) _ hα
    change F.reducedSquareDifference
      (coefficients (map (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))).toLinearMap
        (F.relativeSquarePolynomial w hw p)) α) ∈ _ at hd
    rw [coefficients_map] at hd
    change F.reducedSquareDifference
      (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))
        (coefficients (F.relativeSquarePolynomial w hw p) α)) ∈ _ at hd
    rw [F.reducedSquareDifference_mk, F.relativeSquarePolynomial_coefficient] at hd
    simpa only [sub_zero, Nat.add_assoc] using hd
  · intro hp
    rw [F.reducedRelativeSquareSymbolMap_apply,
      (F.relativeSquareSymbolMap_eq_zero_iff w hw p).mpr hp, map_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (h : σ → ℚ) (e m : L)
  (p : F.adaptedLieSubalgebra (fun _ : σ => 1))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem normalizedFirstCoefficientMap_ker :
    LinearMap.ker (F.normalizedFirstCoefficientMap w) =
      LinearMap.ker (F.reducedRelativeSquareSymbolMap w hw) := by
  ext p
  change F.normalizedFirstCoefficientMap w p = 0 ↔ F.reducedRelativeSquareSymbolMap w hw p = 0
  rw [F.normalizedFirstCoefficientMap_eq_zero_iff, F.reducedRelativeSquareSymbolMap_eq_zero_iff]

noncomputable def firstCoefficientRelativeRangeEquiv :
    LinearMap.range (F.normalizedFirstCoefficientMap w) ≃ₗ[ℚ]
      LinearMap.range (F.reducedRelativeSquareSymbolMap w hw) :=
  commonKernelRangeEquiv (F.normalizedFirstCoefficientMap w) (F.reducedRelativeSquareSymbolMap w hw)
    (F.normalizedFirstCoefficientMap_ker w hw)

theorem firstCoefficientRelativeRangeEquiv_apply (p : F.normalizedRelativeSubmodule w) :
    (F.firstCoefficientRelativeRangeEquiv w hw ⟨F.normalizedFirstCoefficientMap w p, ⟨p, rfl⟩⟩ :
      F.squareFiltration.quotientTop.PolynomialSymbol w) = F.reducedRelativeSquareSymbolMap w hw p :=
  commonKernelRangeEquiv_apply _ _ _ p

noncomputable def firstCoefficientRelativeEquiv :
    LinearMap.ker (F.firstCoefficientHorizontal w) ≃ₗ[ℚ]
      (F.reducedSquareSndSymbolMap w).ker :=
  (LinearEquiv.ofEq _ _ (F.normalizedFirstCoefficientMap_range w).symm).trans
    ((F.firstCoefficientRelativeRangeEquiv w hw).trans
      (LinearEquiv.ofEq _ _ (F.reducedRelativeSquareSymbolMap_range w hw)))

theorem firstCoefficientRelativeEquiv_apply (p : F.normalizedRelativeSubmodule w)
    (hp : F.normalizedFirstCoefficientMap w p ∈ LinearMap.ker (F.firstCoefficientHorizontal w)) :
    (F.firstCoefficientRelativeEquiv w hw ⟨F.normalizedFirstCoefficientMap w p, hp⟩ :
      F.squareFiltration.quotientTop.PolynomialSymbol w) = F.reducedRelativeSquareSymbolMap w hw p :=
  F.firstCoefficientRelativeRangeEquiv_apply w hw p

noncomputable def firstCoefficientRelativeMap :
    LinearMap.ker (F.firstCoefficientHorizontal w) →ₗ[ℚ]
      F.squareFiltration.quotientTop.PolynomialSymbol w :=
  (F.reducedSquareSndSymbolMap w).ker.toSubmodule.subtype.comp
    (F.firstCoefficientRelativeEquiv w hw).toLinearMap

noncomputable def firstCoefficientFastSubmodule
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w)) :
    Submodule ℚ (F.FirstCoefficientModule w) :=
  (U.comap (F.firstCoefficientRelativeMap w hw)).map (LinearMap.ker (F.firstCoefficientHorizontal w)).subtype

theorem firstCoefficientFastSubmodule_le_horizontal_ker
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w)) :
    F.firstCoefficientFastSubmodule w hw U ≤ LinearMap.ker (F.firstCoefficientHorizontal w) := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem normalizedFirstCoefficientMap_mem_fast_iff
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (p : F.normalizedRelativeSubmodule w) :
    F.normalizedFirstCoefficientMap w p ∈ F.firstCoefficientFastSubmodule w hw U ↔
      F.reducedRelativeSquareSymbolMap w hw p ∈ U := by
  have hp : F.normalizedFirstCoefficientMap w p ∈ LinearMap.ker (F.firstCoefficientHorizontal w) := by
    rw [← F.normalizedFirstCoefficientMap_range w]
    exact ⟨p, rfl⟩
  constructor
  · rintro ⟨y, hy, he⟩
    have hy' : y = ⟨F.normalizedFirstCoefficientMap w p, hp⟩ := Subtype.ext he
    rw [hy'] at hy
    change (F.firstCoefficientRelativeEquiv w hw ⟨F.normalizedFirstCoefficientMap w p, hp⟩ :
      F.squareFiltration.quotientTop.PolynomialSymbol w) ∈ U at hy
    rwa [F.firstCoefficientRelativeEquiv_apply] at hy
  · intro h
    refine ⟨⟨F.normalizedFirstCoefficientMap w p, hp⟩, ?_, rfl⟩
    change (F.firstCoefficientRelativeEquiv w hw ⟨F.normalizedFirstCoefficientMap w p, hp⟩ :
      F.squareFiltration.quotientTop.PolynomialSymbol w) ∈ U
    rwa [F.firstCoefficientRelativeEquiv_apply]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

variable [Fintype σ]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem reducedSquareDifference_mem_two
    (x : F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) :
    F.reducedSquareDifference x ∈ F.layer 2 := by
  obtain ⟨y, rfl⟩ := lieQuotientMap_surjective (F.squareFiltration.layerIdeal (s + 1)) x
  rw [F.reducedSquareDifference_mk]
  exact (F.mem_squareLieSubalgebra y.val).mp y.property

noncomputable def reducedSquareDifferenceAdapted :
    F.squareFiltration.quotientTop.adaptedLieSubalgebra w →ₗ[ℚ] F.adaptedLieSubalgebra w :=
  ((VectorPolynomial.map F.reducedSquareDifference).comp
    (F.squareFiltration.quotientTop.adaptedLieSubalgebra w).incl.toLinearMap).codRestrict
      (F.adaptedLieSubalgebra w).toSubmodule (by
        intro p α
        change coefficients (VectorPolynomial.map F.reducedSquareDifference p.val) α ∈ _
        rw [coefficients_map]
        exact F.antitone (Nat.le_succ _) (F.reducedSquareDifference_mem_layer _ _ (p.property α)))

noncomputable def reducedSquareDifferenceRelative :
    F.squareFiltration.quotientTop.adaptedLieSubalgebra w →ₗ[ℚ] F.normalizedRelativeSubmodule w :=
  (F.reducedSquareDifferenceAdapted w).codRestrict (F.normalizedRelativeSubmodule w) (by
    intro p
    constructor
    · intro α
      change coefficients (VectorPolynomial.map F.reducedSquareDifference p.val) α ∈ _
      rw [coefficients_map]
      exact F.reducedSquareDifference_mem_layer _ _ (p.property α)
    · change coefficients (VectorPolynomial.map F.reducedSquareDifference p.val) 0 ∈ F.layer 2
      rw [coefficients_map]
      exact F.reducedSquareDifference_mem_two _)

theorem reducedSquareDifferenceRelative_coefficient
    (p : F.squareFiltration.quotientTop.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (F.reducedSquareDifferenceRelative w p).val.val α =
      F.reducedSquareDifference (coefficients p.val α) :=
  coefficients_map F.reducedSquareDifference p.val α

noncomputable def reducedSquareCoefficientMap :
    F.squareFiltration.quotientTop.PolynomialSymbol w →ₗ[ℚ] F.FirstCoefficientModule w :=
  (F.squareFiltration.quotientTop.shiftedAdaptedIdeal w).toSubmodule.liftQ
    ((F.normalizedFirstCoefficientMap w).comp (F.reducedSquareDifferenceRelative w)) (by
      intro p hp
      apply (F.normalizedFirstCoefficientMap_eq_zero_iff w _).mpr
      intro α
      change coefficients (F.reducedSquareDifferenceRelative w p).val.val α ∈ _
      rw [F.reducedSquareDifferenceRelative_coefficient]
      exact F.reducedSquareDifference_mem_layer _ _ (hp α))

@[simp] theorem reducedSquareCoefficientMap_symbol
    (p : F.squareFiltration.quotientTop.adaptedLieSubalgebra w) :
    F.reducedSquareCoefficientMap w (F.squareFiltration.quotientTop.polynomialSymbolMap w p) =
      F.normalizedFirstCoefficientMap w (F.reducedSquareDifferenceRelative w p) := rfl

theorem reducedSquareDifferenceRelative_relative (hw : ∀ i, 0 < w i)
    (p : F.normalizedRelativeSubmodule w) :
    F.reducedSquareDifferenceRelative w
      (F.reducedSquarePolynomialMap w (F.relativeSquareLift w hw p)) = p := by
  apply Subtype.ext
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [F.reducedSquareDifferenceRelative_coefficient]
  change F.reducedSquareDifference
    (coefficients (VectorPolynomial.map
      (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))).toLinearMap
      (F.relativeSquarePolynomial w hw p)) α) = _
  rw [coefficients_map]
  change F.reducedSquareDifference
    (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))
      (coefficients (F.relativeSquarePolynomial w hw p) α)) = _
  rw [F.reducedSquareDifference_mk, F.relativeSquarePolynomial_coefficient, sub_zero]

@[simp] theorem reducedSquareCoefficientMap_relative (hw : ∀ i, 0 < w i)
    (p : F.normalizedRelativeSubmodule w) :
    F.reducedSquareCoefficientMap w (F.reducedRelativeSquareSymbolMap w hw p) =
      F.normalizedFirstCoefficientMap w p := by
  change F.reducedSquareCoefficientMap w (F.squareFiltration.quotientTop.polynomialSymbolMap w
    (F.reducedSquarePolynomialMap w (F.relativeSquareLift w hw p))) = _
  rw [F.reducedSquareCoefficientMap_symbol, F.reducedSquareDifferenceRelative_relative]

theorem reducedSquareCoefficientMap_horizontal
    (x : F.squareFiltration.quotientTop.PolynomialSymbol w) :
    F.firstCoefficientHorizontal w (F.reducedSquareCoefficientMap w x) = 0 := by
  obtain ⟨p, rfl⟩ := F.squareFiltration.quotientTop.polynomialSymbolMap_surjective w x
  rw [F.reducedSquareCoefficientMap_symbol]
  exact (F.normalizedFirstCoefficientMap_range w).le ⟨F.reducedSquareDifferenceRelative w p, rfl⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem reducedSquareCoefficientMap_relativeMap
    (x : LinearMap.ker (F.firstCoefficientHorizontal w)) :
    F.reducedSquareCoefficientMap w (F.firstCoefficientRelativeMap w hw x) = x.val := by
  have hx : x.val ∈ LinearMap.range (F.normalizedFirstCoefficientMap w) :=
    (F.normalizedFirstCoefficientMap_range w).ge x.property
  obtain ⟨p, hp⟩ := hx
  have hm : F.normalizedFirstCoefficientMap w p ∈ LinearMap.ker (F.firstCoefficientHorizontal w) :=
    (F.normalizedFirstCoefficientMap_range w).le ⟨p, rfl⟩
  have he : x = ⟨F.normalizedFirstCoefficientMap w p, hm⟩ := Subtype.ext hp.symm
  rw [he]
  change F.reducedSquareCoefficientMap w
    (F.firstCoefficientRelativeEquiv w hw ⟨F.normalizedFirstCoefficientMap w p, hm⟩).val = _
  rw [F.firstCoefficientRelativeEquiv_apply, F.reducedSquareCoefficientMap_relative]

theorem firstCoefficientRelativeMap_coefficientMap
    (x : F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hx : x ∈ (F.reducedSquareSndSymbolMap w).ker) :
    F.firstCoefficientRelativeMap w hw
      ⟨F.reducedSquareCoefficientMap w x, F.reducedSquareCoefficientMap_horizontal w x⟩ = x := by
  have hx' : x ∈ LinearMap.range (F.reducedRelativeSquareSymbolMap w hw) :=
    (F.reducedRelativeSquareSymbolMap_range w hw).ge hx
  obtain ⟨p, rfl⟩ := hx'
  have hm : F.normalizedFirstCoefficientMap w p ∈ LinearMap.ker (F.firstCoefficientHorizontal w) :=
    (F.normalizedFirstCoefficientMap_range w).le ⟨p, rfl⟩
  have he : (⟨F.reducedSquareCoefficientMap w (F.reducedRelativeSquareSymbolMap w hw p),
      F.reducedSquareCoefficientMap_horizontal w _⟩ : LinearMap.ker (F.firstCoefficientHorizontal w)) =
      ⟨F.normalizedFirstCoefficientMap w p, hm⟩ :=
    Subtype.ext (F.reducedSquareCoefficientMap_relative w hw p)
  exact (congrArg (F.firstCoefficientRelativeMap w hw) he).trans
    (F.firstCoefficientRelativeEquiv_apply w hw p hm)

theorem firstCoefficientFastSubmodule_eq_image
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w)) :
    F.firstCoefficientFastSubmodule w hw U =
      (U ⊓ (F.reducedSquareSndSymbolMap w).ker.toSubmodule).map (F.reducedSquareCoefficientMap w) := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨F.firstCoefficientRelativeMap w hw x, ⟨hx, ?_⟩,
      F.reducedSquareCoefficientMap_relativeMap w hw x⟩
    exact (F.firstCoefficientRelativeEquiv w hw x).property
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨⟨F.reducedSquareCoefficientMap w x, F.reducedSquareCoefficientMap_horizontal w x⟩, ?_, rfl⟩
    change F.firstCoefficientRelativeMap w hw
      ⟨F.reducedSquareCoefficientMap w x, F.reducedSquareCoefficientMap_horizontal w x⟩ ∈ U
    rw [F.firstCoefficientRelativeMap_coefficientMap w hw x hx.2]
    exact hx.1

end Erdos3.NilpotentLieFiltration

end

end OAI

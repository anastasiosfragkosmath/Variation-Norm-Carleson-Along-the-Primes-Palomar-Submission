/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/OrdinarySymbolBasisDimension.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Dynamics.PointwiseSymbolBudget
public import OAI.Combinatorics.Progressions.Estimates.ProjectedPointwiseCoefficient
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem homogeneousSymbolLift_mem_pointwise (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hlayers) ω U.toSubmodule)
    (α : σ →₀ ℕ) (v : F.AssociatedGraded) (hv : v ∈ U) :
    F.homogeneousSymbolLift b ω hlayers w α v ∈ F.symbolPointwiseSubalgebra b ω hlayers w U := by
  classical
  rw [F.mem_symbolPointwiseSubalgebra_iff]
  intro β
  rw [F.gradedSymbolPolynomial_homogeneousSymbolLift, coefficients_monomial]
  by_cases h : α = β
  · subst β
    rw [Finsupp.single_eq_same]
    exact hU (Finsupp.weight w α) v hv
  · rw [Finsupp.single_eq_of_ne (Ne.symm h)]
    exact U.zero_mem

noncomputable def pointwiseSymbolSpanningFamily (v : κ → F.AssociatedGraded) :
    SymbolBasisIndex w ω × κ → F.PolynomialSymbol w :=
  fun z => F.homogeneousSymbolLift b ω hlayers w z.1.val.1 (v z.2)

theorem pointwiseSymbolSpanningFamily_span [Fintype (SymbolBasisIndex w ω)]
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hlayers) ω U.toSubmodule)
    (v : κ → F.AssociatedGraded) (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule) :
    Submodule.span ℚ (Set.range (F.pointwiseSymbolSpanningFamily b ω hlayers w v)) =
      (F.symbolPointwiseSubalgebra b ω hlayers w U).toSubmodule := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    apply F.homogeneousSymbolLift_mem_pointwise b ω hlayers w U hU
    change v z.2 ∈ U.toSubmodule
    rw [← hspan]
    exact Submodule.subset_span ⟨z.2, rfl⟩
  · intro x hx
    rw [← sum_basisBlockProjection (F.polynomialSymbolBasis b ω hlayers w) (fun z => z.val.1) x]
    apply Submodule.sum_mem
    intro α hα
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hα
    rw [← F.homogeneousSymbolLift_coefficient]
    let W := Submodule.span ℚ (Set.range (F.pointwiseSymbolSpanningFamily b ω hlayers w v))
    have hmap : U.toSubmodule ≤ W.comap (F.homogeneousSymbolLift b ω hlayers w z.val.1) := by
      rw [← hspan]
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨(z, j), rfl⟩
    exact hmap ((F.mem_symbolPointwiseSubalgebra_iff b ω hlayers w U x).mp hx z.val.1)

theorem pointwiseSymbolSpanningFamily_height (v : κ → F.AssociatedGraded) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ j i, RationalHeightLE ((F.associatedGradedBasis b ω hlayers).repr (v j) i) H) :
    ∀ z i, RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr
      (F.pointwiseSymbolSpanningFamily b ω hlayers w v z) i) H := by
  classical
  intro z i
  change RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr
    (F.homogeneousSymbolLift b ω hlayers w z.1.val.1 (v z.2)) i) H
  rw [F.homogeneousSymbolLift_coordinate]
  split_ifs
  · exact hv z.2 i.val.2
  · exact rationalHeightLE_zero hH

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [Fintype σ] [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hF

end Erdos3.NilpotentLieFiltration

end

end OAI

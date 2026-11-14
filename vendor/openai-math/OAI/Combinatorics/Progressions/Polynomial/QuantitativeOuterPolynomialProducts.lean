/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/QuantitativeOuterPolynomialProducts.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.RealSubspaceIntersectionCorrections
public import OAI.Combinatorics.Progressions.Geometry.RealSubspaceCoordinateRetraction
public import OAI.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection
public import OAI.Combinatorics.Progressions.Polynomial.FormalPolynomialCorrectionStep
public import OAI.Combinatorics.Progressions.Sampling.RealAdaptedCoefficientGrid
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

def CoefficientBound (b : Basis ι ℝ L) (T : σ → ℝ) (M : ℝ)
    (P : VectorPolynomial σ ℚ L) : Prop :=
  ∀ α i, |b.repr (coefficients P α) i| ≤ M / monomialScale T α

def CoefficientGrid (b : Basis ι ℝ L) (l : ℕ) (P : VectorPolynomial σ ℚ L) : Prop :=
  ∀ α, (fun i => b.repr (coefficients P α) i) ∈ realDenominatorGrid l

theorem coefficientBound_iff_norm [Fintype ι] (b : Basis ι ℝ L)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (P : VectorPolynomial σ ℚ L) :
    CoefficientBound b T M P ↔ ∀ α, ‖b.equivFun (coefficients P α)‖ ≤ M / monomialScale T α := by
  constructor
  · intro h α
    exact (pi_norm_le_iff_of_nonneg (div_nonneg hM (monomialScale_pos T hT α).le)).mpr (h α)
  · intro h α i
    exact (norm_le_pi_norm (b.equivFun (coefficients P α)) i).trans (h α)

theorem CoefficientBound.mono (b : Basis ι ℝ L) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M N : ℝ} {P : VectorPolynomial σ ℚ L} (h : CoefficientBound b T M P) (hMN : M ≤ N) :
    CoefficientBound b T N P := by
  intro α i
  exact (h α i).trans (div_le_div_of_nonneg_right hMN (monomialScale_pos T hT α).le)

theorem CoefficientBound.neg (b : Basis ι ℝ L) (T : σ → ℝ) {M : ℝ}
    {P : VectorPolynomial σ ℚ L} (h : CoefficientBound b T M P) : CoefficientBound b T M (-P) := by
  intro α i
  simpa only [map_neg, Finsupp.neg_apply, abs_neg] using h α i

theorem CoefficientBound.sub (b : Basis ι ℝ L) (T : σ → ℝ) {M N : ℝ}
    {P Q : VectorPolynomial σ ℚ L} (hP : CoefficientBound b T M P) (hQ : CoefficientBound b T N Q) :
    CoefficientBound b T (M + N) (P - Q) := by
  intro α i
  simp only [map_sub, Finsupp.sub_apply]
  exact (abs_sub _ _).trans ((add_le_add (hP α i) (hQ α i)).trans_eq (by ring))

theorem CoefficientGrid.sub (b : Basis ι ℝ L) (l : ℕ)
    {P Q : VectorPolynomial σ ℚ L} (hP : CoefficientGrid b l P) (hQ : CoefficientGrid b l Q) :
    CoefficientGrid b l (P - Q) := by
  intro α
  simp only [map_sub, Finsupp.sub_apply]
  exact realDenominatorGrid_sub l _ _ (hP α) (hQ α)

end VectorPolynomial

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hF in
theorem gradedPolynomial_mem_adapted (w : σ → ℕ) (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hP : P ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω w) :
    P ∈ F.realification.adaptedLieSubalgebra w := by
  intro α
  have h := F.realGradeProjection_mem_layer b ω hF (Finsupp.weight w α) (coefficients P α)
  have he : basisGradeProjection (b.baseChange ℝ) ω (Finsupp.weight w α) (coefficients P α) = coefficients P α := hP α
  rw [he] at h
  exact h

include hF in
theorem shiftedGradedPolynomial_mem_adapted (w : σ → ℕ) (r : ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hP : P ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω w r) :
    P ∈ F.realification.adaptedLieSubalgebra w := by
  intro α
  have h := F.realGradeProjection_mem_layer b ω hF (Finsupp.weight w α + r) (coefficients P α)
  have he : basisGradeProjection (b.baseChange ℝ) ω (Finsupp.weight w α + r) (coefficients P α) = coefficients P α := hP α
  rw [he] at h
  exact F.realification.antitone (Nat.le_add_right _ _) h

include b ω hF in
theorem exists_real_adapted_representation (w : σ → ℕ) (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hP : P ∈ F.realification.adaptedLieSubalgebra w) :
    ∃ x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w, F.realAdaptedPolynomialMap w x = P := by
  obtain ⟨x, hx⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF ⟨P, hP⟩
  exact ⟨x, congrArg Subtype.val hx⟩

theorem realAdaptedCoefficientBound_iff_formal (w : σ → ℕ) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.RealAdaptedCoefficientBound b ω hF w T M x ↔
      CoefficientBound (b.baseChange ℝ) T M (F.realAdaptedPolynomialMap w x) :=
  F.realAdaptedCoefficientBound_polynomial_iff b ω hF w T hT hM ⟨x⟩

theorem realAdaptedCoefficientGrid_iff_formal (w : σ → ℕ) (l : ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.RealAdaptedCoefficientGrid b ω hF w l x ↔
      CoefficientGrid (b.baseChange ℝ) l (F.realAdaptedPolynomialMap w x) := by
  rw [F.realAdaptedCoefficientGrid_polynomial_iff b ω hF w l ⟨x⟩]
  constructor
  · rintro ⟨a, ha⟩ α
    exact ⟨fun i => a (α, i), funext (fun i => congrFun ha (α, i))⟩
  · intro h
    choose a ha using h
    exact ⟨fun z => a z.1 z.2, funext (fun z => congrFun (ha z.1) z.2)⟩

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

noncomputable def adaptedFullPolynomialHom (F : NilpotentLieFiltration L s) (w : σ → ℕ) :
    (F.adaptedPolynomialFiltration w).Group →* PolynomialGroup σ F.lowerCentralSeries_eq_bot :=
  NilpotentLieBCHGroup.map (F.adaptedLieSubalgebra w).incl

@[simp] theorem adaptedFullPolynomialHom_coord (F : NilpotentLieFiltration L s) (w : σ → ℕ)
    (g : (F.adaptedPolynomialFiltration w).Group) :
    (F.adaptedFullPolynomialHom w g).coord = (g.coord : VectorPolynomial σ ℚ L) := rfl

theorem exists_adapted_polynomial_list_lift (F : NilpotentLieFiltration L s) (w : σ → ℕ)
    (rs : List (PolynomialGroup σ F.lowerCentralSeries_eq_bot))
    (hadapted : ∀ r ∈ rs, r.coord ∈ F.adaptedLieSubalgebra w) :
    ∃ xs : List (F.adaptedPolynomialFiltration w).Group,
      xs.map (F.adaptedFullPolynomialHom w) = rs := by
  induction rs with
  | nil => exact ⟨[], rfl⟩
  | cons r rs ih =>
    obtain ⟨xs, hxs⟩ := ih (fun x hx => hadapted x (List.mem_cons_of_mem r hx))
    let x : (F.adaptedPolynomialFiltration w).Group := ⟨⟨r.coord, hadapted r (List.mem_cons_self)⟩⟩
    have hx : F.adaptedFullPolynomialHom w x = r := NilpotentLieBCHGroup.ext rfl
    exact ⟨x :: xs, by rw [List.map_cons, hx, hxs]⟩

theorem polynomialRationalGrid_iff_formal {ι : Type*} (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (w : σ → ℕ) (l : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.PolynomialRationalGrid b w l g ↔
      CoefficientGrid (b.baseChange ℝ) l (F.realification.adaptedFullPolynomialHom w g).coord := by
  constructor
  · rintro ⟨a, ha⟩ α
    exact ⟨fun i => a (α, i), funext (fun i => congrFun ha (α, i))⟩
  · intro h
    choose a ha using h
    exact ⟨fun z => a z.1 z.2, funext (fun z => congrFun (ha z.1) z.2)⟩

theorem polynomialSlowBound_iff_formal {ι : Type*} (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (w : σ → ℕ) (T : σ → ℝ) (M : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.PolynomialSlowBound b w T M g ↔
      CoefficientBound (b.baseChange ℝ) T M (F.realification.adaptedFullPolynomialHom w g).coord :=
  Iff.rfl

theorem exists_formal_polynomial_product_bound (s a k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      ∀ rs : List (PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot), rs.length ≤ k →
      (∀ r ∈ rs, r.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1)) →
      (∀ r ∈ rs, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) r.coord) →
      CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) rs.prod.coord := by
  obtain ⟨C, hC, hprod⟩ := exists_polynomial_slow_product_bound s a k
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hstructure T hT rs hlen hadapted hbound
  obtain ⟨xs, hxs⟩ := F.realification.exists_adapted_polynomial_list_lift (fun _ => 1) rs hadapted
  have hxlen : xs.length ≤ k := by simpa only [← hxs, List.length_map] using hlen
  have hxbound : ∀ x ∈ xs, F.PolynomialSlowBound b (fun _ => 1) T (Real.exp ((p + 2) ^ a)) x := by
    intro x hx
    have hmem : F.realification.adaptedFullPolynomialHom (fun _ => 1) x ∈ rs := by
      rw [← hxs]
      exact List.mem_map_of_mem hx
    exact (F.polynomialSlowBound_iff_formal b _ T _ x).mpr (hbound _ hmem)
  have hout := (F.polynomialSlowBound_iff_formal b _ T _ xs.prod).mp (
    hprod F b ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) H p hH hp hι hσ hHp hstructure
      T hT xs hxlen hxbound)
  rwa [map_list_prod, hxs] at hout

theorem exists_formal_polynomial_product_grid (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ rs : List (PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot), rs.length ≤ k →
        (∀ r ∈ rs, r.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1)) →
        (∀ r ∈ rs, CoefficientGrid (b.baseChange ℝ) l r.coord) →
        CoefficientGrid (b.baseChange ℝ) m rs.prod.coord := by
  obtain ⟨C, hC, hprod⟩ := exists_polynomial_rational_product_bound s k
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  obtain ⟨m, hm, hmp, hlm, hgrid⟩ :=
    hprod F b ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) H p hH hp hι hσ hHp hstructure l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro rs hlen hadapted hbound
  obtain ⟨xs, hxs⟩ := F.realification.exists_adapted_polynomial_list_lift (fun _ => 1) rs hadapted
  have hxlen : xs.length ≤ k := by simpa only [← hxs, List.length_map] using hlen
  have hxgrid : ∀ x ∈ xs, F.PolynomialRationalGrid b (fun _ => 1) l x := by
    intro x hx
    have hmem : F.realification.adaptedFullPolynomialHom (fun _ => 1) x ∈ rs := by
      rw [← hxs]
      exact List.mem_map_of_mem hx
    exact (F.polynomialRationalGrid_iff_formal b _ l x).mpr (hbound _ hmem)
  have hout := (F.polynomialRationalGrid_iff_formal b _ m xs.prod).mp (hgrid xs hxlen hxgrid)
  rwa [map_list_prod, hxs] at hout

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

section Modules

variable {σ ι κ L M : Type*} [AddCommGroup L] [Module ℚ L]
  [AddCommGroup M] [Module ℚ M]

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

end Modules

section LieModules

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

end LieModules

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {s : ℕ}

noncomputable def positiveUnivariate (v : Fin s → V) : VectorPolynomial Unit ℚ V :=
  ∑ d, monomial (Finsupp.single () (d.val + 1)) (v d)

theorem positiveUnivariate_coefficient (v : Fin s → V) (d : Fin s) :
    coefficients (positiveUnivariate v) (Finsupp.single () (d.val + 1)) = v d := by
  classical
  simp only [positiveUnivariate, map_sum, Finsupp.finsetSum_apply, coefficients_monomial]
  rw [Finset.sum_eq_single d]
  · simp only [Finsupp.single_eq_same]
  · intro j _ hj
    apply Finsupp.single_eq_of_ne
    intro heq
    apply hj
    apply Fin.ext
    have h := congrArg (fun α : Unit →₀ ℕ => α ()) heq
    simp only [Finsupp.single_eq_same] at h
    omega
  · simp

theorem positiveUnivariate_coefficient_eq_zero (v : Fin s → V) (α : Unit →₀ ℕ)
    (hα : ∀ d : Fin s, Finsupp.single () (d.val + 1) ≠ α) :
    coefficients (positiveUnivariate v) α = 0 := by
  classical
  simp only [positiveUnivariate, map_sum, Finsupp.finsetSum_apply, coefficients_monomial]
  exact Finset.sum_eq_zero (fun d _ => Finsupp.single_eq_of_ne (hα d).symm)

theorem positiveUnivariate_zero (v : Fin s → V) : coefficients (positiveUnivariate v) 0 = 0 := by
  apply positiveUnivariate_coefficient_eq_zero
  intro d h
  have h' := congrArg (fun α : Unit →₀ ℕ => α ()) h
  simp only [Finsupp.single_eq_same, Finsupp.zero_apply] at h'
  omega

theorem positiveUnivariate_coefficients_mem (v : Fin s → V) (U : (Unit →₀ ℕ) → Submodule ℚ V)
    (hv : ∀ d, v d ∈ U (Finsupp.single () (d.val + 1))) :
    ∀ α, coefficients (positiveUnivariate v) α ∈ U α := by
  intro α
  by_cases hα : ∃ d : Fin s, Finsupp.single () (d.val + 1) = α
  · obtain ⟨d, rfl⟩ := hα
    rw [positiveUnivariate_coefficient]
    exact hv d
  · rw [positiveUnivariate_coefficient_eq_zero v α (by simpa only [not_exists] using hα)]
    exact (U α).zero_mem

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

theorem positiveUnivariate_coefficientBound (b : Basis ι ℝ L) (v : Fin s → L)
    (T : Unit → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (hv : ∀ d, ‖b.equivFun (v d)‖ ≤ M / monomialScale T (Finsupp.single () (d.val + 1))) :
    CoefficientBound b T M (positiveUnivariate v) := by
  apply (coefficientBound_iff_norm b T hT hM _).mpr
  intro α
  by_cases hα : ∃ d : Fin s, Finsupp.single () (d.val + 1) = α
  · obtain ⟨d, rfl⟩ := hα
    rw [positiveUnivariate_coefficient]
    exact hv d
  · rw [positiveUnivariate_coefficient_eq_zero v α (by simpa only [not_exists] using hα),
      map_zero, norm_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem positiveUnivariate_coefficientGrid (b : Basis ι ℝ L) (v : Fin s → L) (l : ℕ)
    (hv : ∀ d, b.equivFun (v d) ∈ realDenominatorGrid l) :
    CoefficientGrid b l (positiveUnivariate v) := by
  intro α
  by_cases hα : ∃ d : Fin s, Finsupp.single () (d.val + 1) = α
  · obtain ⟨d, rfl⟩ := hα
    rw [positiveUnivariate_coefficient]
    simpa only [Basis.equivFun_apply] using hv d
  · rw [positiveUnivariate_coefficient_eq_zero v α (by simpa only [not_exists] using hα)]
    refine ⟨0, ?_⟩
    ext i
    simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module

variable {σ ι V : Type*}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.NilpotentLieFiltration

end

end OAI

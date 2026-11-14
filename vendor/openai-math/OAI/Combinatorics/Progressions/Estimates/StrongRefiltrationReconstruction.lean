/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/StrongRefiltrationReconstruction.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
public import OAI.Combinatorics.Progressions.Nilpotent.RealifiedBCHProductEquiv
public import OAI.Combinatorics.Progressions.Polynomial.RefilteredPolynomialProjection
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (f : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

theorem symbolPointwiseSubalgebra_mono {U V : LieSubalgebra ℚ F.AssociatedGraded} (hUV : U ≤ V) :
    F.symbolPointwiseSubalgebra e ω hF w U ≤ F.symbolPointwiseSubalgebra e ω hF w V := by
  intro x hx
  exact fun α => hUV ((F.mem_symbolPointwiseSubalgebra_iff e ω hF w U x).mp hx α)

theorem symbolPointwiseSubalgebra_map_le (U : LieSubalgebra ℚ F.AssociatedGraded) :
    (F.symbolPointwiseSubalgebra e ω hF w U).map (F.filteredPolynomialSymbolMap G φ hφ w) ≤
      G.symbolPointwiseSubalgebra f ν hG w (U.map (F.associatedGradedMap G φ hφ)) := by
  rintro _ ⟨x, hx, rfl⟩
  apply (G.mem_symbolPointwiseSubalgebra_iff f ν hG w _ _).mpr
  intro α
  simp only [LieHom.coe_toLinearMap]
  have hm : F.associatedGradedMap G φ hφ (coefficients (F.gradedSymbolPolynomial e ω hF w x) α) ∈
      U.map (F.associatedGradedMap G φ hφ) :=
    ⟨_, (F.mem_symbolPointwiseSubalgebra_iff e ω hF w U x).mp hx α, rfl⟩
  rw [F.gradedSymbolPolynomial_filteredMap_coefficient G e ω hF f ν hG φ hφ w x α]
  exact hm

theorem symbolPointwiseSubalgebra_comap (U : LieSubalgebra ℚ G.AssociatedGraded) :
    (G.symbolPointwiseSubalgebra f ν hG w U).comap (F.filteredPolynomialSymbolMap G φ hφ w) =
      F.symbolPointwiseSubalgebra e ω hF w (U.comap (F.associatedGradedMap G φ hφ)) := by
  ext x
  constructor
  · intro hx
    simp only [LieSubalgebra.mem_comap] at hx
    apply (F.mem_symbolPointwiseSubalgebra_iff e ω hF w _ x).mpr
    intro α
    have hm := (G.mem_symbolPointwiseSubalgebra_iff f ν hG w U
      (F.filteredPolynomialSymbolMap G φ hφ w x)).mp hx α
    rw [F.gradedSymbolPolynomial_filteredMap_coefficient G e ω hF f ν hG φ hφ w x α] at hm
    exact hm
  · intro hx
    simp only [LieSubalgebra.mem_comap]
    apply (G.mem_symbolPointwiseSubalgebra_iff f ν hG w U _).mpr
    intro α
    have hm : F.associatedGradedMap G φ hφ (coefficients (F.gradedSymbolPolynomial e ω hF w x) α) ∈ U :=
      (F.mem_symbolPointwiseSubalgebra_iff e ω hF w _ x).mp hx α
    rw [F.gradedSymbolPolynomial_filteredMap_coefficient G e ω hF f ν hG φ hφ w x α]
    exact hm

theorem symbolPointwiseSubalgebra_map [Fintype (SymbolBasisIndex w ν)]
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule) :
    (F.symbolPointwiseSubalgebra e ω hF w U).map (F.filteredPolynomialSymbolMap G φ hφ w) =
      G.symbolPointwiseSubalgebra f ν hG w (U.map (F.associatedGradedMap G φ hφ)) := by
  classical
  apply le_antisymm (F.symbolPointwiseSubalgebra_map_le G e ω hF f ν hG φ hφ w U)
  intro x hx
  change x ∈ ((F.symbolPointwiseSubalgebra e ω hF w U).map
    (F.filteredPolynomialSymbolMap G φ hφ w)).toSubmodule
  rw [← sum_basisBlockProjection (G.polynomialSymbolBasis f ν hG w) (fun z => z.val.1) x]
  apply Submodule.sum_mem
  intro α _
  obtain ⟨v, hv, he⟩ := (G.mem_symbolPointwiseSubalgebra_iff f ν hG w _ x).mp hx α
  refine ⟨F.homogeneousSymbolLift e ω hF w α v,
    F.homogeneousSymbolLift_mem_pointwise e ω hF w U hU α v hv, ?_⟩
  change F.filteredPolynomialSymbolMap G φ hφ w (F.homogeneousSymbolLift e ω hF w α v) = _
  change F.associatedGradedMap G φ hφ v = _ at he
  rw [F.homogeneousSymbolLift_filteredMap G e ω hF f ν hG φ hφ w, he,
    G.homogeneousSymbolLift_coefficient]

theorem associatedGradedMap_image_graded (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule) :
    BasisGradedSubmodule (G.associatedGradedBasis f ν hG) ν
      (U.map (F.associatedGradedMap G φ hφ)).toSubmodule := by
  rintro j _ ⟨x, hx, rfl⟩
  exact ⟨basisGradeProjection (F.associatedGradedBasis e ω hF) ω j x, hU j x hx,
    F.associatedGradedMap_gradeProjection G e ω hF f ν hG φ hφ j x⟩

theorem associatedGradedMap_comap_graded (U : LieSubalgebra ℚ G.AssociatedGraded)
    (hU : BasisGradedSubmodule (G.associatedGradedBasis f ν hG) ν U.toSubmodule) :
    BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω
      (U.comap (F.associatedGradedMap G φ hφ)).toSubmodule := by
  intro j x hx
  change F.associatedGradedMap G φ hφ
    (basisGradeProjection (F.associatedGradedBasis e ω hF) ω j x) ∈ U
  rw [F.associatedGradedMap_gradeProjection G e ω hF f ν hG φ hφ]
  exact hU j _ hx

end Erdos3.NilpotentLieFiltration

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

variable {ι : Type v} {H : Type u} {L : ι → Type u}
  [LieRing H] [LieAlgebra ℚ H] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NilpotentLieFiltration
open Module
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (w : σ → ℕ)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (b : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (b '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

universe u

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {J : Type v} [Fintype J] {L : Type u} {M : J → Type u} {Y : Type*}
  [LieRing L] [LieAlgebra ℚ L] [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
  [LieRing Y] [LieAlgebra ℚ Y] {s d₀ dQ : ℕ} {d : J → ℕ}
  (D : RationalFilteredNilmanifold L s d₀)
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (d j))
  (π : L →ₗ⁅ℚ⁆ Y) (eta : J → L →ₗ[ℚ] ℚ) (js : List J)
  (Q : RationalFilteredNilmanifold
    (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) s dQ)
  (hQ : Q.filtration = D.filtration.quotientLie
    (D.filtration.pivotAnnihilatorIdeal π eta js)
    (by rw [D.filtration.terminal]; exact bot_le))

include hQ

variable (U : LieSubalgebra ℚ (optionProduct D E).filtration.AssociatedGraded)

variable {κ κQ : Type*}
  (e : Basis κ ℚ (∀ i : Option J, optionLieSpace L M i)) (μ : κ → ℕ)
  (hSource : ∀ k, (optionProduct D E).filtration.layer k =
    Submodule.span ℚ (e '' {i | k ≤ μ i}))
  (c : Basis κQ ℚ (∀ i : Option J,
    optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) M i))
  (ν : κQ → ℕ)
  (hTarget : ∀ k, (optionProduct Q E).filtration.layer k =
    Submodule.span ℚ (c '' {i | k ≤ ν i}))
  (hU : BasisGradedSubmodule
    ((optionProduct D E).filtration.associatedGradedBasis e μ hSource) μ U.toSubmodule)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (U : LieSubalgebra ℚ F.AssociatedGraded)

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (b : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (b '' {i | j ≤ ν i}))
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (htop : ∀ a ∈ U,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω s a = a →
      F.associatedGradedMap G φ hφ a = 0 → a = 0)

end Erdos3.NilpotentLieFiltration

end

end OAI

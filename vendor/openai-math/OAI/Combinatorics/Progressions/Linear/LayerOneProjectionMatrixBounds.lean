/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/LayerOneProjectionMatrixBounds.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import OAI.Combinatorics.Progressions.Geometry.ControlledLayerOneCoordinates
public import OAI.Combinatorics.Progressions.Geometry.LayerOneTransportBudget
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct Matrix

theorem rational_horizontal_basis_transport
    {V ι κ ν : Type*} [AddCommGroup V] [Module ℚ V]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (b : Basis ι ℚ V) (η : (κ → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] V))
    (A : Matrix ι κ ℚ)
    (hA : ∀ x, (b.baseChange ℝ).equivFun (η x) = A.map (Rat.castHom ℝ) *ᵥ x)
    (K : Submodule ℝ (κ → ℝ)) (Q : Matrix κ ν ℚ)
    (hK : K = Submodule.span ℝ (Set.range (Q.map (Rat.castHom ℝ)).col))
    (hQ : LinearIndependent ℝ (Q.map (Rat.castHom ℝ)).col)
    {H J : ℕ} (hAH : ∀ i j, RationalHeightLE (A i j) H)
    (hQJ : ∀ i j, RationalHeightLE (Q i j) J) :
    ∃ v : ν → V,
      (∀ j, (1 : ℝ) ⊗ₜ[ℚ] v j = η ((Q.map (Rat.castHom ℝ)).col j)) ∧
      K.map η.toLinearMap = (Submodule.span ℚ (Set.range v)).baseChange ℝ ∧
      LinearIndependent ℚ v ∧
      ∀ i j, RationalHeightLE (b.repr (v j) i) ((Fintype.card κ + 1) * (H * J) ^ Fintype.card κ) := by
  let v : ν → V := fun j => b.equivFun.symm ((A * Q).col j)
  have hvc (i : ι) (j : ν) : b.repr (v j) i = (A * Q) i j :=
    congrFun (b.equivFun.apply_symm_apply ((A * Q).col j)) i
  have hv (j : ν) : (1 : ℝ) ⊗ₜ[ℚ] v j = η ((Q.map (Rat.castHom ℝ)).col j) := by
    apply (b.baseChange ℝ).equivFun.injective
    rw [hA]
    funext i
    rw [Basis.equivFun_apply, Basis.baseChange_repr_tmul, hvc]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]
  refine ⟨v, hv, ?_, ?_, ?_⟩
  · rw [hK, Submodule.map_span, Submodule.baseChange_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨v j, ⟨j, rfl⟩, hv j⟩
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨_, ⟨j, rfl⟩, (hv j).symm⟩
  · have hreal : LinearIndependent ℝ (fun j => (1 : ℝ) ⊗ₜ[ℚ] v j) := by
      simpa only [hv, Function.comp_def, LinearEquiv.coe_coe] using
        hQ.map' η.toLinearMap (LinearMap.ker_eq_bot.mpr η.injective)
    apply LinearIndependent.of_comp (TensorProduct.mk ℚ ℝ V 1)
    exact LinearIndependent.restrict_scalars' ℚ hreal
  · intro i j
    rw [hvc]
    exact rationalHeightLE_matrix_mul A Q hAH hQJ i j

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct Matrix

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s a d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
  (b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
    F.realFirstCoefficientFastSubmodule w hw U))
  (ha : a ≤ d) (η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)))
  (hη : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = F.realFastCoefficientHorizontal w hw U x)
  (R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w)
  (hR : ∀ y, (F.realFirstCoefficientFastSubmodule w hw U).mkQ (R y) = b.equivFun.symm y)
  (l m : ℕ) (hm : 0 < m) (C : ℝ) (hC : 0 ≤ C)
  (hgrid : ∀ y, y ∈ realDenominatorGrid l → F.FirstCoefficientGrid e ω hF w m (R y))
  (hbound : ∀ (y : Fin d → ℝ) (M : ℝ), 0 ≤ M → (∀ j, |y j| ≤ M) →
    F.FirstCoefficientSlowBound e ω hF w (fun _ => 1) (C * M) (R y))

include hη hR hm hC hgrid hbound

theorem layerOne_equiv_rational_matrix :
    ∃ A : Matrix (LayerOneBasisIndex ω) (Fin a) ℚ,
      (∀ i j, RationalHeightLE (A i j) (max m (Nat.ceil ((m : ℝ) * C)))) ∧
      ∀ x, ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (η x) =
        A.map (Rat.castHom ℝ) *ᵥ x := by
  exact exists_bounded_rational_map_matrix
    (((F.layerOneBasis e ω hF).baseChange ℝ).equivFun.toLinearMap.comp η.toLinearMap)
    m hm (fun j => F.layerOne_equiv_grid e ω hF w hw U b ha η hη l m R hR hgrid
      (Pi.single j 1) (realDenominatorGrid_single l j)) C
    (F.layerOne_equiv_norm e ω hF w hw U b ha η hη C hC R hR hbound)

theorem layerOne_rational_kernel_basis {ν : Type*}
    (K : Submodule ℝ (Fin a → ℝ)) (Q : Matrix (Fin a) ν ℚ)
    (hK : K = Submodule.span ℝ (Set.range (Q.map (Rat.castHom ℝ)).col))
    (hQ : LinearIndependent ℝ (Q.map (Rat.castHom ℝ)).col)
    {J : ℕ} (hQJ : ∀ i j, RationalHeightLE (Q i j) J) :
    ∃ v : ν → L ⧸ F.layer 2,
      (∀ j, (1 : ℝ) ⊗ₜ[ℚ] v j = η ((Q.map (Rat.castHom ℝ)).col j)) ∧
      K.map η.toLinearMap = (Submodule.span ℚ (Set.range v)).baseChange ℝ ∧
      LinearIndependent ℚ v ∧
      ∀ i j, RationalHeightLE ((F.layerOneBasis e ω hF).repr (v j) i)
        ((a + 1) * (max m (Nat.ceil ((m : ℝ) * C)) * J) ^ a) := by
  obtain ⟨A, hA, heq⟩ := F.layerOne_equiv_rational_matrix e ω hF w hw U b ha η hη
    R hR l m hm C hC hgrid hbound
  simpa only [Fintype.card_fin] using rational_horizontal_basis_transport
    (F.layerOneBasis e ω hF) η A heq K Q hK hQ hA hQJ

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct NNReal Matrix

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s a d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
  (b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
    F.realFirstCoefficientFastSubmodule w hw U))
  (ha : a ≤ d) (η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)))
  (hη : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = F.realFastCoefficientHorizontal w hw U x)
  (A : Matrix (LayerOneBasisIndex ω) (Fin a) ℚ)
  (hA : ∀ x, ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (η x) =
    A.map (Rat.castHom ℝ) *ᵥ x)

include hη hA

end Erdos3.NilpotentLieFiltration

end

end OAI

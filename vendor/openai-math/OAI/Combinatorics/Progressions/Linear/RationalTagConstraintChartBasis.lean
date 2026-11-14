/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/RationalTagConstraintChartBasis.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.MvPolynomial.Basic
public import OAI.Combinatorics.Progressions.Estimates.DerivativeIndexBounds
public import OAI.Combinatorics.Progressions.Estimates.IndependentColumnsMinor
public import OAI.Combinatorics.Progressions.Estimates.PartiallyBoundedNormalization
public import OAI.Combinatorics.Progressions.Lattices.LatticeMinorNormBound
public import OAI.Combinatorics.Progressions.Dynamics.RationalConstraintCountBudget
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {κ V : Type*} [AddCommGroup V] [Module ℚ V]
  (K : Submodule ℚ V) (b : Basis κ ℚ K)

noncomputable def realSubmoduleBasis : Basis κ ℝ (K.baseChange ℝ) :=
  (b.baseChange ℝ).map (realificationSubmoduleEquiv K)

theorem realSubmoduleBasis_coe (i : κ) :
    (realSubmoduleBasis K b i : ℝ ⊗[ℚ] V) = (1 : ℝ) ⊗ₜ[ℚ] (b i : V) := by
  rw [realSubmoduleBasis, Basis.map_apply, Basis.baseChange_apply, realificationSubmoduleEquiv_tmul]

variable [Fintype κ]

noncomputable def realSubmoduleParameterization : (κ → ℝ) ≃ₗ[ℝ] K.baseChange ℝ :=
  (realSubmoduleBasis K b).equivFun.symm

theorem realSubmoduleParameterization_basis (i : κ) :
    realSubmoduleParameterization K b (Pi.basisFun ℝ κ i) = realSubmoduleBasis K b i := by
  classical
  apply (realSubmoduleBasis K b).equivFun.injective
  rw [realSubmoduleParameterization, LinearEquiv.apply_symm_apply]
  ext j
  simp [Pi.basisFun_apply, Pi.single_apply, eq_comm]

end Erdos3

end

section

namespace Erdos3

theorem basis_projection_range_eq_span {E ι κ : Type*}
    [AddCommGroup E] [Module ℝ E] (b : Module.Basis κ ℝ E)
    (P : E →ₗ[ℝ] (ι → ℝ)) :
    LinearMap.range P = Submodule.span ℝ (Set.range (fun j => P (b j))) := by
  rw [← Submodule.map_top, ← b.span_eq, Submodule.map_span, ← Set.range_comp]
  rfl

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem exists_bounded_rational_projection_lift
    {E F α β : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype α] {k : ℕ}
    (b : Module.Basis (Fin k) ℝ E) (P : E →ₗ[ℝ] (α → ℝ))
    (hP : Function.Injective P) (g : E →ₗ[ℝ] (β → ℝ))
    (e : α → β) (hhor : ∀ v i, g v (e i) = P v i)
    (W : (β → ℝ) →ₗ[ℝ] F) (C : ℝ)
    (hbound : ∀ v, ‖W (g v)‖ ≤ C * ‖P v‖)
    (B : Matrix β (Fin k) ℝ) (hB : ∀ i j, B i j = g (b j) i)
    (p : Fin k → α) (hp : (B.submatrix (e ∘ p) id).det ≠ 0)
    (Q : Matrix β (Fin k) ℚ)
    (hQ : Q.map (Rat.castHom ℝ) = B * (B.submatrix (e ∘ p) id)⁻¹)
    (hQid : Q.submatrix (e ∘ p) id = 1) :
    let QH := Q.submatrix e id
    ∃ R : LinearMap.range P →ₗ[ℝ] (β → ℝ),
      (∀ x i, R x (e i) = x.val i) ∧
      (∀ x, ‖W (R x)‖ ≤ C * ‖x‖) ∧
      (∀ v, R ⟨P v, v, rfl⟩ = g v) ∧
      LinearMap.range P = Submodule.span ℝ (Set.range (QH.map (Rat.castHom ℝ)).col) ∧
      LinearIndependent ℝ (QH.map (Rat.castHom ℝ)).col ∧
      LinearIndependent ℚ QH.col ∧
      (∀ j, ∃ x : LinearMap.range P,
        x.val = (QH.map (Rat.castHom ℝ)).col j ∧ R x = (Q.map (Rat.castHom ℝ)).col j) := by
  let J := (LinearEquiv.ofInjective P hP).symm.toLinearMap
  have hJ (x : LinearMap.range P) : P (J x) = x.val :=
    congrArg Subtype.val ((LinearEquiv.ofInjective P hP).apply_symm_apply x)
  let R := g.comp J
  let H := B.submatrix e id
  let QH := Q.submatrix e id
  have hHcol : H.col = fun j => P (b j) := by
    funext j i
    exact (hB (e i) j).trans (hhor (b j) i)
  have hQH : QH.map (Rat.castHom ℝ) = H * (H.submatrix p id)⁻¹ := by
    ext i j
    exact congrArg (fun M : Matrix β (Fin k) ℝ => M (e i) j) hQ
  have hQHid : QH.submatrix p id = 1 := hQid
  have hrealid : (QH.map (Rat.castHom ℝ)).submatrix p id = 1 := by
    rw [hQH]
    exact row_normalization_submatrix H p hp
  refine ⟨R, ?_, ?_, ?_, ?_, independent_columns_of_identity_minor _ p hrealid,
    independent_columns_of_identity_minor QH p hQHid, ?_⟩
  · intro x i
    exact (hhor (J x) i).trans (congrFun (hJ x) i)
  · intro x
    have h := hbound (J x)
    rw [hJ x] at h
    exact h
  · intro v
    have h : J ⟨P v, v, rfl⟩ = v := hP (hJ ⟨P v, v, rfl⟩)
    change g (J ⟨P v, v, rfl⟩) = g v
    rw [h]
  · change LinearMap.range P = Submodule.span ℝ (Set.range (QH.map (Rat.castHom ℝ)).col)
    rw [hQH, row_normalization_col_span H p hp, hHcol]
    exact basis_projection_range_eq_span b P
  · intro j
    obtain ⟨v, hv⟩ := exists_normalized_basis_vector b g B hB
      (B.submatrix (e ∘ p) id)⁻¹ j
    have hv' : g v = (Q.map (Rat.castHom ℝ)).col j := by
      rw [hQ]
      exact hv
    let x : LinearMap.range P := ⟨P v, v, rfl⟩
    refine ⟨x, ?_, ?_⟩
    · funext i
      exact (hhor v i).symm.trans (congrFun hv' (e i))
    · have hx : J x = v := hP (hJ x)
      change g (J x) = _
      rw [hx]
      exact hv'

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]
  (e : Basis ι ℚ V) (K : Submodule ℚ V) (b : Basis κ ℚ K)

noncomputable def submoduleBasisMatrix : Matrix ι κ ℚ :=
  fun i j => e.repr (b j).val i

theorem realSubmoduleBasis_matrix_coordinates (j : κ) :
    (e.baseChange ℝ).equivFun (realSubmoduleBasis K b j).val =
      ((submoduleBasisMatrix e K b).map (Rat.castHom ℝ)).col j := by
  funext i
  rw [Basis.equivFun_apply, realSubmoduleBasis_coe, Basis.baseChange_repr_tmul]
  simp [submoduleBasisMatrix, Matrix.col, Algebra.smul_def]

theorem realSubmoduleBasis_matrix_span :
    Submodule.span ℝ (Set.range ((submoduleBasisMatrix e K b).map (Rat.castHom ℝ)).col) =
      (K.baseChange ℝ).map (e.baseChange ℝ).equivFun.toLinearMap := by
  let f := (e.baseChange ℝ).equivFun.toLinearMap.comp (K.baseChange ℝ).subtype
  have he : (f ∘ realSubmoduleBasis K b) =
      ((submoduleBasisMatrix e K b).map (Rat.castHom ℝ)).col := by
    funext j
    exact realSubmoduleBasis_matrix_coordinates e K b j
  have hs := congrArg (fun U : Submodule ℝ (K.baseChange ℝ) => U.map f)
    (realSubmoduleBasis K b).span_eq
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, he] at hs
  exact hs.trans (by simp only [f, LinearMap.range_comp, Submodule.range_subtype])

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {B I : Type*} [Fintype B]
  (U : Submodule ℚ (B → ℚ)) (b : Basis I ℚ U)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_rational_lift_matrix_data
    {σ : Type*} [Fintype σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R : ℝ) (a : ℕ) (ha : a ≤ m) (Tmin C : ℝ)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i) (hlarge : C * (l : ℝ) ^ m < Tmin) :
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let L := latticeKernel (shortVectorLattice Λ R) π
    let k := Module.finrank ℝ V
    ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
      ∃ b : Module.Basis (Fin k) ℤ L, ∃ B : Matrix (Fin m) (Fin k) ℝ,
        ∃ p : Fin k → Fin a,
          (∀ j, B.col j ∈ realDenominatorGrid l) ∧
          (∀ j, (b j).val.val.val = euclideanVerticalMap scale hs0 A (B.col j)) ∧
          (B.submatrix (Fin.castLE ha ∘ p) id).det ≠ 0 ∧
          ∃ D : ℕ, 0 < D ∧ D ≤ Nat.ceil (C * (l : ℝ) ^ k) ∧
            ∃ Q : Matrix (Fin m) (Fin k) ℚ,
              (∀ j, Q.col j ∈ denominatorGrid D) ∧
              Q.map (Rat.castHom ℝ) = B * (B.submatrix (Fin.castLE ha ∘ p) id)⁻¹ ∧
              Q.submatrix (Fin.castLE ha ∘ p) id = 1 ∧
              (∀ i j, RationalHeightLE (Q (Fin.castLE ha i) j)
                (Nat.ceil (C * (l : ℝ) ^ k))) := by
  let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
  let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  dsimp only
  intro hupper
  let : IsZLattice ℝ L := euclideanDerivative_vertical_lattice_full T hT scale hs0 Y A l hl R
  obtain ⟨b, B, _, hgrid, hrep, p, _, hdet⟩ := euclideanDerivative_horizontal_basis_data
    T hT scale hscale Y A hA hdiag l hl R a ha Tmin C hfar hlarge hupper
  refine ⟨b, B, p, hgrid, hrep, hdet, ?_⟩
  apply exists_partially_bounded_grid_normalization B l hl hgrid (Fin.castLE ha) p hdet C
  let f : V →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ Fin m) := Z.subtypeₗᵢ.comp V.subtypeₗᵢ
  let e : Fin a → σ ⊕ Fin m := fun i => Sum.inr (Fin.castLE ha i)
  have he : Function.Injective e := by
    intro i j hij
    have h : Fin.castLE ha i = Fin.castLE ha j := Sum.inr.inj hij
    exact Fin.ext (congrArg (fun u : Fin m => u.val) h)
  let H := B.submatrix (Fin.castLE ha) id
  have hH (i j) : H i j = f (b j).val (e i) := by
    change B (Fin.castLE ha i) j = (b j).val.val.val (Sum.inr (Fin.castLE ha i))
    rw [hrep]
    exact (euclideanVerticalMap_horizontal scale hs0 hscalehor A hA hblock (B.col j)
      (Fin.castLE ha i) i.isLt).symm
  intro q
  exact (lattice_projection_all_minors_bound L b f e he H hH q).trans hupper

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module

variable {m : ℕ} {J : Fin m → Type*}

end Erdos3.VectorPolynomial

end

end OAI

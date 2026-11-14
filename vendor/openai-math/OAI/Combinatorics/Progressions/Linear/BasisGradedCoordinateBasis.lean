/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/BasisGradedCoordinateBasis.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Projection
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def supportedSubmoduleBasis (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
    (hP : P = Submodule.span K (b '' S)) : Basis S K P := by
  let c := Basis.span (b.linearIndependent.comp (fun i : S => (i : ι)) Subtype.val_injective)
  have he : Submodule.span K (Set.range (fun i : S => b i)) = P := by
    rw [hP]
    congr 1
    ext x
    simp
  exact c.map (LinearEquiv.ofEq _ _ he)

@[simp] theorem supportedSubmoduleBasis_coe (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
    (hP : P = Submodule.span K (b '' S)) (i : S) :
    (supportedSubmoduleBasis b P S hP i : V) = b i := by
  simp [supportedSubmoduleBasis, Basis.map_apply]

theorem supportedSubmoduleBasis_repr (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
    (hP : P = Submodule.span K (b '' S)) (x : P) (i : S) :
    (supportedSubmoduleBasis b P S hP).repr x i = b.repr (x : V) i := by
  classical
  let c := supportedSubmoduleBasis b P S hP
  have he : c.coord i = (b.coord i).comp P.subtype := by
    apply c.ext
    intro j
    simp [c, Basis.coord_apply, Finsupp.single_apply, Subtype.ext_iff]
  change c.coord i x = b.coord i (x : V)
  rw [he]
  rfl

theorem basis_mem_span_image_iff (b : Basis ι K V) (S : Set ι) (x : V) :
    x ∈ Submodule.span K (b '' S) ↔ ∀ i, i ∉ S → b.repr x i = 0 := by
  classical
  rw [b.mem_span_image]
  constructor
  · intro h i hi
    by_contra hne
    exact hi (h (Finsupp.mem_support_iff.mpr hne))
  · intro h i hi
    by_contra hnot
    exact (Finsupp.mem_support_iff.mp hi) (h i hnot)

end Erdos3

end

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def basisCoordinateProjection (b : Basis ι K V) (S : Set ι) : V →ₗ[K] V := by
  classical
  exact
    { toFun := fun x => b.repr.symm ((b.repr x).filter (· ∈ S))
      map_add' := fun x y => by simp only [map_add, Finsupp.filter_add]
      map_smul' := fun c x => by simp only [map_smul, Finsupp.filter_smul, RingHom.id_apply] }

theorem basisCoordinateProjection_repr (b : Basis ι K V) (S : Set ι)
    [DecidablePred (· ∈ S)] (x : V) (i : ι) :
    b.repr (basisCoordinateProjection b S x) i = if i ∈ S then b.repr x i else 0 := by
  classical
  by_cases hi : i ∈ S <;>
    simp [basisCoordinateProjection, hi]

theorem basisCoordinateProjection_mem_span (b : Basis ι K V) (S : Set ι) (x : V) :
    basisCoordinateProjection b S x ∈ Submodule.span K (b '' S) := by
  classical
  apply (basis_mem_span_image_iff b S _).mpr
  intro i hi
  simp only [basisCoordinateProjection_repr, hi, ↓reduceIte]

theorem basisCoordinateProjection_eq_self (b : Basis ι K V) (S : Set ι) (x : V)
    (hx : x ∈ Submodule.span K (b '' S)) : basisCoordinateProjection b S x = x := by
  classical
  apply b.repr.injective
  ext i
  rw [basisCoordinateProjection_repr]
  split_ifs with hi
  · rfl
  · exact ((basis_mem_span_image_iff b S x).mp hx i hi).symm

theorem basisCoordinateProjection_basis (b : Basis ι K V) (S : Set ι)
    [DecidablePred (· ∈ S)] (i : ι) :
    basisCoordinateProjection b S (b i) = if i ∈ S then b i else 0 := by
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi]
    exact basisCoordinateProjection_eq_self b S (b i) (Submodule.subset_span ⟨i, hi, rfl⟩)
  · apply b.repr.injective
    ext j
    classical
    by_cases hj : j ∈ S <;> by_cases hij : i = j <;>
      simp_all [basisCoordinateProjection_repr]

theorem basisCoordinateProjection_idempotent (b : Basis ι K V) (S : Set ι) (x : V) :
    basisCoordinateProjection b S (basisCoordinateProjection b S x) = basisCoordinateProjection b S x :=
  basisCoordinateProjection_eq_self b S _ (basisCoordinateProjection_mem_span b S x)

theorem basisCoordinateProjection_eq_zero_iff (b : Basis ι K V) (S : Set ι) (x : V) :
    basisCoordinateProjection b S x = 0 ↔ x ∈ Submodule.span K (b '' Sᶜ) := by
  classical
  rw [basis_mem_span_image_iff]
  constructor
  · intro hx i hi
    have hiS : i ∈ S := by simpa only [Set.mem_compl_iff, not_not] using hi
    have h := congrArg (fun v => b.repr v i) hx
    simpa only [basisCoordinateProjection_repr, hiS, ↓reduceIte, map_zero, Finsupp.zero_apply] using h
  · intro hx
    apply b.repr.injective
    ext i
    simp only [basisCoordinateProjection_repr, map_zero, Finsupp.zero_apply]
    split_ifs with hi
    · exact hx i (by simpa only [Set.mem_compl_iff, not_not] using hi)
    · rfl

theorem sub_basisCoordinateProjection_mem (b : Basis ι K V) (S : Set ι) (x : V) :
    x - basisCoordinateProjection b S x ∈ Submodule.span K (b '' Sᶜ) := by
  apply (basisCoordinateProjection_eq_zero_iff b S _).mp
  rw [map_sub, basisCoordinateProjection_idempotent, sub_self]

theorem basisCoordinateProjection_eq_iff (b : Basis ι K V) (S : Set ι) (x y : V) :
    basisCoordinateProjection b S x = basisCoordinateProjection b S y ↔
      x - y ∈ Submodule.span K (b '' Sᶜ) := by
  rw [← basisCoordinateProjection_eq_zero_iff, map_sub, sub_eq_zero]

end Erdos3

end

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem basis_isCompl_span_compl (b : Basis ι K V) (S : Set ι) :
    IsCompl (Submodule.span K (b '' S)) (Submodule.span K (b '' Sᶜ)) := by
  apply b.linearIndependent.isCompl_span_image
  · exact b.span_eq
  · exact isCompl_compl

noncomputable def supportedQuotientBasis (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
    (hP : P = Submodule.span K (b '' S)) : Basis {i // i ∉ S} K (V ⧸ P) :=
  (supportedSubmoduleBasis b (Submodule.span K (b '' Sᶜ)) Sᶜ rfl).map
    (P.quotientEquivOfIsCompl (Submodule.span K (b '' Sᶜ))
      (by rw [hP]; exact basis_isCompl_span_compl b S)).symm

@[simp] theorem supportedQuotientBasis_apply (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
    (hP : P = Submodule.span K (b '' S)) (i : {i // i ∉ S}) :
    supportedQuotientBasis b P S hP i = P.mkQ (b i) := by
  change P.mkQ ((supportedSubmoduleBasis b (Submodule.span K (b '' Sᶜ)) Sᶜ rfl) i : V) = _
  exact congrArg P.mkQ (supportedSubmoduleBasis_coe b (Submodule.span K (b '' Sᶜ)) Sᶜ rfl i)

theorem supportedQuotientBasis_repr_mk (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
    (hP : P = Submodule.span K (b '' S)) (x : V) (i : {i // i ∉ S}) :
    (supportedQuotientBasis b P S hP).repr (P.mkQ x) i = b.repr x i := by
  classical
  have hker : P ≤ LinearMap.ker (b.coord i) := by
    intro y hy
    rw [hP, basis_mem_span_image_iff] at hy
    exact hy i i.property
  let f := P.liftQ (b.coord i) hker
  have hf : (supportedQuotientBasis b P S hP).coord i = f := by
    apply (supportedQuotientBasis b P S hP).ext
    intro j
    change (supportedQuotientBasis b P S hP).repr (supportedQuotientBasis b P S hP j) i = _
    rw [Basis.repr_self]
    simp [f, Basis.coord_apply, Finsupp.single_apply, Subtype.ext_iff]
  change (supportedQuotientBasis b P S hP).coord i (P.mkQ x) = _
  rw [hf]
  rfl

theorem supportedQuotientBasis_map_span (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
    (hP : P = Submodule.span K (b '' S)) (T : Set ι) :
    (Submodule.span K (b '' T)).map P.mkQ = Submodule.span K
      (supportedQuotientBasis b P S hP '' {i : {i // i ∉ S} | (i : ι) ∈ T}) := by
  rw [Submodule.map_span, Set.image_image]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    by_cases hs : i ∈ S
    · have hz : P.mkQ (b i) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr (by
        rw [hP]
        exact Submodule.subset_span ⟨i, hs, rfl⟩)
      change P.mkQ (b i) ∈ _
      rw [hz]
      exact Submodule.zero_mem _
    · have h := Submodule.subset_span (R := K)
        (show supportedQuotientBasis b P S hP ⟨i, hs⟩ ∈
          supportedQuotientBasis b P S hP '' {j : {i // i ∉ S} | (j : ι) ∈ T} from
            ⟨⟨i, hs⟩, hi, rfl⟩)
      simpa only [supportedQuotientBasis_apply] using h
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    rw [supportedQuotientBasis_apply]
    exact Submodule.subset_span ⟨i.val, hi, rfl⟩

end Erdos3

end

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def basisGradeProjection (b : Basis ι K V) (w : ι → ℕ) (j : ℕ) : V →ₗ[K] V :=
  basisCoordinateProjection b {i | w i = j}

noncomputable def basisBelowProjection (b : Basis ι K V) (w : ι → ℕ) (j : ℕ) : V →ₗ[K] V :=
  basisCoordinateProjection b {i | w i < j}

@[simp] theorem basisGradeProjection_repr (b : Basis ι K V) (w : ι → ℕ) (j : ℕ) (x : V) (i : ι) :
    b.repr (basisGradeProjection b w j x) i = if w i = j then b.repr x i else 0 :=
  basisCoordinateProjection_repr b {i | w i = j} x i

@[simp] theorem basisBelowProjection_repr (b : Basis ι K V) (w : ι → ℕ) (j : ℕ) (x : V) (i : ι) :
    b.repr (basisBelowProjection b w j x) i = if w i < j then b.repr x i else 0 :=
  basisCoordinateProjection_repr b {i | w i < j} x i

theorem basisBelowProjection_eq_sum_grades (b : Basis ι K V) (w : ι → ℕ) (j : ℕ) (x : V) :
    basisBelowProjection b w j x = ∑ k ∈ Finset.range j, basisGradeProjection b w k x := by
  apply b.repr.injective
  ext i
  simp [basisBelowProjection_repr, basisGradeProjection_repr]

def BasisGradedSubmodule (b : Basis ι K V) (w : ι → ℕ) (U : Submodule K V) : Prop :=
  ∀ j x, x ∈ U → basisGradeProjection b w j x ∈ U

theorem BasisGradedSubmodule.below_mem (b : Basis ι K V) (w : ι → ℕ) (U : Submodule K V)
    (hU : BasisGradedSubmodule b w U) (j : ℕ) (x : V) (hx : x ∈ U) :
    basisBelowProjection b w j x ∈ U := by
  rw [basisBelowProjection_eq_sum_grades]
  exact Submodule.sum_mem U (fun k _ => hU k x hx)

theorem sub_basisBelowProjection_mem (b : Basis ι K V) (w : ι → ℕ) (j : ℕ) (x : V) :
    x - basisBelowProjection b w j x ∈ Submodule.span K (b '' {i | j ≤ w i}) := by
  simpa only [basisBelowProjection, Set.compl_ofPred, not_lt] using
    sub_basisCoordinateProjection_mem b {i | w i < j} x

theorem basisBelowProjection_eq_iff (b : Basis ι K V) (w : ι → ℕ) (j : ℕ) (x y : V) :
    basisBelowProjection b w j x = basisBelowProjection b w j y ↔
      x - y ∈ Submodule.span K (b '' {i | j ≤ w i}) := by
  simpa only [basisBelowProjection, Set.compl_ofPred, not_lt] using
    basisCoordinateProjection_eq_iff b {i | w i < j} x y

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

end Erdos3

end

end OAI

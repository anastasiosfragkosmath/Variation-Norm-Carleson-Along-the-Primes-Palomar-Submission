/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/ProperCyclicKernelBasis.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.Order.Round
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Order.Interval.Finset.Fin
public import OAI.Combinatorics.Progressions.Estimates.SaturatedFlag
public import OAI.Combinatorics.Progressions.Fourier.CyclicTorusCoordinates
public import OAI.Combinatorics.Progressions.Lattices.NaturalScaleIntegerWindow
public import OAI.Combinatorics.Progressions.Linear.MahlerBasis
@[expose] public section

namespace OAI

section

namespace Erdos3.IntegerBasisReduction.Mahler

open scoped BigOperators
open Module

def IsCenteredReduction {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (a : Fin n → Fin n → ℝ) : Prop :=
  ∀ i,
    integralEmbed (b i) = ∑ j, a i j • integralEmbed (x j) ∧
    (∀ j, i < j → a i j = 0) ∧
    ((|a i i| = 1 ∧ ∀ j, j < i → a i j = 0) ∨
      ∀ j, j ≤ i → |a i j| ≤ (1 : ℝ) / 2)

def IsRawFlagReduction {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
  (u : Fin n → Fin n → ℝ) : Prop :=
  (∀ i, integralEmbed (b i) = ∑ j, u i j • integralEmbed (x j)) ∧
  (∀ i j, i < j → u i j = 0) ∧
  (∀ i j, i < j → b.repr (x i) j = 0) ∧
  ∀ i, b.repr (x i) i ≠ 0 ∧
    ((b.repr (x i) i : ℝ) * u i i = 1)

theorem exists_rawFlagReduction_of_linearIndependent {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (hli : LinearIndependent ℝ (fun i ↦ integralEmbed (x i))) :
    ∃ (b : Basis (Fin n) ℤ (IntegralPoint n))
      (u : Fin n → Fin n → ℝ), IsRawFlagReduction x b u := by
  classical
  have hrealEmbed (z : IntegralPoint n) :
      SaturatedFlag.realEmbed n z = integralEmbed z := by
    ext j
    rfl
  have hli' : LinearIndependent ℝ
      (fun i ↦ SaturatedFlag.realEmbed n (x i)) := by
    simpa only [hrealEmbed] using hli
  obtain ⟨b, hprefix, hxrepr, hxdiag⟩ :=
    SaturatedFlag.exists_prefix_adapted_basis_realPrefixLattice x hli'
  let xb : Basis (Fin n) ℝ (Fin n → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank'
      (fun i ↦ integralEmbed (x i)) hli (by simp)
  let u : Fin n → Fin n → ℝ :=
    fun i j ↦ xb.repr (integralEmbed (b i)) j
  have hxb (i : Fin n) : xb i = integralEmbed (x i) := by
    simp [xb]
  have hexpand (i : Fin n) :
      integralEmbed (b i) = ∑ j, u i j • integralEmbed (x j) := by
    simpa only [hxb] using (xb.sum_repr (integralEmbed (b i))).symm
  have htri : ∀ i j, i < j → u i j = 0 := by
    intro i j hij
    have hbi : b i ∈ SaturatedFlag.realPrefixLattice x i := by
      rw [hprefix i]
      apply Submodule.subset_span
      exact ⟨i, Set.mem_Iic.mpr le_rfl, rfl⟩
    have hbispan : integralEmbed (b i) ∈
        Submodule.span ℝ (xb '' Set.Iic i) := by
      have hm := SaturatedFlag.mem_realPrefixLattice.mp hbi
      have himage : SaturatedFlag.realEmbed n '' (x '' Set.Iic i) =
          xb '' Set.Iic i := by
        ext y
        constructor
        · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
          exact ⟨k, hk, (hxb k).trans (hrealEmbed (x k)).symm⟩
        · rintro ⟨k, hk, rfl⟩
          exact ⟨x k, ⟨k, hk, rfl⟩,
            (hrealEmbed (x k)).trans (hxb k).symm⟩
      rw [himage] at hm
      rw [hrealEmbed] at hm
      exact hm
    have hsupp := xb.repr_support_subset_of_mem_span (Set.Iic i) hbispan
    by_contra hne
    have hjmem : j ∈ Set.Iic i :=
      hsupp (Finsupp.mem_support_iff.mpr hne)
    exact (not_le_of_gt hij) (Set.mem_Iic.mp hjmem)
  refine ⟨b, u, hexpand, htri, hxrepr, ?_⟩
  intro i
  have hxreal :
      ∑ j, (b.repr (x i) j : ℝ) • integralEmbed (b j) =
        integralEmbed (x i) := by
    calc
      (∑ j, (b.repr (x i) j : ℝ) • integralEmbed (b j)) =
          integralEmbed (∑ j, b.repr (x i) j • b j) := by
        ext k
        simp [integralEmbed]
      _ = integralEmbed (x i) := congrArg integralEmbed (b.sum_repr (x i))
  have hcoord := congrArg (fun y : Fin n → ℝ ↦ xb.repr y i) hxreal
  have hrhs : xb.repr (integralEmbed (x i)) i = 1 := by
    rw [← hxb]
    simp
  rw [hrhs] at hcoord
  have hcoord' :
      ∑ j, (b.repr (x i) j : ℝ) * u j i = 1 := by
    simpa [u, hxb] using hcoord
  have hsingle :
      (∑ j, (b.repr (x i) j : ℝ) * u j i) =
        (b.repr (x i) i : ℝ) * u i i := by
    apply Finset.sum_eq_single i
    · intro j _hj hji
      rcases lt_or_gt_of_ne hji with hji | hij
      · rw [htri j i hji]
        simp
      · rw [hxrepr i j hij]
        simp
    · simp
  have hrecip : (b.repr (x i) i : ℝ) * u i i = 1 := by
    rw [← hsingle]
    exact hcoord'
  exact ⟨hxdiag i, hrecip⟩

theorem rawFlagReduction_diag_abs_le_one {n : ℕ}
    {x : Fin n → IntegralPoint n}
    {b : Basis (Fin n) ℤ (IntegralPoint n)}
    {u : Fin n → Fin n → ℝ}
    (hraw : IsRawFlagReduction x b u) (i : Fin n) :
    |u i i| ≤ 1 := by
  have hcne := (hraw.2.2.2 i).1
  have hrecip := (hraw.2.2.2 i).2
  have hcabsZ : (1 : ℤ) ≤ |b.repr (x i) i| := by
    have hpos : (0 : ℤ) < |b.repr (x i) i| := abs_pos.mpr hcne
    omega
  have hcabs : (1 : ℝ) ≤ |(b.repr (x i) i : ℝ)| := by
    exact_mod_cast hcabsZ
  have habsprod : |(b.repr (x i) i : ℝ)| * |u i i| = 1 := by
    rw [← abs_mul, hrecip, abs_one]
  nlinarith [abs_nonneg (u i i)]

theorem rawFlagReduction_diag_abs_le_half_of_not_unit {n : ℕ}
    {x : Fin n → IntegralPoint n}
    {b : Basis (Fin n) ℤ (IntegralPoint n)}
    {u : Fin n → Fin n → ℝ}
    (hraw : IsRawFlagReduction x b u) (i : Fin n)
    (hnot : |b.repr (x i) i| ≠ 1) :
    |u i i| ≤ (1 : ℝ) / 2 := by
  have hcne := (hraw.2.2.2 i).1
  have hrecip := (hraw.2.2.2 i).2
  have hcabsZ : (2 : ℤ) ≤ |b.repr (x i) i| := by
    have hpos : (0 : ℤ) < |b.repr (x i) i| := abs_pos.mpr hcne
    omega
  have hcabs : (2 : ℝ) ≤ |(b.repr (x i) i : ℝ)| := by
    exact_mod_cast hcabsZ
  have habsprod : |(b.repr (x i) i : ℝ)| * |u i i| = 1 := by
    rw [← abs_mul, hrecip, abs_one]
  nlinarith [abs_nonneg (u i i)]

def prefixIndex {n : ℕ} (i : Fin n) (j : Fin i.val) : Fin n :=
  ⟨j.val, lt_trans j.isLt i.isLt⟩

@[simp] theorem prefixIndex_val {n : ℕ} (i : Fin n) (j : Fin i.val) :
    (prefixIndex i j).val = j.val := rfl

theorem prefixIndex_lt {n : ℕ} (i : Fin n) (j : Fin i.val) :
    prefixIndex i j < i := j.isLt

noncomputable def centeredStep {n : ℕ} (r u : Fin n → ℝ) (j : Fin n) :
    Fin n → ℝ :=
  fun h ↦ r h - (round (r j / u j) : ℝ) * u h

theorem abs_centeredStep_apply_self_le {n : ℕ}
    (r u : Fin n → ℝ) (j : Fin n)
    (hdiag_ne : u j ≠ 0) (hdiag_le : |u j| ≤ 1) :
    |centeredStep r u j j| ≤ (1 : ℝ) / 2 := by
  have heq : centeredStep r u j j =
      u j * (r j / u j - (round (r j / u j) : ℝ)) := by
    rw [centeredStep]
    field_simp
  rw [heq, abs_mul]
  calc
    |u j| * |r j / u j - (round (r j / u j) : ℝ)| ≤
        1 * ((1 : ℝ) / 2) :=
      mul_le_mul hdiag_le (abs_sub_round (r j / u j))
        (abs_nonneg _) (by positivity)
    _ = (1 : ℝ) / 2 := one_mul _

theorem exists_integerCombination_abs_le_half : ∀ {n : ℕ}
    (u : Fin n → Fin n → ℝ),
    (∀ j h, j < h → u j h = 0) →
    (∀ j, u j j ≠ 0) →
    (∀ j, |u j j| ≤ (1 : ℝ)) →
    ∀ r : Fin n → ℝ,
      ∃ t : Fin n → ℤ,
        ∀ h, |r h + ∑ j, (t j : ℝ) * u j h| ≤ (1 : ℝ) / 2 := by
  intro n
  induction n with
  | zero =>
      intro u _htri _hne _hle r
      refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
      intro h
      exact Fin.elim0 h
  | succ n ih =>
      intro u htri hne hle r
      let last : Fin (n + 1) := Fin.last n
      let q : ℤ := -round (r last / u last last)
      let rHead : Fin n → ℝ := fun h ↦
        r h.castSucc + (q : ℝ) * u last h.castSucc
      let uHead : Fin n → Fin n → ℝ := fun j h ↦
        u j.castSucc h.castSucc
      have htriHead : ∀ j h, j < h → uHead j h = 0 := by
        intro j h hjh
        exact htri j.castSucc h.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hjh)
      have hneHead : ∀ j, uHead j j ≠ 0 := fun j ↦ hne j.castSucc
      have hleHead : ∀ j, |uHead j j| ≤ (1 : ℝ) := fun j ↦ hle j.castSucc
      obtain ⟨tHead, htHead⟩ := ih uHead htriHead hneHead hleHead rHead
      let t : Fin (n + 1) → ℤ := Fin.lastCases q tHead
      refine ⟨t, ?_⟩
      intro h
      refine Fin.lastCases ?_ (fun h ↦ ?_) h
      · have hzero :
            ∑ j : Fin n, (t j.castSucc : ℝ) * u j.castSucc last = 0 := by
          apply Finset.sum_eq_zero
          intro j _hj
          rw [htri j.castSucc last (Fin.castSucc_lt_last j)]
          simp
        rw [Fin.sum_univ_castSucc, hzero, zero_add]
        have hstep := abs_centeredStep_apply_self_le
          r (u last) last (hne last) (hle last)
        simpa [t, q, last, centeredStep, sub_eq_add_neg] using hstep
      · have hh := htHead h
        simpa [Fin.sum_univ_castSucc, t, rHead, uHead, q,
          add_assoc, add_comm, add_left_comm] using hh

theorem exists_prefix_integerCombination_abs_le_half {n : ℕ}
    (u : Fin n → Fin n → ℝ)
    (htri : ∀ j h, j < h → u j h = 0)
    (hne : ∀ j, u j j ≠ 0)
    (hle : ∀ j, |u j j| ≤ (1 : ℝ))
    (r : Fin n → ℝ) (i : Fin n) :
    ∃ t : Fin i.val → ℤ, ∀ h : Fin i.val,
      |r (prefixIndex i h) +
        ∑ j, (t j : ℝ) * u (prefixIndex i j) (prefixIndex i h)| ≤
          (1 : ℝ) / 2 := by
  let up : Fin i.val → Fin i.val → ℝ :=
    fun j h ↦ u (prefixIndex i j) (prefixIndex i h)
  have htrip : ∀ j h, j < h → up j h = 0 := by
    intro j h hjh
    exact htri (prefixIndex i j) (prefixIndex i h) hjh
  have hnep : ∀ j, up j j ≠ 0 := fun j ↦ hne (prefixIndex i j)
  have hlep : ∀ j, |up j j| ≤ (1 : ℝ) := fun j ↦ hle (prefixIndex i j)
  simpa [up] using exists_integerCombination_abs_le_half up htrip hnep hlep
    (fun h ↦ r (prefixIndex i h))

noncomputable def basisOfUpperTriangularUnits {n : ℕ} {M : Type*}
    [AddCommGroup M] (b : Basis (Fin n) ℤ M)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hupper : A.IsUpperTriangular) (hdiag : ∀ i, IsUnit (A i i)) :
    Basis (Fin n) ℤ M := by
  have hdet : IsUnit A.det := by
    rw [Matrix.det_of_isUpperTriangular hupper]
    exact IsUnit.prod_univ_iff.mpr hdiag
  exact b.map (A.toLinearEquiv b hdet)

theorem basisOfUpperTriangularUnits_apply {n : ℕ} {M : Type*}
    [AddCommGroup M] (b : Basis (Fin n) ℤ M)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hupper : A.IsUpperTriangular) (hdiag : ∀ i, IsUnit (A i i))
    (i : Fin n) :
    basisOfUpperTriangularUnits b A hupper hdiag i = ∑ j, A j i • b j := by
  simp [basisOfUpperTriangularUnits, Matrix.toLinearEquiv_apply,
    Matrix.toLin_self]

def extendPrefix {n : ℕ} (i : Fin n) (t : Fin i.val → ℤ) : Fin n → ℤ :=
  fun j ↦ if h : j < i then t ⟨j.val, h⟩ else 0

@[simp]
theorem extendPrefix_prefixIndex {n : ℕ} (i : Fin n)
    (t : Fin i.val → ℤ) (j : Fin i.val) :
    extendPrefix i t (prefixIndex i j) = t j := by
  simp [extendPrefix, prefixIndex_lt]

def prefixIndexEquivIio {n : ℕ} (i : Fin n) :
    Fin i.val ≃ {j : Fin n // j ∈ Finset.Iio i} where
  toFun j := ⟨prefixIndex i j, Finset.mem_Iio.mpr (prefixIndex_lt i j)⟩
  invFun j :=
    { val := j.1.val
      isLt := by
        have hji : j.1 < i := Finset.mem_Iio.mp j.2
        exact hji }
  left_inv j := by ext; rfl
  right_inv j := by ext; rfl

theorem sum_extendPrefix_mul {n : ℕ} (i : Fin n) (t : Fin i.val → ℤ)
    (f : Fin n → ℝ) :
    (∑ j, (extendPrefix i t j : ℝ) * f j) =
      ∑ j : Fin i.val, (t j : ℝ) * f (prefixIndex i j) := by
  classical
  calc
    (∑ j, (extendPrefix i t j : ℝ) * f j) =
        ∑ j ∈ Finset.Iio i, (extendPrefix i t j : ℝ) * f j := by
      symm
      apply Finset.sum_subset (by intro j hj; simp)
      intro j _hj hjnot
      have hnlt : ¬j < i := by simpa using hjnot
      simp [extendPrefix, hnlt]
    _ = ∑ j : {j : Fin n // j ∈ Finset.Iio i},
          (extendPrefix i t j : ℝ) * f j := by
      rw [← Finset.sum_attach]
      simp
    _ = ∑ j : Fin i.val, (t j : ℝ) * f (prefixIndex i j) := by
      symm
      refine Fintype.sum_equiv (prefixIndexEquivIio i) _ _ ?_
      intro j
      simp [prefixIndexEquivIio]

noncomputable def centeredReductionMatrix {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (t : (i : Fin n) → Fin i.val → ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  fun j i ↦
    if |b.repr (x i) i| = 1 then
      b.repr (x i) i * b.repr (x i) j
    else if j = i then 1 else extendPrefix i (t i) j

theorem centeredReductionMatrix_isUpperTriangular {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (t : (i : Fin n) → Fin i.val → ℤ)
    (hupper : ∀ i j, i < j → b.repr (x i) j = 0) :
    (centeredReductionMatrix x b t).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  change centeredReductionMatrix x b t i j = 0
  by_cases hunit : |b.repr (x j) j| = 1
  · simp [centeredReductionMatrix, hunit, hupper j i hji]
  · have hne : i ≠ j := hji.ne'
    have hnlt : ¬i < j := hji.asymm
    simp [centeredReductionMatrix, hunit, hne, extendPrefix, hnlt]

@[simp]
theorem centeredReductionMatrix_apply_self {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (t : (i : Fin n) → Fin i.val → ℤ) (i : Fin n) :
    centeredReductionMatrix x b t i i = 1 := by
  by_cases hunit : |b.repr (x i) i| = 1
  · have hsquare : b.repr (x i) i * b.repr (x i) i = 1 := by
      by_cases hnonneg : 0 ≤ b.repr (x i) i
      · rw [abs_of_nonneg hnonneg] at hunit
        simp [hunit]
      · have hnonpos : b.repr (x i) i ≤ 0 := le_of_not_ge hnonneg
        rw [abs_of_nonpos hnonpos] at hunit
        have hminus : b.repr (x i) i = -1 := by omega
        simp [hminus]
    simp [centeredReductionMatrix, hunit, hsquare]
  · simp [centeredReductionMatrix, hunit]

theorem centeredReductionMatrix_isUnit_diagonal {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (t : (i : Fin n) → Fin i.val → ℤ) :
    ∀ i, IsUnit (centeredReductionMatrix x b t i i) := by
  intro i
  rw [centeredReductionMatrix_apply_self]
  exact isUnit_one

theorem exists_centeredReduction_of_rawFlagReduction {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (hli : LinearIndependent ℝ (fun i ↦ integralEmbed (x i)))
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (u : Fin n → Fin n → ℝ)
    (hraw : IsRawFlagReduction x b u) :
    ∃ (e : Basis (Fin n) ℤ (IntegralPoint n))
      (a : Fin n → Fin n → ℝ), IsCenteredReduction x e a := by
  classical
  have hudiag_ne : ∀ i, u i i ≠ 0 := by
    intro i hui
    have hrecip := (hraw.2.2.2 i).2
    rw [hui] at hrecip
    norm_num at hrecip
  have hudiag_le : ∀ i, |u i i| ≤ (1 : ℝ) :=
    fun i ↦ rawFlagReduction_diag_abs_le_one hraw i
  have hround : ∀ i, ∃ t : Fin i.val → ℤ, ∀ h : Fin i.val,
      |u i (prefixIndex i h) +
        ∑ j, (t j : ℝ) * u (prefixIndex i j) (prefixIndex i h)| ≤
          (1 : ℝ) / 2 := by
    intro i
    exact exists_prefix_integerCombination_abs_le_half u hraw.2.1
      hudiag_ne hudiag_le (u i) i
  choose t ht using hround
  let A : Matrix (Fin n) (Fin n) ℤ := centeredReductionMatrix x b t
  have hAupper : A.IsUpperTriangular :=
    centeredReductionMatrix_isUpperTriangular x b t hraw.2.2.1
  have hAdiag : ∀ i, IsUnit (A i i) :=
    centeredReductionMatrix_isUnit_diagonal x b t
  let e : Basis (Fin n) ℤ (IntegralPoint n) :=
    basisOfUpperTriangularUnits b A hAupper hAdiag
  let xb : Basis (Fin n) ℝ (Fin n → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank'
      (fun i ↦ integralEmbed (x i)) hli (by simp)
  have hxb (i : Fin n) : xb i = integralEmbed (x i) := by
    simp [xb]
  let a : Fin n → Fin n → ℝ :=
    fun i h ↦ xb.repr (integralEmbed (e i)) h
  have hurepr (j h : Fin n) :
      xb.repr (integralEmbed (b j)) h = u j h := by
    rw [hraw.1 j]
    simp_rw [← hxb]
    simp [Finsupp.single_apply]
  have he_apply (i : Fin n) : e i = ∑ j, A j i • b j :=
    basisOfUpperTriangularUnits_apply b A hAupper hAdiag i
  have hembed (i : Fin n) :
      integralEmbed (e i) = ∑ j, (A j i : ℝ) • integralEmbed (b j) := by
    rw [he_apply]
    ext k
    simp [integralEmbed]
  have haformula (i h : Fin n) :
      a i h = ∑ j, (A j i : ℝ) * u j h := by
    change xb.repr (integralEmbed (e i)) h = _
    rw [hembed]
    simp [hurepr]
  have hexpand (i : Fin n) :
      integralEmbed (e i) = ∑ j, a i j • integralEmbed (x j) := by
    simpa only [hxb] using (xb.sum_repr (integralEmbed (e i))).symm
  refine ⟨e, a, ?_⟩
  intro i
  refine ⟨hexpand i, ?_⟩
  by_cases hunit : |b.repr (x i) i| = 1
  · have heprim : e i = b.repr (x i) i • x i := by
      rw [he_apply]
      simp only [A, centeredReductionMatrix, hunit, ite_true]
      simp_rw [mul_smul]
      rw [← Finset.smul_sum, b.sum_repr]
    have hembedprim : integralEmbed (e i) =
        (b.repr (x i) i : ℝ) • xb i := by
      rw [heprim]
      ext k
      simp [integralEmbed, hxb]
    have haprim (h : Fin n) : a i h =
        (b.repr (x i) i : ℝ) * (if i = h then 1 else 0) := by
      change xb.repr (integralEmbed (e i)) h = _
      rw [hembedprim]
      simp [Finsupp.single_apply]
    have habove : ∀ j, i < j → a i j = 0 := by
      intro j hij
      rw [haprim]
      simp [hij.ne]
    refine ⟨habove, Or.inl ⟨?_, ?_⟩⟩
    · rw [haprim]
      have hcabs : |(b.repr (x i) i : ℝ)| = 1 := by
        exact_mod_cast hunit
      simpa using hcabs
    · intro j hji
      rw [haprim]
      simp [hji.ne']
  · have hainon (h : Fin n) : a i h =
        u i h + ∑ j : Fin i.val,
          (t i j : ℝ) * u (prefixIndex i j) h := by
      rw [haformula]
      calc
        (∑ j, (A j i : ℝ) * u j h) =
            ∑ j, ((if j = i then 1 else 0) +
              (extendPrefix i (t i) j : ℤ) : ℤ) * u j h := by
          apply Finset.sum_congr rfl
          intro j _hj
          by_cases hji : j = i
          · subst j
            simp [A, extendPrefix]
          · simp [A, centeredReductionMatrix, hunit, hji]
        _ = u i h + ∑ j, (extendPrefix i (t i) j : ℝ) * u j h := by
          simp_rw [Int.cast_add, add_mul]
          rw [Finset.sum_add_distrib]
          simp
        _ = u i h + ∑ j : Fin i.val,
              (t i j : ℝ) * u (prefixIndex i j) h := by
          rw [sum_extendPrefix_mul]
    have habove : ∀ h, i < h → a i h = 0 := by
      intro h hih
      rw [hainon, hraw.2.1 i h hih]
      have hsum : (∑ j : Fin i.val,
          (t i j : ℝ) * u (prefixIndex i j) h) = 0 := by
        apply Finset.sum_eq_zero
        intro j _hj
        rw [hraw.2.1 (prefixIndex i j) h
          (lt_trans (prefixIndex_lt i j) hih)]
        simp
      rw [hsum, add_zero]
    refine ⟨habove, Or.inr ?_⟩
    intro h hhi
    rcases lt_or_eq_of_le hhi with hlt | heq
    · let h' : Fin i.val := ⟨h.val, hlt⟩
      have hp : prefixIndex i h' = h := by
        apply Fin.ext
        rfl
      rw [hainon]
      simpa only [hp] using ht i h'
    · subst h
      rw [hainon]
      have hsum : (∑ j : Fin i.val,
          (t i j : ℝ) * u (prefixIndex i j) i) = 0 := by
        apply Finset.sum_eq_zero
        intro j _hj
        rw [hraw.2.1 (prefixIndex i j) i (prefixIndex_lt i j)]
        simp
      rw [hsum, add_zero]
      exact rawFlagReduction_diag_abs_le_half_of_not_unit hraw i hunit

theorem exists_centeredReduction_of_linearIndependent {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (hli : LinearIndependent ℝ (fun i ↦ integralEmbed (x i))) :
    ∃ (b : Basis (Fin n) ℤ (IntegralPoint n))
      (a : Fin n → Fin n → ℝ), IsCenteredReduction x b a := by
  obtain ⟨b, u, hraw⟩ := exists_rawFlagReduction_of_linearIndependent x hli
  exact exists_centeredReduction_of_rawFlagReduction x hli b u hraw

end Erdos3.IntegerBasisReduction.Mahler

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem IntegerBasisReduction.Mahler.IsCenteredReduction.abs_coefficient_le_one
    {n : ℕ} {x : Fin n → IntegerBasisReduction.Mahler.IntegralPoint n}
    {b : Basis (Fin n) ℤ (IntegerBasisReduction.Mahler.IntegralPoint n)}
    {a : Fin n → Fin n → ℝ}
    (h : IntegerBasisReduction.Mahler.IsCenteredReduction x b a) (i j : Fin n) :
    |a i j| ≤ 1 := by
  obtain ⟨_, habove, hprim | hhalf⟩ := h i
  · rcases lt_trichotomy j i with hlt | rfl | hgt
    · simp [hprim.2 j hlt]
    · exact hprim.1.le
    · simp [habove j hgt]
  · rcases le_or_gt j i with hle | hgt
    · exact (hhalf j hle).trans (by norm_num)
    · simp [habove j hgt]

theorem exists_lattice_basis_bounded_expansion
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {n : ℕ} (b₀ : Basis (Fin n) ℤ Λ) (v : Fin n → E)
    (hv : ∀ i, v i ∈ Λ) (hli : LinearIndependent ℝ v) :
    ∃ (b : Basis (Fin n) ℤ Λ) (a : Fin n → Fin n → ℝ),
      (∀ i j, |a i j| ≤ 1) ∧ ∀ i, (b i : E) = ∑ j, a i j • v j := by
  classical
  let B := (b₀.ofZLatticeBasis ℝ Λ).equivFun
  let w : Fin n → Λ := fun i => ⟨v i, hv i⟩
  let x : Fin n → IntegerBasisReduction.Mahler.IntegralPoint n := fun i => b₀.equivFun (w i)
  have hcoord (i) : IntegerBasisReduction.Mahler.integralEmbed (x i) = B (v i) := by
    ext j
    change (b₀.repr (w i) j : ℝ) = (b₀.ofZLatticeBasis ℝ Λ).repr (w i : E) j
    rw [Basis.ofZLatticeBasis_repr_apply]
  have hxi : LinearIndependent ℝ (fun i => IntegerBasisReduction.Mahler.integralEmbed (x i)) := by
    simpa only [hcoord, Function.comp_def, LinearEquiv.coe_coe] using
      hli.map_injOn B.toLinearMap B.injective.injOn
  obtain ⟨c, a, hred⟩ := IntegerBasisReduction.Mahler.exists_centeredReduction_of_linearIndependent x hxi
  let b := c.map b₀.equivFun.symm
  have hcast (z : Fin n → ℤ) :
      B.symm (IntegerBasisReduction.Mahler.integralEmbed z) = (b₀.equivFun.symm z : E) := by
    apply B.injective
    ext j
    rw [LinearEquiv.apply_symm_apply]
    change (z j : ℝ) = (b₀.ofZLatticeBasis ℝ Λ).repr (b₀.equivFun.symm z : E) j
    rw [Basis.ofZLatticeBasis_repr_apply]
    exact (congrArg (fun q : ℤ => (q : ℝ))
      (congrFun (b₀.equivFun.apply_symm_apply z) j)).symm
  refine ⟨b, a, hred.abs_coefficient_le_one, ?_⟩
  intro i
  have h := congrArg B.symm (hred i).1
  rw [map_sum] at h
  simp only [map_smul, hcoord, LinearEquiv.symm_apply_apply] at h
  rw [hcast] at h
  exact h

theorem exists_lattice_basis_coordinate_bound
    {ι : Type} [Fintype ι] (Λ : Submodule ℤ (ι → ℝ))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {n : ℕ} (b₀ : Basis (Fin n) ℤ Λ) (v : Fin n → ι → ℝ)
    (hv : ∀ i, v i ∈ Λ) (hli : LinearIndependent ℝ v)
    (R : ι → ℝ) (hbound : ∀ i j, |v i j| ≤ R j) :
    ∃ b : Basis (Fin n) ℤ Λ, ∀ i j, |(b i : ι → ℝ) j| ≤ (n : ℝ) * R j := by
  obtain ⟨b, a, ha, he⟩ := exists_lattice_basis_bounded_expansion Λ b₀ v hv hli
  refine ⟨b, ?_⟩
  intro i j
  rw [he]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    |∑ k, a i k * v k j| ≤ ∑ k, |a i k * v k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, R j := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      have h := mul_le_mul_of_nonneg_right (ha i k) (abs_nonneg (v k j))
      have h' : |a i k| * |v k j| ≤ |v k j| := by simpa only [one_mul] using h
      exact h'.trans (hbound k j)
    _ = (n : ℝ) * R j := by simp

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem cyclicIntegerKernel_eq_zero_of_lt_radii
    {ι : Type} [Fintype ι] {N : ℕ} (η : (ι → ℤ) →+ ZMod N) (R : ι → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (y : ι → ℝ) (hy : y ∈ cyclicIntegerKernel η)
    (hsmall : ∀ i, |y i| < (R i : ℝ) + 1) : y = 0 := by
  obtain ⟨x, hx, rfl⟩ := hy
  change ∀ i, |(x i : ℝ)| < (R i : ℝ) + 1 at hsmall
  have hbound : ∀ i, |x i| ≤ (R i : ℤ) := by
    intro i
    have h : |x i| < (R i : ℤ) + 1 := by exact_mod_cast hsmall i
    omega
  have he : x = 0 := hinj hbound (by simp) (by simpa using hx)
  rw [he, map_zero]

theorem cyclicIntegerKernel_nonzero_large_coordinate
    {ι : Type} [Fintype ι] {N : ℕ} (η : (ι → ℤ) →+ ZMod N) (R : ι → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (y : ι → ℝ) (hy : y ∈ cyclicIntegerKernel η) (hne : y ≠ 0) :
    ∃ i, (R i : ℝ) + 1 ≤ |y i| := by
  by_contra! h
  exact hne (cyclicIntegerKernel_eq_zero_of_lt_radii η R hinj y hy h)

theorem affine_box_card_le_radius_product
    {ι G : Type} [Fintype ι] [AddCommGroup G]
    (η : (ι → ℤ) →+ G) (R : ι → ℕ) (h₀ : G) (J : Finset G)
    (hrep : ∀ h ∈ J, ∃ x : ι → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x) :
    (J.card : ℝ) ≤ (2 : ℝ) ^ Fintype.card ι * ∏ i, ((R i : ℝ) + 1) := by
  classical
  have hsub : J ⊆ (centeredIntegerBox R).image (fun x => h₀ + η x) := by
    intro h hh
    obtain ⟨x, hx, rfl⟩ := hrep h hh
    exact Finset.mem_image.mpr ⟨x, (mem_centeredIntegerBox R x).mpr hx, rfl⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  have hp : (centeredIntegerBox R).card ≤ 2 ^ Fintype.card ι * ∏ i, (R i + 1) := by
    rw [card_centeredIntegerBox]
    calc
      (∏ i, (2 * R i + 1)) ≤ ∏ i, (2 * (R i + 1)) := by
        gcongr with i
        omega
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  exact_mod_cast hc.trans hp

theorem cyclicIntegerKernel_normalized_covolume_le
    {ι : Type} [Fintype ι] {N : ℕ} [NeZero N]
    (η : (ι → ℤ) →+ ZMod N) (R : ι → ℕ) (h₀ : ZMod N) (J : Finset (ZMod N))
    (δ : ℝ) (hδ : 0 < δ) (hdense : δ * N ≤ (J.card : ℝ))
    (hrep : ∀ h ∈ J, ∃ x : ι → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x) :
    ZLattice.covolume (cyclicIntegerKernel η) * (∏ i, ((R i : ℝ) + 1))⁻¹ ≤
      (2 : ℝ) ^ Fintype.card ι / δ := by
  have hprod : 0 < ∏ i, ((R i : ℝ) + 1) := Finset.prod_pos (by intros; positivity)
  rw [← div_eq_mul_inv, div_le_div_iff₀ hprod hδ]
  have hcov := mul_le_mul_of_nonneg_left (cyclicIntegerKernel_covolume_le η) hδ.le
  have hc := affine_box_card_le_radius_product η R h₀ J hrep
  nlinarith

theorem exists_short_independent_cyclic_kernel_vectors
    {r N : ℕ} [NeZero N] (η : (Fin r → ℤ) →+ ZMod N) (R : Fin r → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N))
    (δ : ℝ) (hδ : 0 < δ) (hdense : δ * N ≤ (J.card : ℝ))
    (hrep : ∀ h ∈ J, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x) :
    ∃ v : Fin r → Fin r → ℝ, LinearIndependent ℝ v ∧
      (∀ i, v i ∈ cyclicIntegerKernel η) ∧
      ∀ i j, |v i j| ≤
        (BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r * 2 ^ r / δ) *
          ((R j : ℝ) + 1) := by
  classical
  let b : Basis (Fin r) ℤ (cyclicIntegerKernel η) :=
    (finiteLatticeBasis (cyclicIntegerKernel η)).reindex (finCongr (by simp))
  let B := b.ofZLatticeBasis ℝ (cyclicIntegerKernel η)
  have hB : Submodule.span ℤ (Set.range B) = cyclicIntegerKernel η :=
    b.ofZLatticeBasis_span ℝ _
  have hdet : |(Matrix.of B).det| = ZLattice.covolume (cyclicIntegerKernel η) := by
    have he : (B : Fin r → Fin r → ℝ) = fun i => (b i : Fin r → ℝ) :=
      funext (fun i => Basis.ofZLatticeBasis_apply ℝ (cyclicIntegerKernel η) b i)
    rw [he]
    exact (ZLattice.covolume_eq_det (cyclicIntegerKernel η) b).symm
  obtain ⟨C⟩ := BohrLattice.MinkowskiSecondBox.realBox_has_minkowskiSecondCertificate
    B (fun i => (R i : ℝ) + 1) (by intro i; positivity)
  have hmem (i) : C.point i ∈ cyclicIntegerKernel η := hB ▸ C.point_mem i
  have hpoint (i j) : |C.point i j| ≤ C.scale i * ((R j : ℝ) + 1) := by
    have h := C.mem_scaledBox i
    exact abs_le.mpr ⟨h.1 j, h.2 j⟩
  have hone (i) : 1 ≤ C.scale i := by
    obtain ⟨j, hj⟩ := cyclicIntegerKernel_nonzero_large_coordinate η R hinj
      (C.point i) (hmem i) (C.independent.ne_zero i)
    have hp : 0 < (R j : ℝ) + 1 := by positivity
    nlinarith [hpoint i j]
  have hbound : ∏ i, C.scale i ≤
      BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r * 2 ^ r / δ := by
    have hm : 0 ≤ BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r := by
      unfold BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant
      positivity
    have hc := mul_le_mul_of_nonneg_left
      (cyclicIntegerKernel_normalized_covolume_le η R h₀ J δ hδ hdense hrep) hm
    have he : ∏ i, C.scale i ≤
        BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r *
          (ZLattice.covolume (cyclicIntegerKernel η) * (∏ i, ((R i : ℝ) + 1))⁻¹) := by
      simpa only [hdet, mul_assoc] using C.product_le
    simpa only [Fintype.card_fin, mul_div_assoc] using he.trans hc
  refine ⟨C.point, C.independent, hmem, ?_⟩
  intro i j
  have hi : C.scale i ≤ ∏ k, C.scale k := by
    calc
      C.scale i ≤ C.scale i * ∏ k ∈ Finset.univ.erase i, C.scale k :=
        le_mul_of_one_le_right (C.scale_nonneg i) (Finset.one_le_prod₀ (fun k _ => hone k))
      _ = ∏ k, C.scale k := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  exact (hpoint i j).trans (mul_le_mul_of_nonneg_right (hi.trans hbound) (by positivity))

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem proper_cyclic_kernel_box_card_le_covolume
    {ι : Type} [Fintype ι] {N : ℕ} [NeZero N]
    (η : (ι → ℤ) →+ ZMod N) (R : ι → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)}) :
    ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤ ZLattice.covolume (cyclicIntegerKernel η) := by
  classical
  let f : {x // x ∈ centeredIntegerBox R} → η.range := fun x => η.rangeRestrict x.val
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact hinj ((mem_centeredIntegerBox R x.val).mp x.property)
      ((mem_centeredIntegerBox R y.val).mp y.property) (congrArg Subtype.val h)
  have hc := Nat.card_le_card_of_injective f hf
  have hcard : (centeredIntegerBox R).card ≤ Nat.card η.range := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hc
  rw [card_centeredIntegerBox] at hcard
  rw [cyclicIntegerKernel_covolume_eq_card_range]
  exact_mod_cast hcard

theorem proper_cyclic_kernel_covolume_lower_bound
    {ι : Type} [Fintype ι] {N : ℕ} [NeZero N]
    (η : (ι → ℤ) →+ ZMod N) (R : ι → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)}) :
    (∏ i, ((R i : ℝ) + 1)) ≤ ZLattice.covolume (cyclicIntegerKernel η) := by
  have hp : (∏ i, (R i + 1)) ≤ ∏ i, (2 * R i + 1) := by
    gcongr with i
    omega
  have hpR : (∏ i, ((R i : ℝ) + 1)) ≤ ((∏ i, (2 * R i + 1) : ℕ) : ℝ) := by
    exact_mod_cast hp
  exact hpR.trans (proper_cyclic_kernel_box_card_le_covolume η R hinj)

noncomputable def properCyclicKernelBasisBound (r : ℕ) (δ : ℝ) : ℝ :=
  (r : ℝ) * BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r * 2 ^ r / δ

theorem properCyclicKernelBasisBound_nonneg (r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ properCyclicKernelBasisBound r δ := by
  unfold properCyclicKernelBasisBound BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant
  positivity

theorem exists_proper_cyclic_kernel_basis
    {r N : ℕ} [NeZero N] (η : (Fin r → ℤ) →+ ZMod N) (R : Fin r → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N))
    (δ : ℝ) (hδ : 0 < δ) (hdense : δ * N ≤ (J.card : ℝ))
    (hrep : ∀ h ∈ J, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x) :
    ∃ b : Basis (Fin r) ℤ (cyclicIntegerKernel η), ∀ i j,
      |(b i : Fin r → ℝ) j| ≤ properCyclicKernelBasisBound r δ * ((R j : ℝ) + 1) := by
  classical
  obtain ⟨v, hli, hv, hbound⟩ :=
    exists_short_independent_cyclic_kernel_vectors η R hinj h₀ J δ hδ hdense hrep
  let b₀ : Basis (Fin r) ℤ (cyclicIntegerKernel η) :=
    (finiteLatticeBasis (cyclicIntegerKernel η)).reindex (finCongr (by simp))
  obtain ⟨b, hb⟩ := exists_lattice_basis_coordinate_bound (cyclicIntegerKernel η) b₀ v hv hli
    (fun j => (BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r * 2 ^ r / δ) *
      ((R j : ℝ) + 1)) hbound
  refine ⟨b, ?_⟩
  intro i j
  simpa only [properCyclicKernelBasisBound, mul_div_assoc, mul_assoc] using hb i j

theorem exists_proper_affine_torus_basis
    {r N : ℕ} [NeZero N] (η : (Fin r → ℤ) →+ ZMod N) (R : Fin r → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N))
    (δ : ℝ) (hδ : 0 < δ) (hdense : δ * N ≤ (J.card : ℝ))
    (hrep : ∀ h ∈ J, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x) :
    ∃ b : Basis (Fin r) ℤ (cyclicIntegerKernel η),
      (∀ i j, |(b i : Fin r → ℝ) j| ≤ properCyclicKernelBasisBound r δ * ((R j : ℝ) + 1)) ∧
      ∃ t : Fin r → ℝ, (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
        (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
        ∀ (h : ZMod N) (x : Fin r → ℤ), h = h₀ + η x → ∀ i,
          ((cyclicKernelRealCoordinates η b (integerVectorRealMap x) i : ℝ) :
            AddCircle (1 : ℝ)) =
              ((((h.val : ℝ) - h₀.val) * t i : ℝ) : AddCircle (1 : ℝ)) := by
  obtain ⟨b, hb⟩ := exists_proper_cyclic_kernel_basis η R hinj h₀ J δ hδ hdense hrep
  exact ⟨b, hb, exists_affine_cyclic_kernel_real_frequencies η b h₀⟩

end Erdos3

end

end OAI

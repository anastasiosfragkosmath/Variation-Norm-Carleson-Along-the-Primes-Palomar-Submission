/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/LieBCHContinuity.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Nilpotent.Exp
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import OAI.Combinatorics.Progressions.Estimates.FormalExpLog
public import OAI.Combinatorics.Progressions.Estimates.FreeLieTreeCoefficientBounds
@[expose] public section

namespace OAI

section

namespace Erdos3

open PowerSeries Finset

section Ring
variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

noncomputable def nilpotentSeries (f : PowerSeries ℚ) (a : A) : A :=
  ∑ i ∈ range (nilpotencyClass a), coeff i f • a ^ i

theorem nilpotentSeries_eq_sum (f : PowerSeries ℚ) {a : A} {k : ℕ} (h : a ^ k = 0) :
    nilpotentSeries f a = ∑ i ∈ range k, coeff i f • a ^ i := by
  unfold nilpotentSeries
  have hle : nilpotencyClass a ≤ k := csInf_le' h
  apply sum_subset (range_mono hle)
  intro i hi hnot
  rw [pow_eq_zero_of_le (Nat.le_of_not_gt (by simpa using hnot))
    (pow_nilpotencyClass ⟨k, h⟩), smul_zero]

theorem nilpotentSeries_eq_finsum (f : PowerSeries ℚ) {a : A} (ha : IsNilpotent a) :
    nilpotentSeries f a = ∑ᶠ i : ℕ, coeff i f • a ^ i := by
  symm
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra hn
  have he : a ^ i = 0 := pow_eq_zero_of_le
    (Nat.le_of_not_gt (by simpa using hn)) (pow_nilpotencyClass ha)
  exact hi (by simp [he])

theorem map_nilpotentSeries (f : PowerSeries ℚ) {a : A} (ha : IsNilpotent a)
    (φ : A →ₐ[ℚ] B) : φ (nilpotentSeries f a) = nilpotentSeries f (φ a) := by
  obtain ⟨k, hk⟩ := ha
  have hk' : (φ a) ^ k = 0 := by rw [← map_pow, hk, map_zero]
  simp [nilpotentSeries_eq_sum f hk, nilpotentSeries_eq_sum f hk']

theorem nilpotentSeries_exp (a : A) :
    nilpotentSeries (PowerSeries.exp ℚ) a = IsNilpotent.exp a := by
  simp [nilpotentSeries, IsNilpotent.exp, coeff_exp, one_div]

end Ring

section CommRing
variable {A : Type*} [CommRing A] [Algebra ℚ A]

omit [Algebra ℚ A] in
theorem hasSubst_C_nilpotent {a : A} (ha : IsNilpotent a) :
    HasSubst (C a : PowerSeries A) := by
  change IsNilpotent (constantCoeff (C a))
  simpa only [constantCoeff_C] using ha

theorem subst_C_nilpotent_eq (f : PowerSeries ℚ) {a : A} (ha : IsNilpotent a) :
    f.subst (C a : PowerSeries A) = C (nilpotentSeries f a) := by
  ext n
  rw [coeff_subst' (hasSubst_C_nilpotent ha)]
  simp only [← map_pow, coeff_C]
  cases n with
  | zero => simp only [ite_true, nilpotentSeries_eq_finsum f ha]
  | succ n => simp

noncomputable def nilpotentSeriesHom {a : A} (ha : IsNilpotent a) :
    PowerSeries ℚ →ₐ[ℚ] A :=
  constantCoeff.toRatAlgHom.comp (substAlgHom (hasSubst_C_nilpotent ha))

theorem nilpotentSeriesHom_apply {a : A} (ha : IsNilpotent a) (f : PowerSeries ℚ) :
    nilpotentSeriesHom ha f = nilpotentSeries f a := by
  simp only [nilpotentSeriesHom, AlgHom.comp_apply, RingHom.toRatAlgHom_apply,
    coe_substAlgHom, subst_C_nilpotent_eq f ha, constantCoeff_C]

theorem nilpotentSeries_X {a : A} (ha : IsNilpotent a) :
    nilpotentSeries X a = a := by
  have h := subst_X (R := ℚ) (hasSubst_C_nilpotent ha)
  rw [subst_C_nilpotent_eq _ ha] at h
  exact C_injective h

theorem isNilpotent_nilpotentSeries {a : A} (ha : IsNilpotent a)
    {g : PowerSeries ℚ} (hg : constantCoeff g = 0) :
    IsNilpotent (nilpotentSeries g a) := by
  have h := (HasSubst.of_constantCoeff_zero' hg).comp (hasSubst_C_nilpotent ha)
  change IsNilpotent (nilpotentSeriesHom ha g) at h
  rwa [nilpotentSeriesHom_apply] at h

theorem nilpotentSeries_subst {a : A} (ha : IsNilpotent a)
    (f : PowerSeries ℚ) {g : PowerSeries ℚ} (hg : constantCoeff g = 0) :
    nilpotentSeries (f.subst g) a = nilpotentSeries f (nilpotentSeries g a) := by
  have h := subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hg)
    (hasSubst_C_nilpotent ha) f
  rw [subst_C_nilpotent_eq _ ha, subst_C_nilpotent_eq _ ha,
    subst_C_nilpotent_eq _ (isNilpotent_nilpotentSeries ha hg)] at h
  exact C_injective h

end CommRing
end Erdos3

end

section

namespace Erdos3

open PowerSeries

section Ring
variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

noncomputable def nilpotentLog (a : A) : A := nilpotentSeries (log ℚ) a

theorem nilpotentLog_eq_sum {a : A} {k : ℕ} (h : a ^ k = 0) :
    nilpotentLog a = ∑ i ∈ Finset.range k, ((-1 : ℚ) ^ (i + 1) / i) • a ^ i := by
  rw [nilpotentLog, nilpotentSeries_eq_sum _ h]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hzero : i = 0
  · simp [hzero]
  · simp [coeff_log, hzero]

theorem nilpotentLog_zero : nilpotentLog (0 : A) = 0 := by
  simp [nilpotentLog_eq_sum (pow_one (0 : A))]

theorem map_nilpotentLog {a : A} (ha : IsNilpotent a) (φ : A →ₐ[ℚ] B) :
    φ (nilpotentLog a) = nilpotentLog (φ a) := map_nilpotentSeries _ ha φ

end Ring

section CommRing
variable {A : Type*} [CommRing A] [Algebra ℚ A]

theorem isNilpotent_nilpotentLog_comm {a : A} (ha : IsNilpotent a) :
    IsNilpotent (nilpotentLog a) := isNilpotent_nilpotentSeries ha constantCoeff_log

theorem exp_nilpotentLog_comm {a : A} (ha : IsNilpotent a) :
    IsNilpotent.exp (nilpotentLog a) = 1 + a := by
  have h := nilpotentSeries_subst ha (exp ℚ) (g := log ℚ) constantCoeff_log
  rw [formal_exp_log, ← nilpotentSeriesHom_apply ha, map_add, map_one,
    nilpotentSeriesHom_apply, nilpotentSeries_X ha, nilpotentSeries_exp] at h
  exact h.symm

theorem nilpotentLog_exp_sub_one_comm {a : A} (ha : IsNilpotent a) :
    nilpotentLog (IsNilpotent.exp a - 1) = a := by
  have h := nilpotentSeries_subst ha (log ℚ) (g := exp ℚ - 1)
    (by simp [constantCoeff_exp])
  rw [formal_log_exp, nilpotentSeries_X ha, ← nilpotentSeriesHom_apply ha,
    map_sub, map_one, nilpotentSeriesHom_apply, nilpotentSeries_exp] at h
  exact h.symm

end CommRing

section Ring
variable {A : Type*} [Ring A] [Algebra ℚ A]

theorem exp_nilpotentLog {a : A} (ha : IsNilpotent a) :
    IsNilpotent.exp (nilpotentLog a) = 1 + a := by
  let S := Algebra.adjoin ℚ ({a} : Set A)
  let x : S := ⟨a, Algebra.self_mem_adjoin_singleton ℚ a⟩
  have hx : IsNilpotent x :=
    (IsNilpotent.map_iff (f := S.val) Subtype.val_injective).mp ha
  have h := congrArg S.val (exp_nilpotentLog_comm hx)
  rw [IsNilpotent.map_exp (isNilpotent_nilpotentLog_comm hx),
    map_nilpotentLog hx, map_add, map_one] at h
  exact h

theorem nilpotentLog_exp_sub_one {a : A} (ha : IsNilpotent a) :
    nilpotentLog (IsNilpotent.exp a - 1) = a := by
  let S := Algebra.adjoin ℚ ({a} : Set A)
  let x : S := ⟨a, Algebra.self_mem_adjoin_singleton ℚ a⟩
  have hx : IsNilpotent x :=
    (IsNilpotent.map_iff (f := S.val) Subtype.val_injective).mp ha
  have h := congrArg S.val (nilpotentLog_exp_sub_one_comm hx)
  rw [map_nilpotentLog (IsNilpotent.isNilpotent_exp_sub_one hx), map_sub, map_one,
    IsNilpotent.map_exp hx] at h
  exact h

theorem exp_injective_on_nilpotents {a b : A} (ha : IsNilpotent a)
    (hb : IsNilpotent b) (h : IsNilpotent.exp a = IsNilpotent.exp b) : a = b := by
  rw [← nilpotentLog_exp_sub_one ha, ← nilpotentLog_exp_sub_one hb, h]

end Ring
end Erdos3

end

section

namespace Erdos3

open PowerSeries Finset

variable {A : Type*} [Ring A] [Algebra ℚ A]

theorem nonUnitalSubalgebra_pow_mem (I : NonUnitalSubalgebra ℚ A) {a : A}
    (ha : a ∈ I) {n : ℕ} (hn : 0 < n) : a ^ n ∈ I := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  clear hn
  induction n with
  | zero => simpa using ha
  | succ n ih =>
    rw [pow_succ]
    exact mul_mem ih ha

theorem nilpotentSeries_sub (f g : PowerSeries ℚ) (a : A) :
    nilpotentSeries (f - g) a = nilpotentSeries f a - nilpotentSeries g a := by
  simp [nilpotentSeries, sub_smul, sum_sub_distrib]

theorem nilpotentSeries_one {a : A} (ha : IsNilpotent a) :
    nilpotentSeries 1 a = 1 := by
  obtain ⟨k, hk⟩ := ha
  rw [nilpotentSeries_eq_sum _ (pow_eq_zero_of_le (Nat.le_succ k) hk)]
  simp [coeff_one]

theorem nilpotentSeries_mem (I : NonUnitalSubalgebra ℚ A) {a : A} (ha : a ∈ I)
    {f : PowerSeries ℚ} (hf : constantCoeff f = 0) : nilpotentSeries f a ∈ I := by
  apply I.sum_mem
  intro i hi
  by_cases hzero : i = 0
  · simp [hzero, coeff_zero_eq_constantCoeff, hf]
  · exact I.smul_mem _ (nonUnitalSubalgebra_pow_mem I ha (Nat.pos_of_ne_zero hzero))

theorem nilpotentLog_mem (I : NonUnitalSubalgebra ℚ A) {a : A} (ha : a ∈ I) :
    nilpotentLog a ∈ I := nilpotentSeries_mem I ha constantCoeff_log

theorem exp_sub_one_mem (I : NonUnitalSubalgebra ℚ A) {a : A}
    (ha : a ∈ I) (hna : IsNilpotent a) : IsNilpotent.exp a - 1 ∈ I := by
  rw [← nilpotentSeries_exp a, ← nilpotentSeries_one hna, ← nilpotentSeries_sub]
  exact nilpotentSeries_mem I ha (by simp [constantCoeff_exp])

theorem exp_mul_exp_sub_one_mem (I : NonUnitalSubalgebra ℚ A) {a b : A}
    (ha : a ∈ I) (hb : b ∈ I) (hna : IsNilpotent a) (hnb : IsNilpotent b) :
    IsNilpotent.exp a * IsNilpotent.exp b - 1 ∈ I := by
  have hpa := exp_sub_one_mem I ha hna
  have hpb := exp_sub_one_mem I hb hnb
  have hid : IsNilpotent.exp a * IsNilpotent.exp b - 1 =
      (IsNilpotent.exp a - 1) * (IsNilpotent.exp b - 1) +
        (IsNilpotent.exp a - 1) + (IsNilpotent.exp b - 1) := by noncomm_ring
  rw [hid]
  exact I.add_mem (I.add_mem (I.mul_mem hpa hpb) hpa) hpb

noncomputable def nilpotentBCH (a b : A) : A :=
  nilpotentLog (IsNilpotent.exp a * IsNilpotent.exp b - 1)

theorem nilpotentBCH_mem (I : NonUnitalSubalgebra ℚ A) {a b : A}
    (ha : a ∈ I) (hb : b ∈ I) (hna : IsNilpotent a) (hnb : IsNilpotent b) :
    nilpotentBCH a b ∈ I :=
  nilpotentLog_mem I (exp_mul_exp_sub_one_mem I ha hb hna hnb)

section NilAlgebra
variable (I : NonUnitalSubalgebra ℚ A) (hI : ∀ a ∈ I, IsNilpotent a)
include hI

theorem exp_nilpotentBCH {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    IsNilpotent.exp (nilpotentBCH a b) = IsNilpotent.exp a * IsNilpotent.exp b := by
  have hn := hI _ (exp_mul_exp_sub_one_mem I ha hb (hI _ ha) (hI _ hb))
  rw [nilpotentBCH, exp_nilpotentLog hn]
  abel

theorem nilpotentBCH_assoc {a b c : A} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I) :
    nilpotentBCH (nilpotentBCH a b) c = nilpotentBCH a (nilpotentBCH b c) := by
  have hab := nilpotentBCH_mem I ha hb (hI _ ha) (hI _ hb)
  have hbc := nilpotentBCH_mem I hb hc (hI _ hb) (hI _ hc)
  apply exp_injective_on_nilpotents
    (hI _ (nilpotentBCH_mem I hab hc (hI _ hab) (hI _ hc)))
    (hI _ (nilpotentBCH_mem I ha hbc (hI _ ha) (hI _ hbc)))
  rw [exp_nilpotentBCH I hI hab hc, exp_nilpotentBCH I hI ha hbc,
    exp_nilpotentBCH I hI ha hb, exp_nilpotentBCH I hI hb hc, mul_assoc]

end NilAlgebra

theorem nilpotentBCH_zero_left {a : A} (ha : IsNilpotent a) : nilpotentBCH 0 a = a := by
  simp only [nilpotentBCH, IsNilpotent.exp_zero, one_mul, nilpotentLog_exp_sub_one ha]

theorem nilpotentBCH_neg_left {a : A} (ha : IsNilpotent a) : nilpotentBCH (-a) a = 0 := by
  rw [nilpotentBCH, IsNilpotent.exp_neg_mul_exp_self ha, sub_self, nilpotentLog_zero]

theorem nilpotentBCH_eq_add_of_commute {a b : A} (ha : IsNilpotent a)
    (hb : IsNilpotent b) (hab : Commute a b) : nilpotentBCH a b = a + b := by
  rw [nilpotentBCH, ← IsNilpotent.exp_add_of_commute hab ha hb,
    nilpotentLog_exp_sub_one (hab.isNilpotent_add ha hb)]

end Erdos3

end

section

namespace Erdos3

open IsNilpotent TensorProduct Module.End

variable {R M N P : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [Module ℚ M] [IsScalarTower ℚ R M]
  [AddCommGroup N] [Module R N] [Module ℚ N] [IsScalarTower ℚ R N]
  [AddCommGroup P] [Module R P] [Module ℚ P] [IsScalarTower ℚ R P]

end Erdos3

end

section

namespace Erdos3

variable {A : Type*} [Ring A] [Algebra ℚ A]

namespace NilpotentBCHGroup
variable {I : NonUnitalSubalgebra ℚ A} {hI : ∀ a ∈ I, IsNilpotent a}


end NilpotentBCHGroup
end Erdos3

end

section

namespace Erdos3

open Finset

variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

noncomputable def finiteExp (k : ℕ) (a : A) : A :=
  ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • a ^ i

noncomputable def finiteLog (k : ℕ) (a : A) : A :=
  ∑ i ∈ range k, ((-1 : ℚ) ^ (i + 1) / i) • a ^ i

theorem map_finiteExp (φ : A →ₐ[ℚ] B) (k : ℕ) (a : A) :
    φ (finiteExp k a) = finiteExp k (φ a) := by simp [finiteExp]

theorem map_finiteLog (φ : A →ₐ[ℚ] B) (k : ℕ) (a : A) :
    φ (finiteLog k a) = finiteLog k (φ a) := by simp [finiteLog]

theorem finiteExp_eq_exp {a : A} {k : ℕ} (h : a ^ k = 0) :
    finiteExp k a = IsNilpotent.exp a := (IsNilpotent.exp_eq_sum h).symm

theorem finiteLog_eq_log {a : A} {k : ℕ} (h : a ^ k = 0) :
    finiteLog k a = nilpotentLog a := (nilpotentLog_eq_sum h).symm

noncomputable def bchPolynomial (k : ℕ) : FreeAlgebra ℚ (Fin 2) :=
  finiteLog k (finiteExp k (FreeAlgebra.ι ℚ 0) * finiteExp k (FreeAlgebra.ι ℚ 1) - 1)

noncomputable def bchPolynomialEval (a b : A) : FreeAlgebra ℚ (Fin 2) →ₐ[ℚ] A :=
  FreeAlgebra.lift ℚ ![a, b]

theorem bchPolynomialEval_formula (k : ℕ) (a b : A) :
    bchPolynomialEval a b (bchPolynomial k) =
      finiteLog k (finiteExp k a * finiteExp k b - 1) := by
  simp [bchPolynomial, bchPolynomialEval, map_finiteLog, map_finiteExp]

theorem bchPolynomialEval_eq (I : NonUnitalSubalgebra ℚ A) {k : ℕ}
    (hI : ∀ a ∈ I, a ^ k = 0) {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    bchPolynomialEval a b (bchPolynomial k) = nilpotentBCH a b := by
  have hna : IsNilpotent a := ⟨k, hI a ha⟩
  have hnb : IsNilpotent b := ⟨k, hI b hb⟩
  rw [bchPolynomialEval_formula, finiteExp_eq_exp (hI a ha), finiteExp_eq_exp (hI b hb),
    finiteLog_eq_log (hI _ (exp_mul_exp_sub_one_mem I ha hb hna hnb))]
  rfl

theorem map_nilpotentBCH (I : NonUnitalSubalgebra ℚ A)
    (hI : ∀ a ∈ I, IsNilpotent a) (φ : A →ₐ[ℚ] B) {a b : A}
    (ha : a ∈ I) (hb : b ∈ I) : φ (nilpotentBCH a b) = nilpotentBCH (φ a) (φ b) := by
  rw [nilpotentBCH, map_nilpotentLog (hI _
    (exp_mul_exp_sub_one_mem I ha hb (hI _ ha) (hI _ hb))), map_sub, map_mul, map_one,
    IsNilpotent.map_exp (hI _ ha), IsNilpotent.map_exp (hI _ hb), nilpotentBCH]

end Erdos3

end

section

namespace Erdos3
variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

theorem nilpotentBCH_commuting_maps
    (I : NonUnitalSubalgebra ℚ A) (hI : ∀ a ∈ I, IsNilpotent a)
    (J : NonUnitalSubalgebra ℚ B) (hJ : ∀ b ∈ J, IsNilpotent b)
    (L R : A →ₐ[ℚ] B) (hL : ∀ a ∈ I, L a ∈ J) (hR : ∀ a ∈ I, R a ∈ J)
    (hcomm : ∀ a b, Commute (L a) (R b)) {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    nilpotentBCH (L a + R a) (L b + R b) = L (nilpotentBCH a b) + R (nilpotentBCH a b) := by
  have hc := nilpotentBCH_mem I ha hb (hI _ ha) (hI _ hb)
  have hca := J.add_mem (hL _ ha) (hR _ ha)
  have hcb := J.add_mem (hL _ hb) (hR _ hb)
  apply exp_injective_on_nilpotents
    (hJ _ (nilpotentBCH_mem J hca hcb (hJ _ hca) (hJ _ hcb)))
    (hJ _ (J.add_mem (hL _ hc) (hR _ hc)))
  rw [exp_nilpotentBCH J hJ hca hcb,
    IsNilpotent.exp_add_of_commute (hcomm a a) (hJ _ (hL _ ha)) (hJ _ (hR _ ha)),
    IsNilpotent.exp_add_of_commute (hcomm b b) (hJ _ (hL _ hb)) (hJ _ (hR _ hb)),
    IsNilpotent.exp_add_of_commute (hcomm _ _) (hJ _ (hL _ hc)) (hJ _ (hR _ hc)),
    ← IsNilpotent.map_exp (hI _ ha) L, ← IsNilpotent.map_exp (hI _ ha) R,
    ← IsNilpotent.map_exp (hI _ hb) L, ← IsNilpotent.map_exp (hI _ hb) R,
    ← IsNilpotent.map_exp (hI _ hc) L, ← IsNilpotent.map_exp (hI _ hc) R,
    exp_nilpotentBCH I hI ha hb, map_mul, map_mul]
  exact (hcomm (IsNilpotent.exp b) (IsNilpotent.exp a)).symm.mul_mul_mul_comm _ _

end Erdos3

end

section

namespace Erdos3

variable (A : Type*) [Ring A] [Algebra ℚ A]

structure NilpotentAlgebraFiltration (s : ℕ) where
  layer : ℕ → Submodule ℚ A
  antitone : Antitone layer
  zero_eq_top : layer 0 = ⊤
  mul_mem : ∀ {i j : ℕ} {a b : A}, a ∈ layer i → b ∈ layer j → a * b ∈ layer (i + j)
  terminal : layer (s + 1) = ⊥

namespace NilpotentAlgebraFiltration
variable {A} {s : ℕ} (F : NilpotentAlgebraFiltration A s)

def layerAlgebra (i : ℕ) : NonUnitalSubalgebra ℚ A where
  carrier := F.layer i
  zero_mem' := (F.layer i).zero_mem
  add_mem' := (F.layer i).add_mem
  smul_mem' c _ hx := (F.layer i).smul_mem c hx
  mul_mem' ha hb := F.antitone (Nat.le_add_right i i) (F.mul_mem ha hb)

@[simp] theorem mem_layerAlgebra (i : ℕ) (a : A) : a ∈ F.layerAlgebra i ↔ a ∈ F.layer i :=
  Iff.rfl

theorem pow_mem {i : ℕ} {a : A} (ha : a ∈ F.layer i) (n : ℕ) :
    a ^ n ∈ F.layer (n * i) := by
  induction n with
  | zero => simp [F.zero_eq_top]
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact F.mul_mem ih ha

theorem pow_eq_zero {i : ℕ} (hi : 1 ≤ i) {a : A} (ha : a ∈ F.layer i) :
    a ^ (s + 1) = 0 := by
  have h := F.antitone (Nat.le_mul_of_pos_right (s + 1) hi) (F.pow_mem ha (s + 1))
  simpa only [F.terminal, Submodule.mem_bot] using h

theorem isNilpotent_of_mem {i : ℕ} (hi : 1 ≤ i) {a : A} (ha : a ∈ F.layer i) :
    IsNilpotent a := ⟨s + 1, F.pow_eq_zero hi ha⟩

theorem positive_nilpotent : ∀ a ∈ F.layerAlgebra 1, IsNilpotent a :=
  fun _ ha => F.isNilpotent_of_mem le_rfl ha

theorem bchPolynomial_formula {a b : A} (ha : a ∈ F.layer 1) (hb : b ∈ F.layer 1) :
    bchPolynomialEval a b (bchPolynomial (s + 1)) = nilpotentBCH a b :=
  bchPolynomialEval_eq (F.layerAlgebra 1) (fun _ hx => F.pow_eq_zero le_rfl hx) ha hb

theorem bch_mem {i : ℕ} (hi : 1 ≤ i) {a b : A}
    (ha : a ∈ F.layer i) (hb : b ∈ F.layer i) : nilpotentBCH a b ∈ F.layer i :=
  nilpotentBCH_mem (F.layerAlgebra i) ha hb
    (F.isNilpotent_of_mem hi ha) (F.isNilpotent_of_mem hi hb)

theorem exp_sub_one_mem_layer {i : ℕ} {a : A} (ha : a ∈ F.layer i)
    (hna : IsNilpotent a) : IsNilpotent.exp a - 1 ∈ F.layer i :=
  exp_sub_one_mem (F.layerAlgebra i) ha hna

end NilpotentAlgebraFiltration
end Erdos3

end

section

namespace Erdos3
open TensorProduct
variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

theorem seriesMap_commute (L R : A →ₐ[ℚ] B) (hcomm : ∀ a b, Commute (L a) (R b))
    (f g : PowerSeries A) : Commute (PowerSeries.mapAlgHom L f) (PowerSeries.mapAlgHom R g) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  conv_rhs => rw [← Finset.HasAntidiagonal.map_swap_antidiagonal]
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk,
    PowerSeries.mapAlgHom_apply, PowerSeries.coeff_map]
  apply Finset.sum_congr rfl
  intro ij _
  exact (hcomm _ _).eq

theorem truncatedSeriesMap_commute (s : ℕ) (L R : A →ₐ[ℚ] B)
    (hcomm : ∀ a b, Commute (L a) (R b)) (p q : TruncatedSeries A s) :
    Commute (truncatedSeriesMap s L p) (truncatedSeriesMap s R q) := by
  obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
  obtain ⟨g, rfl⟩ := truncatedSeriesMk_surjective s q
  exact (seriesMap_commute L R hcomm f g).map (truncatedSeriesMk s)

variable {X : Type*}

def TruncatedPrimitive {s : ℕ} (p : TruncatedSeries (FreeAlgebra ℚ X) s) : Prop :=
  truncatedSeriesMap s freeCoproduct p =
    truncatedSeriesMap s Algebra.TensorProduct.includeLeft p +
      truncatedSeriesMap s Algebra.TensorProduct.includeRight p

theorem TruncatedPrimitive.coeff {s : ℕ} {p : TruncatedSeries (FreeAlgebra ℚ X) s}
    (hp : TruncatedPrimitive p) (n : ℕ) (hn : n ≤ s) :
    FreePrimitive (truncatedSeriesCoeff s n hn p) := by
  have h := congrArg (truncatedSeriesCoeff s n hn) hp
  simpa only [FreePrimitive, truncatedSeriesCoeff_map, map_add, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply] using h

theorem truncatedPrimitive_iff_coeff {s : ℕ} (p : TruncatedSeries (FreeAlgebra ℚ X) s) :
    TruncatedPrimitive p ↔ ∀ n (hn : n ≤ s), FreePrimitive (truncatedSeriesCoeff s n hn p) := by
  refine ⟨fun hp n hn => hp.coeff n hn, fun h => ?_⟩
  apply truncatedSeries_ext
  intro n hn
  simpa only [FreePrimitive, truncatedSeriesCoeff_map, map_add, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply] using h n hn

theorem TruncatedPrimitive.bch {s : ℕ} {p q : TruncatedSeries (FreeAlgebra ℚ X) s}
    (hp : TruncatedPrimitive p) (hq : TruncatedPrimitive q)
    (hp0 : p ∈ truncatedSeriesPositive s) (hq0 : q ∈ truncatedSeriesPositive s) :
    TruncatedPrimitive (nilpotentBCH p q) := by
  let I := truncatedSeriesPositive (A := FreeAlgebra ℚ X) s
  let J := truncatedSeriesPositive (A := FreeAlgebra ℚ X ⊗[ℚ] FreeAlgebra ℚ X) s
  let D : TruncatedSeries (FreeAlgebra ℚ X) s →ₐ[ℚ]
      TruncatedSeries (FreeAlgebra ℚ X ⊗[ℚ] FreeAlgebra ℚ X) s :=
    truncatedSeriesMap s freeCoproduct
  let L : TruncatedSeries (FreeAlgebra ℚ X) s →ₐ[ℚ]
      TruncatedSeries (FreeAlgebra ℚ X ⊗[ℚ] FreeAlgebra ℚ X) s :=
    truncatedSeriesMap s Algebra.TensorProduct.includeLeft
  let R : TruncatedSeries (FreeAlgebra ℚ X) s →ₐ[ℚ]
      TruncatedSeries (FreeAlgebra ℚ X ⊗[ℚ] FreeAlgebra ℚ X) s :=
    truncatedSeriesMap s Algebra.TensorProduct.includeRight
  have hI : ∀ a ∈ I, IsNilpotent a := fun _ ha => truncatedSeriesPositive_nilpotent ha
  have hJ : ∀ a ∈ J, IsNilpotent a := fun _ ha => truncatedSeriesPositive_nilpotent ha
  change D (nilpotentBCH p q) = L (nilpotentBCH p q) + R (nilpotentBCH p q)
  calc
    D (nilpotentBCH p q) = nilpotentBCH (D p) (D q) :=
      map_nilpotentBCH (A := TruncatedSeries (FreeAlgebra ℚ X) s)
        (B := TruncatedSeries (FreeAlgebra ℚ X ⊗[ℚ] FreeAlgebra ℚ X) s)
        I hI D (a := p) (b := q) hp0 hq0
    _ = nilpotentBCH (L p + R p) (L q + R q) := congrArg₂ nilpotentBCH hp hq
    _ = L (nilpotentBCH p q) + R (nilpotentBCH p q) := ?_
  apply nilpotentBCH_commuting_maps (A := TruncatedSeries (FreeAlgebra ℚ X) s)
    (B := TruncatedSeries (FreeAlgebra ℚ X ⊗[ℚ] FreeAlgebra ℚ X) s) I hI J hJ L R
    (fun _ ha => truncatedSeriesMap_positive s _ ha)
    (fun _ ha => truncatedSeriesMap_positive s _ ha) _ hp0 hq0
  intro a b
  apply truncatedSeriesMap_commute
  intro u v
  change (u ⊗ₜ[ℚ] 1) * (1 ⊗ₜ[ℚ] v) = (1 ⊗ₜ[ℚ] v) * (u ⊗ₜ[ℚ] 1)
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end Erdos3

end

section

namespace Erdos3
variable {X : Type*}
attribute [local instance] LieRing.ofAssociativeRing

noncomputable def scaledFreeGenerator (s : ℕ) (x : X) : TruncatedSeries (FreeAlgebra ℚ X) s :=
  truncatedSeriesMk s (PowerSeries.monomial 1 (FreeAlgebra.ι ℚ x))

theorem scaledFreeGenerator_positive (s : ℕ) (x : X) :
    scaledFreeGenerator s x ∈ truncatedSeriesPositive s := by
  rw [mem_truncatedSeriesPositive]
  change PowerSeries.constantCoeff (PowerSeries.monomial 1 (FreeAlgebra.ι ℚ x)) = 0
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_monomial]
  rfl

theorem scaledFreeGenerator_primitive (s : ℕ) (x : X) :
    TruncatedPrimitive (scaledFreeGenerator s x) := by
  apply (truncatedPrimitive_iff_coeff _).mpr
  intro n hn
  change FreePrimitive (PowerSeries.coeff n (PowerSeries.monomial 1 (FreeAlgebra.ι ℚ x)))
  rw [PowerSeries.coeff_monomial]
  split_ifs
  · exact freePrimitive_generator x
  · simp [FreePrimitive]

theorem scaled_bchPolynomial (s : ℕ) :
    truncatedSeriesMk s (freeScaleSeries (bchPolynomial (s + 1))) =
      nilpotentBCH (scaledFreeGenerator s (0 : Fin 2)) (scaledFreeGenerator s (1 : Fin 2)) := by
  have h := bchPolynomialEval_eq (A := TruncatedSeries (FreeAlgebra ℚ (Fin 2)) s)
    (truncatedSeriesPositive s) (k := s + 1)
    (fun _ ha => truncatedSeriesPositive_pow ha)
    (a := scaledFreeGenerator s (0 : Fin 2)) (b := scaledFreeGenerator s (1 : Fin 2))
    (scaledFreeGenerator_positive s (0 : Fin 2)) (scaledFreeGenerator_positive s (1 : Fin 2))
  rw [bchPolynomialEval_formula] at h
  simpa only [bchPolynomial, map_finiteLog, map_sub, map_mul, map_one, map_finiteExp,
    freeScaleSeries_generator, scaledFreeGenerator] using h

theorem bchHomogeneousPart_primitive (s n : ℕ) (hn : n ≤ s) :
    FreePrimitive (freeHomogeneousPart n (bchPolynomial (s + 1))) := by
  have h := (scaledFreeGenerator_primitive s (0 : Fin 2)).bch
    (scaledFreeGenerator_primitive s (1 : Fin 2))
    (scaledFreeGenerator_positive s (0 : Fin 2)) (scaledFreeGenerator_positive s (1 : Fin 2))
  rw [← scaled_bchPolynomial] at h
  exact h.coeff n hn

theorem bchHomogeneousPart_mem (s n : ℕ) (hn : n ≤ s) :
    freeHomogeneousPart n (bchPolynomial (s + 1)) ∈ freeAssociativeLieSubalgebra :=
  (bchHomogeneousPart_primitive s n hn).mem

theorem bchTruncation_mem (s : ℕ) :
    freeTruncation s (bchPolynomial (s + 1)) ∈ freeAssociativeLieSubalgebra := by
  rw [freeTruncation_apply]
  apply freeAssociativeLieSubalgebra.sum_mem
  intro n hn
  exact bchHomogeneousPart_mem s n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))

noncomputable def bchLiePolynomial (s : ℕ) : FreeLieAlgebra ℚ (Fin 2) :=
  Classical.choose (bchTruncation_mem s)

theorem bchLiePolynomial_expansion (s : ℕ) :
    freeLieAssociativeExpansion (bchLiePolynomial s) = freeTruncation s (bchPolynomial (s + 1)) :=
  Classical.choose_spec (bchTruncation_mem s)

noncomputable def lieBCH {L : Type*} [LieRing L] [LieAlgebra ℚ L] (s : ℕ) (a b : L) : L :=
  FreeLieAlgebra.lift ℚ ![a, b] (bchLiePolynomial s)

end Erdos3

end

section

namespace Erdos3

noncomputable def bchWordCoefficients (s : ℕ) : FreeSemigroup (Fin 2) →₀ ℚ :=
  (freeLieWordExpansion (bchLiePolynomial s)).coeff

noncomputable def bchBracketSupport (s : ℕ) : Finset (FreeSemigroup (Fin 2)) :=
  (bchWordCoefficients s).support

noncomputable def bchBracketCoefficient (s : ℕ) (w : FreeSemigroup (Fin 2)) : ℚ :=
  bchWordCoefficients s w / w.length

theorem bchWordExpansion_truncation (s : ℕ) :
    wordTruncation s (freeLieWordExpansion (bchLiePolynomial s)) =
      freeLieWordExpansion (bchLiePolynomial s) := by
  apply wordPolynomialEmbedding_injective
  rw [wordPolynomialEmbedding_truncation, wordPolynomialEmbedding_freeLieExpansion,
    bchLiePolynomial_expansion, freeTruncation_idempotent]

theorem bchBracketSupport_length (s : ℕ) {w : FreeSemigroup (Fin 2)}
    (hw : w ∈ bchBracketSupport s) : w.length ≤ s := by
  have h := congrArg (fun p : WordPolynomial (Fin 2) => p.coeff w) (bchWordExpansion_truncation s)
  rw [wordTruncation_coeff] at h
  by_contra hgt
  rw [ite_eq_right hgt] at h
  exact (Finsupp.mem_support_iff.mp hw) h.symm

theorem lieBCH_bracket_formula {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (s : ℕ) (a b : L) :
    lieBCH s a b = ∑ w ∈ bchBracketSupport s, bchBracketCoefficient s w • dynkinWord ![a, b] w := by
  rw [lieBCH, ← dynkinProjection_lift]
  change (bchWordCoefficients s).sum (fun w r => r • ((w.length : ℚ)⁻¹ • dynkinWord ![a, b] w)) = _
  simp only [Finsupp.sum, bchBracketSupport, bchBracketCoefficient, smul_smul, div_eq_mul_inv]

noncomputable def bchCoefficientHeight (s : ℕ) : ℕ :=
  1 + (bchBracketSupport s).sup (fun w =>
    max (bchBracketCoefficient s w).num.natAbs (bchBracketCoefficient s w).den)

theorem bchBracketCoefficient_height (s : ℕ) {w : FreeSemigroup (Fin 2)}
    (hw : w ∈ bchBracketSupport s) : RationalHeightLE (bchBracketCoefficient s w) (bchCoefficientHeight s) := by
  have h := Finset.le_sup (f := fun w =>
    max (bchBracketCoefficient s w).num.natAbs (bchBracketCoefficient s w).den) hw
  constructor
  · exact (le_max_left _ _).trans (h.trans (Nat.le_add_left _ 1))
  · exact (le_max_right _ _).trans (h.trans (Nat.le_add_left _ 1))

theorem exists_bch_integer_coefficients (s : ℕ) :
    ∃ D : ℕ, 0 < D ∧ D ≤ bchCoefficientHeight s ^ (bchBracketSupport s).card ∧
      ∃ c : (w : FreeSemigroup (Fin 2)) → w ∈ bchBracketSupport s → ℤ,
        (∀ w hw, (c w hw : ℚ) = (D : ℚ) * bchBracketCoefficient s w) ∧
        ∀ w hw, (c w hw).natAbs ≤ bchCoefficientHeight s ^ (bchBracketSupport s).card := by
  classical
  let q : bchBracketSupport s → ℚ := fun w => bchBracketCoefficient s w
  have hq : ∀ w, RationalHeightLE (q w) (bchCoefficientHeight s) :=
    fun w => bchBracketCoefficient_height s w.property
  obtain ⟨D, hD, hDb, c, hc, hcb⟩ := exists_bounded_integer_array q hq
  refine ⟨D, hD, ?_, (fun w hw => c ⟨w, hw⟩), ?_, ?_⟩
  · simpa only [Fintype.card_coe] using hDb
  · intro w hw
    exact hc ⟨w, hw⟩
  · intro w hw
    simpa only [Fintype.card_coe] using hcb ⟨w, hw⟩

end Erdos3

end

section

namespace Erdos3
variable {X A : Type*} [Ring A] [Algebra ℚ A]
attribute [local instance] LieRing.ofAssociativeRing

namespace NilpotentAlgebraFiltration
variable {s : ℕ} (F : NilpotentAlgebraFiltration A s) (f : X → A)

theorem eval_freeWord_mem (hf : ∀ x, f x ∈ F.layer 1) (w : FreeMonoid X) :
    FreeAlgebra.lift ℚ f (freeWord w) ∈ F.layer w.length := by
  induction w using freeMonoid_induction_right with
  | h1 => simp [F.zero_eq_top]
  | hstep w x hw =>
    rw [map_mul, map_mul, freeWord_of, FreeAlgebra.lift_ι_apply,
      FreeMonoid.length_mul, FreeMonoid.length_of]
    exact F.mul_mem hw (hf x)

theorem eval_freeWord_eq_zero (hf : ∀ x, f x ∈ F.layer 1) (w : FreeMonoid X)
    (hw : s < w.length) : FreeAlgebra.lift ℚ f (freeWord w) = 0 := by
  have h := F.antitone (Nat.succ_le_of_lt hw) (F.eval_freeWord_mem f hf w)
  simpa only [F.terminal, Submodule.mem_bot] using h

theorem eval_freeTruncation (hf : ∀ x, f x ∈ F.layer 1) (p : FreeAlgebra ℚ X) :
    FreeAlgebra.lift ℚ f (freeTruncation s p) = FreeAlgebra.lift ℚ f p := by
  apply freeAlgebra_linear_induction (fun p =>
    FreeAlgebra.lift ℚ f (freeTruncation s p) = FreeAlgebra.lift ℚ f p)
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro r p hp
    simp only [map_smul, hp]
  · intro w
    rw [freeTruncation_word]
    split_ifs with hw
    · rfl
    · rw [map_zero, F.eval_freeWord_eq_zero f hf w (Nat.lt_of_not_ge hw)]

end NilpotentAlgebraFiltration

theorem freeLieAssociativeExpansion_eval (f : X → A) (p : FreeLieAlgebra ℚ X) :
    FreeAlgebra.lift ℚ f (freeLieAssociativeExpansion p) = FreeLieAlgebra.lift ℚ f p := by
  have h : (FreeAlgebra.lift ℚ f).toLieHom.comp freeLieAssociativeExpansion = FreeLieAlgebra.lift ℚ f := by
    apply FreeLieAlgebra.hom_ext
    intro x
    simp [freeLieAssociativeExpansion]
  exact DFunLike.congr_fun h p

theorem NilpotentAlgebraFiltration.lieBCH_eq {s : ℕ} (F : NilpotentAlgebraFiltration A s)
    {a b : A} (ha : a ∈ F.layer 1) (hb : b ∈ F.layer 1) : lieBCH s a b = nilpotentBCH a b := by
  rw [lieBCH, ← freeLieAssociativeExpansion_eval, bchLiePolynomial_expansion,
    F.eval_freeTruncation ![a, b] (by intro x; fin_cases x <;> assumption)]
  exact F.bchPolynomial_formula ha hb

end Erdos3

end

section

namespace Erdos3

open Module

section General

variable {X Y L : Type*} [TopologicalSpace Y] [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousConstSMul ℚ L]

omit [IsTopologicalAddGroup L] [ContinuousConstSMul ℚ L] in
theorem continuous_rightBracketList
    (hlie : Continuous (fun z : L × L => ⁅z.1, z.2⁆))
    (f : X → Y → L) (hf : ∀ x, Continuous (f x)) (xs : List X)
    (a : Y → L) (ha : Continuous a) :
    Continuous (fun y => rightBracketList (fun x => f x y) xs (a y)) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    exact ih (fun y => ⁅a y, f x y⁆) (hlie.comp (ha.prodMk (hf x)))

omit [IsTopologicalAddGroup L] [ContinuousConstSMul ℚ L] in
theorem continuous_dynkinWord
    (hlie : Continuous (fun z : L × L => ⁅z.1, z.2⁆))
    (f : X → Y → L) (hf : ∀ x, Continuous (f x)) (w : FreeSemigroup X) :
    Continuous (fun y => dynkinWord (fun x => f x y) w) :=
  continuous_rightBracketList hlie f hf w.tail (f w.head) (hf w.head)

theorem continuous_lieBCH
    (hlie : Continuous (fun z : L × L => ⁅z.1, z.2⁆)) (s : ℕ) :
    Continuous (fun z : L × L => lieBCH s z.1 z.2) := by
  simp only [lieBCH_bracket_formula]
  apply continuous_finsetSum
  intro w _
  apply Continuous.const_smul
  exact continuous_dynkinWord hlie (fun i (z : L × L) => ![z.1, z.2] i)
    (by intro i; fin_cases i; exact continuous_fst; exact continuous_snd) w

end General

section Real

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

theorem continuous_lie_of_real_basis (e : Basis ι ℝ L) :
    Continuous (fun z : L × L => ⁅z.1, z.2⁆) := by
  classical
  have hcoord (i : ι) : Continuous (fun x : L => e.repr x i) :=
    (continuous_apply i).comp e.equivFunL.continuous
  have hformula (a b : L) : ⁅a, b⁆ =
      ∑ i, ∑ j, e.repr a i • e.repr b j • ⁅e i, e j⁆ := by
    conv_lhs => rw [← e.sum_repr a, ← e.sum_repr b]
    simp only [sum_lie, lie_sum, smul_lie, lie_smul, Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact smul_comm _ _ _
  have heq : (fun z : L × L => ⁅z.1, z.2⁆) =
      (fun z => ∑ i, ∑ j, e.repr z.1 i • e.repr z.2 j • ⁅e i, e j⁆) :=
    funext (fun z => hformula z.1 z.2)
  rw [heq]
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact ((hcoord i).comp continuous_fst).smul
    (((hcoord j).comp continuous_snd).smul continuous_const)

theorem continuous_lie_finiteDimensional [FiniteDimensional ℝ L] :
    Continuous (fun z : L × L => ⁅z.1, z.2⁆) :=
  continuous_lie_of_real_basis (Module.finBasis ℝ L)

end Real

end Erdos3

end

end OAI

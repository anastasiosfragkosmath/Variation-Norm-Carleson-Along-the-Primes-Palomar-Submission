module

public import PrimeCarleson.Proof.Fplus31.Cramer.Model
public import PrimeCarleson.Proof.Fplus31.Brun.Combinatorics

/-!
# Brun's pure sieve: divisors of `P(w)` versus sets of primes

The Brun truncation of the Cramér model `Λ_{C,w}` (a type I sum, used in the proof of [F+]
Proposition 3.1):

* `brunSet w k`: the divisors `d ∣ P(w)` with `ω(d) ≤ k` (the level of the type I sum;
  `le_pow_of_mem_brunSet`: `d ≤ w^k`);
* `truncMoebius w k n = ∑_{d ∈ brunSet w k, d ∣ n} μ(d)` and
  `brunTrunc w k n = (P(w)/φ(P(w))) · truncMoebius w k n`: the type I sum;
* `sum_brunSet`: a sum over `brunSet w k` equals the double sum over `j ≤ k` and the
  `j`-subsets `D` of the primes below `w`, with `d = ∏ D` and `μ(d) = (-1)^j`;
* `smallPrimeDivisors w n`: the primes `p < w` with `p ∣ n`; `cramerModel_eq_ite`,
  `brunTrunc_eq`: `Λ_{C,w}(n) = (P/φ(P)) 1_{A = ∅}` and
  `brunTrunc w k n = (P/φ(P)) ∑_{j ≤ k} (-1)^j C(|A|, j)` with `A = smallPrimeDivisors w n`;
* `abs_cramerModel_sub_brunTrunc_le`: the pointwise Bonferroni bound
  `|Λ_{C,w}(n) - brunTrunc w k n| ≤ (P/φ(P)) C(|A|, k+1)`;
* `sum_choose_smallPrimeDivisors`: the double count
  `∑_{n ∈ X} C(|A(n)|, j) = ∑_{D ⊆ primes below w, |D| = j} #{n ∈ X : ∏ D ∣ n}`.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- A sum over the divisors of `P(w)` is a sum over the subsets `D` of the primes below `w`,
with `d = ∏ D`. -/
theorem sum_divisors_primorialBelow {M : Type*} [AddCommMonoid M] (w : ℕ) (h : ℕ → M) :
    ∑ d ∈ (primorialBelow w).divisors, h d =
      ∑ D ∈ (Nat.primesBelow w).powerset, h (∏ p ∈ D, p) := by
  refine Finset.sum_nbij' (fun d => d.primeFactors) (fun D => ∏ p ∈ D, p) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_powerset, ← primeFactors_primorialBelow]
    exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) (primorialBelow_pos w).ne'
  · intro D hD
    rw [Finset.mem_powerset] at hD
    refine Nat.mem_divisors.mpr ⟨?_, (primorialBelow_pos w).ne'⟩
    exact Finset.prod_dvd_prod_of_subset _ _ _ hD
  · intro d hd
    exact Nat.prod_primeFactors_of_squarefree
      ((squarefree_primorialBelow w).squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))
  · intro D hD
    rw [Finset.mem_powerset] at hD
    exact Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primesBelow (hD hp)
  · intro d hd
    rw [Nat.prod_primeFactors_of_squarefree
      ((squarefree_primorialBelow w).squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))]

/-- `μ(∏ D) = (-1)^{|D|}` for a finite set `D` of primes. -/
theorem moebius_prod_primes {D : Finset ℕ} (h : ∀ p ∈ D, p.Prime) :
    ((ArithmeticFunction.moebius (∏ p ∈ D, p) : ℤ) : ℝ) = (-1 : ℝ) ^ D.card := by
  rw [ArithmeticFunction.IsMultiplicative.map_prod_of_prime
      ArithmeticFunction.isMultiplicative_moebius D h]
  push_cast
  rw [Finset.prod_congr rfl (fun p hp => by rw [ArithmeticFunction.moebius_apply_prime (h p hp)]),
    Finset.prod_const]
  simp

/-- The index set of the Brun truncation: the divisors `d ∣ P(w)` with at most `k` prime
factors. -/
def brunSet (w k : ℕ) : Finset ℕ :=
  (primorialBelow w).divisors.filter fun d => d.primeFactors.card ≤ k

theorem mem_brunSet {w k d : ℕ} :
    d ∈ brunSet w k ↔ d ∣ primorialBelow w ∧ d.primeFactors.card ≤ k := by
  simp [brunSet, (primorialBelow_pos w).ne']

/-- A sum over `brunSet w k`: the double sum over `j ≤ k` and the `j`-subsets `D` of the primes
below `w`, with `d = ∏ D` and `μ(d) = (-1)^j`. -/
theorem sum_brunSet (w k : ℕ) (F : ℕ → ℝ) :
    ∑ d ∈ brunSet w k, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * F d =
      ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
        ∑ D ∈ (Nat.primesBelow w).powersetCard j, F (∏ p ∈ D, p) := by
  rw [brunSet, Finset.sum_filter, sum_divisors_primorialBelow, Finset.sum_powerset]
  have hterm : ∀ j ∈ range ((Nat.primesBelow w).card + 1),
      ∑ D ∈ (Nat.primesBelow w).powersetCard j,
        (if (∏ p ∈ D, p).primeFactors.card ≤ k then
          ((ArithmeticFunction.moebius (∏ p ∈ D, p) : ℤ) : ℝ) * F (∏ p ∈ D, p) else 0) =
      if j ≤ k then (-1 : ℝ) ^ j *
        ∑ D ∈ (Nat.primesBelow w).powersetCard j, F (∏ p ∈ D, p) else 0 := by
    intro j _
    split_ifs with hjk
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun D hD => ?_
      obtain ⟨hDs, hDj⟩ := Finset.mem_powersetCard.mp hD
      have hprime : ∀ p ∈ D, p.Prime := fun p hp => Nat.prime_of_mem_primesBelow (hDs hp)
      have hc : (∏ p ∈ D, p).primeFactors.card ≤ k := by
        rw [Nat.primeFactors_prod hprime, hDj]
        exact hjk
      simp only [hc, ↓reduceIte, moebius_prod_primes hprime, hDj]
    · refine Finset.sum_eq_zero fun D hD => ?_
      obtain ⟨hDs, hDj⟩ := Finset.mem_powersetCard.mp hD
      have hprime : ∀ p ∈ D, p.Prime := fun p hp => Nat.prime_of_mem_primesBelow (hDs hp)
      rw [Nat.primeFactors_prod hprime, hDj]
      simp [hjk]
  rw [Finset.sum_congr rfl hterm]
  refine sum_range_ite_le (fun j => (-1 : ℝ) ^ j *
    ∑ D ∈ (Nat.primesBelow w).powersetCard j, F (∏ p ∈ D, p)) k _ fun j hj => ?_
  rw [Finset.powersetCard_eq_empty.mpr (by omega)]
  simp

/-- The truncated Möbius sum `T_k(n) = ∑_{d ∣ P(w), ω(d) ≤ k, d ∣ n} μ(d)` (Brun's pure sieve:
`T_k(n)` approximates `1_{(n, P(w)) = 1}`). -/
def truncMoebius (w k : ℕ) (n : ℤ) : ℝ :=
  ∑ d ∈ brunSet w k, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (if (d : ℤ) ∣ n then 1 else 0)

/-- The Brun truncation `Λ_{C,w}^{(k)}(n) = (P/φ(P)) ∑_{d ∣ P(w), ω(d) ≤ k, d ∣ n} μ(d)`:
a type I sum with coefficients `(P/φ(P)) μ(d)`, supported on `d ∈ brunSet w k` (so `d ≤ w^k`). -/
def brunTrunc (w k : ℕ) (n : ℤ) : ℝ :=
  (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) * truncMoebius w k n

/-- The level of the type I sum: `d ≤ w^k` for `d ∈ brunSet w k`, `w ≥ 1`. -/
theorem le_pow_of_mem_brunSet {w k d : ℕ} (hw : 1 ≤ w) (hd : d ∈ brunSet w k) : d ≤ w ^ k := by
  obtain ⟨hdP, hdk⟩ := mem_brunSet.mp hd
  have hsq : Squarefree d := (squarefree_primorialBelow w).squarefree_of_dvd hdP
  have hsub : d.primeFactors ⊆ Nat.primesBelow w := by
    rw [← primeFactors_primorialBelow]
    exact Nat.primeFactors_mono hdP (primorialBelow_pos w).ne'
  calc d = ∏ p ∈ d.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsq).symm
    _ ≤ w ^ d.primeFactors.card :=
        Finset.prod_le_pow_card _ _ _ fun p hp => (Nat.lt_of_mem_primesBelow (hsub hp)).le
    _ ≤ w ^ k := Nat.pow_le_pow_right hw hdk

/-- The primes `p < w` dividing `n`. -/
def smallPrimeDivisors (w : ℕ) (n : ℤ) : Finset ℕ :=
  (Nat.primesBelow w).filter fun p => (p : ℤ) ∣ n

theorem smallPrimeDivisors_subset (w : ℕ) (n : ℤ) :
    smallPrimeDivisors w n ⊆ Nat.primesBelow w :=
  Finset.filter_subset _ _

/-- `Λ_{C,w}(n) = (P/φ(P)) 1_{no prime below w divides n}`. -/
theorem cramerModel_eq_ite (w : ℕ) (n : ℤ) :
    cramerModel w n =
      if smallPrimeDivisors w n = ∅ then
        (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) else 0 := by
  have h : Int.gcd n (primorialBelow w : ℤ) = 1 ↔ smallPrimeDivisors w n = ∅ := by
    rw [gcd_primorialBelow_eq_one_iff, smallPrimeDivisors, Finset.filter_eq_empty_iff]
  simp only [cramerModel, h]

/-- For a set `D` of primes below `w`: `∏ D ∣ n` iff every `p ∈ D` divides `n`. -/
theorem prod_dvd_iff_subset {w : ℕ} {D : Finset ℕ} (hD : D ⊆ Nat.primesBelow w) (n : ℤ) :
    (((∏ p ∈ D, p : ℕ) : ℤ) ∣ n) ↔ D ⊆ smallPrimeDivisors w n := by
  have hprime : ∀ p ∈ D, Prime p := fun p hp => (Nat.prime_of_mem_primesBelow (hD hp)).prime
  rw [Int.natCast_dvd]
  constructor
  · intro h p hp
    rw [smallPrimeDivisors, Finset.mem_filter]
    refine ⟨hD hp, ?_⟩
    rw [Int.natCast_dvd]
    exact (Finset.dvd_prod_of_mem _ hp).trans h
  · intro h
    refine Finset.prod_primes_dvd _ hprime fun p hp => ?_
    have := (Finset.mem_filter.mp (h hp)).2
    rwa [Int.natCast_dvd] at this

/-- The number of `j`-subsets `D` of the primes below `w` with `∏ D ∣ n` is `C(|A|, j)`,
`A = smallPrimeDivisors w n`. -/
theorem sum_powersetCard_dvd (w j : ℕ) (n : ℤ) :
    ∑ D ∈ (Nat.primesBelow w).powersetCard j, (if (((∏ p ∈ D, p : ℕ) : ℤ) ∣ n) then (1 : ℝ) else 0)
      = (((smallPrimeDivisors w n).card.choose j : ℕ) : ℝ) := by
  rw [Finset.sum_boole, ← Finset.card_powersetCard]
  have hset : ((Nat.primesBelow w).powersetCard j).filter
      (fun D => (((∏ p ∈ D, p : ℕ) : ℤ) ∣ n)) = (smallPrimeDivisors w n).powersetCard j := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hDs, hDj⟩, hdvd⟩
      exact ⟨(prod_dvd_iff_subset hDs n).mp hdvd, hDj⟩
    · rintro ⟨hDA, hDj⟩
      have hDs : D ⊆ Nat.primesBelow w := hDA.trans (smallPrimeDivisors_subset w n)
      exact ⟨⟨hDs, hDj⟩, (prod_dvd_iff_subset hDs n).mpr hDA⟩
  rw [hset]

/-- `brunTrunc w k n = (P/φ(P)) ∑_{j ≤ k} (-1)^j C(|A|, j)`, `A = smallPrimeDivisors w n`. -/
theorem brunTrunc_eq (w k : ℕ) (n : ℤ) :
    brunTrunc w k n =
      (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) *
        ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * (((smallPrimeDivisors w n).card.choose j : ℕ) : ℝ) := by
  rw [brunTrunc, truncMoebius, sum_brunSet w k (fun d => if (d : ℤ) ∣ n then (1 : ℝ) else 0)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_powersetCard_dvd]

/-- **Pointwise Bonferroni.** `|Λ_{C,w}(n) - Λ_{C,w}^{(k)}(n)| ≤ (P/φ(P)) C(|A|, k+1)`,
`A = smallPrimeDivisors w n` the set of primes `p < w` dividing `n`. -/
theorem abs_cramerModel_sub_brunTrunc_le (w k : ℕ) (n : ℤ) :
    |cramerModel w n - brunTrunc w k n| ≤
      (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) *
        (((smallPrimeDivisors w n).card.choose (k + 1) : ℕ) : ℝ) := by
  have hW : 0 ≤ (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) := by positivity
  have hb := abs_ite_sub_alternating_choose_le (smallPrimeDivisors w n).card k
  have hb' : |(if (smallPrimeDivisors w n).card = 0 then (1 : ℝ) else 0) -
      ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * (((smallPrimeDivisors w n).card.choose j : ℕ) : ℝ)| ≤
      (((smallPrimeDivisors w n).card.choose (k + 1) : ℕ) : ℝ) := by
    exact_mod_cast hb
  simp only [Finset.card_eq_zero] at hb'
  rw [brunTrunc_eq, cramerModel_eq_ite]
  have hite : (if smallPrimeDivisors w n = ∅ then
      (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) else 0) =
      (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) *
        (if smallPrimeDivisors w n = ∅ then (1 : ℝ) else 0) := by
    split_ifs <;> simp
  rw [hite, ← mul_sub, abs_mul, abs_of_nonneg hW]
  exact mul_le_mul_of_nonneg_left hb' hW

/-- The double count: `∑_{n ∈ X} C(|A(n)|, j) = ∑_{|D| = j} #{n ∈ X : ∏ D ∣ n}`, `D` ranging
over the `j`-subsets of the primes below `w`. -/
theorem sum_choose_smallPrimeDivisors (w j : ℕ) (X : Finset ℤ) :
    ∑ n ∈ X, (((smallPrimeDivisors w n).card.choose j : ℕ) : ℝ) =
      ∑ D ∈ (Nat.primesBelow w).powersetCard j,
        ((X.filter fun n => (((∏ p ∈ D, p : ℕ) : ℤ) ∣ n)).card : ℝ) := by
  simp_rw [← sum_powersetCard_dvd w j]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [Finset.sum_boole]

end PrimeCarleson.Proof.Fplus31

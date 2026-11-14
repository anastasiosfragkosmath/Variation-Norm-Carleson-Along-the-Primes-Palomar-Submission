module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.NumberTheory.SmoothNumbers
public import PrimeCarleson.Proof.Common.Mertens
public import PrimeCarleson.Proof.Common.TotientBound
public import PrimeCarleson.Proof.Common.EulerProductFinite

/-!
# The Cramér model `Λ_{C,w}` and arithmetic progressions

Part of the proof of [F+] Proposition 3.1: the Cramér model of Tao–Teräväinen,
`Λ_{Cramér,w}(n) = P(w)/φ(P(w)) · 1_{(n, P(w)) = 1}` with `P(w) = ∏_{p < w} p`, and the progression
`{lo < n ≤ hi, n ≡ a (mod r)}` on which it is compared with `Λ`.

* `primorialBelow w = ∏_{p < w} p`, with `primeFactors_primorialBelow`,
  `squarefree_primorialBelow`, `dvd_primorialBelow_iff` (`q ∣ P(w)` iff `q` is squarefree with all
  prime factors below `w`), `dvd_primorialBelow_of_squarefree` (every squarefree `q < w` divides
  `P(w)`);
* `cramerModel w n` (on `ℤ`) and `apSet r a lo hi` (the progression, a `Finset ℤ`);
* `gcd_primorialBelow_eq_one_iff`: `(n, P(w)) = 1` iff no prime `p < w` divides `n`;
* `primorialBelow_div_totient`: `P(w)/φ(P(w)) = ∏_{p < w} (1 + 1/(p-1))`, and the bound
  `P(w)/φ(P(w)) ≤ e⁵ log w` (`primorialBelow_div_totient_le`, from Mertens), whence
  `0 ≤ cramerModel w n ≤ e⁵ log w` (`cramerModel_nonneg`, `cramerModel_le`);
* `cramerModel_mul_self`: `Λ_{C,w}² = (P(w)/φ(P(w))) Λ_{C,w}`;
* `cramerModel_eq_zero_of_not_coprime`: on a progression `a mod r` with `1 ≤ r < w` and
  `gcd(a, r) > 1` the model vanishes identically (this needs `r ≥ 1`);
* `abs_card_filter_modEq_sub_le`: a residue class modulo `m` has `(hi - lo)/m + θ`, `|θ| ≤ 1`,
  elements in `(lo, hi]`; in particular `card_apSet_le` and `abs_card_apSet_sub_le`.

Used by the prime number theorem in progressions (`c5_target_sw`, `cramerModel_nonneg`,
`cramerModel_le`, `cramerModel_eq_zero_of_not_coprime`), by the comparison with the Heath-Brown
model (the model `Λ_{C,w}`) and by the iteration and the final assembly (the bound
`0 ≤ Λ_C ≪ log w`).
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- `P(w) = ∏_{p < w} p`, the product of the primes below `w`. -/
def primorialBelow (w : ℕ) : ℕ := ∏ p ∈ Nat.primesBelow w, p

/-- The Cramér model `Λ_{C,w}(n) = P(w)/φ(P(w)) · 1_{(n, P(w)) = 1}`
(Tao–Teräväinen, `intro.tex` L47-51; convention `p < w`). -/
def cramerModel (w : ℕ) (n : ℤ) : ℝ :=
  if Int.gcd n (primorialBelow w : ℤ) = 1 then
    (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) else 0

/-- The arithmetic progression `{n : lo < n ≤ hi, n ≡ a mod r}`. -/
def apSet (r : ℕ) (a : ℤ) (lo hi : ℕ) : Finset ℤ :=
  (Finset.Ioc (lo : ℤ) hi).filter (fun n => n ≡ a [ZMOD r])

theorem primorialBelow_pos (w : ℕ) : 0 < primorialBelow w :=
  Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primesBelow hp).pos

/-- The prime factors of `P(w)` are the primes below `w`. -/
theorem primeFactors_primorialBelow (w : ℕ) :
    (primorialBelow w).primeFactors = Nat.primesBelow w :=
  Nat.primeFactors_prod fun _ hp => Nat.prime_of_mem_primesBelow hp

/-- `P(w)` is squarefree. -/
theorem squarefree_primorialBelow (w : ℕ) : Squarefree (primorialBelow w) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    fun _ hp => (Nat.prime_of_mem_primesBelow hp).squarefree
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (Nat.prime_of_mem_primesBelow hp)
    (Nat.prime_of_mem_primesBelow hq)).mpr hpq

/-- `q ∣ P(w)` if and only if `q` is squarefree with all prime factors below `w`. -/
theorem dvd_primorialBelow_iff {q w : ℕ} :
    q ∣ primorialBelow w ↔ Squarefree q ∧ ∀ p ∈ q.primeFactors, p < w := by
  constructor
  · intro h
    refine ⟨(squarefree_primorialBelow w).squarefree_of_dvd h, fun p hp => ?_⟩
    have : p ∈ (primorialBelow w).primeFactors :=
      Nat.primeFactors_mono h (primorialBelow_pos w).ne' hp
    rw [primeFactors_primorialBelow] at this
    exact Nat.lt_of_mem_primesBelow this
  · rintro ⟨hq, hp⟩
    rw [← Nat.prod_primeFactors_of_squarefree hq]
    refine Finset.prod_dvd_prod_of_subset _ _ _ fun p hpq => ?_
    exact Nat.mem_primesBelow.mpr ⟨hp p hpq, Nat.prime_of_mem_primeFactors hpq⟩

/-- Every squarefree `q < w` divides `P(w)` (so for `w = T' + 1` every squarefree `q ≤ T'`). -/
theorem dvd_primorialBelow_of_squarefree {q w : ℕ} (hq : Squarefree q) (hqw : q < w) :
    q ∣ primorialBelow w :=
  dvd_primorialBelow_iff.mpr ⟨hq, fun _ hp =>
    lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hq.ne_zero)
      (Nat.dvd_of_mem_primeFactors hp)) hqw⟩

/-- `(n, P(w)) = 1` if and only if no prime below `w` divides `n`. -/
theorem gcd_primorialBelow_eq_one_iff (w : ℕ) (n : ℤ) :
    Int.gcd n (primorialBelow w : ℤ) = 1 ↔ ∀ p ∈ Nat.primesBelow w, ¬ (p : ℤ) ∣ n := by
  rw [Int.gcd, Int.natAbs_natCast, ← Nat.coprime_iff_gcd_eq_one, primorialBelow,
    Nat.coprime_prod_right_iff]
  refine forall₂_congr fun p hp => ?_
  rw [Int.natCast_dvd, Nat.coprime_comm, (Nat.prime_of_mem_primesBelow hp).coprime_iff_not_dvd]

/-- Euler's product formula for `φ(P(w))`. -/
theorem totient_primorialBelow_eq (w : ℕ) :
    (Nat.totient (primorialBelow w) : ℝ) =
      (primorialBelow w : ℝ) * ∏ p ∈ Nat.primesBelow w, (1 - (p : ℝ)⁻¹) := by
  have h := Nat.totient_eq_mul_prod_factors (primorialBelow w)
  rw [primeFactors_primorialBelow] at h
  have h' := congrArg (fun x : ℚ => (x : ℝ)) h
  simpa using h'

/-- `P(w)/φ(P(w)) = ∏_{p < w} (1 + 1/(p-1)) = ∏_{p < w} p/(p-1)`. -/
theorem primorialBelow_div_totient (w : ℕ) :
    (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) =
      ∏ p ∈ Nat.primesBelow w, (1 + 1 / ((p : ℝ) - 1)) := by
  have hpos : (0 : ℝ) < primorialBelow w := by exact_mod_cast primorialBelow_pos w
  rw [totient_primorialBelow_eq, div_mul_eq_div_div, div_self hpos.ne', one_div,
    ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast Nat.two_le_of_mem_primesBelow hp
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (p : ℝ) ≠ 0 := by linarith
  field_simp
  ring

/-- The Cramér model is nonnegative. -/
theorem cramerModel_nonneg (w : ℕ) (n : ℤ) : 0 ≤ cramerModel w n := by
  unfold cramerModel
  split_ifs
  · positivity
  · exact le_rfl

/-- `P(w)/φ(P(w)) ≤ e⁵ log w` for `w ≥ 2` (Mertens). -/
theorem primorialBelow_div_totient_le (w : ℕ) (hw : 2 ≤ w) :
    (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) ≤
      Real.exp 5 * Real.log w := by
  rw [primorialBelow_div_totient]
  have hp2 : ∀ p ∈ Nat.primesBelow w, (2 : ℝ) ≤ p := fun p hp => by
    exact_mod_cast Nat.two_le_of_mem_primesBelow hp
  refine le_trans (PrimeCarleson.Proof.Common.prod_one_add_le_exp_sum _ _ ?_) ?_
  · intro p hp
    have := hp2 p hp
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have hsplit : ∑ p ∈ Nat.primesBelow w, 1 / ((p : ℝ) - 1) ≤
      ∑ p ∈ Nat.primesBelow w, (1 / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
    refine Finset.sum_le_sum fun p hp => le_of_eq ?_
    have := hp2 p hp
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (p : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  have hsum2 : ∑ p ∈ Nat.primesBelow w, 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.Icc 2 w) ?_ ?_)
      (PrimeCarleson.Proof.Common.sum_Icc_inv_mul_pred_le_one w)
    · intro p hp
      rw [Finset.mem_Icc]
      exact ⟨Nat.two_le_of_mem_primesBelow hp, (Nat.lt_of_mem_primesBelow hp).le⟩
    · intro n hn _
      have : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      positivity
  have hmert := PrimeCarleson.Proof.Common.sum_primesBelow_inv_le_log_log hw
  rw [Finset.sum_add_distrib] at hsplit
  have hlogw : 0 < Real.log w := Real.log_pos (by exact_mod_cast hw)
  calc Real.exp (∑ p ∈ Nat.primesBelow w, 1 / ((p : ℝ) - 1))
      ≤ Real.exp (Real.log (Real.log w) + 5) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp 5 * Real.log w := by
      rw [Real.exp_add, Real.exp_log hlogw, mul_comm]

/-- `0 ≤ Λ_{C,w} ≤ e⁵ log w` for `w ≥ 2`. -/
theorem cramerModel_le (w : ℕ) (hw : 2 ≤ w) (n : ℤ) :
    cramerModel w n ≤ Real.exp 5 * Real.log w := by
  unfold cramerModel
  split_ifs
  · exact primorialBelow_div_totient_le w hw
  · exact mul_nonneg (Real.exp_pos 5).le
      (Real.log_nonneg (by exact_mod_cast hw.trans' (by norm_num)))

/-- `Λ_{C,w}² = (P/φ(P)) Λ_{C,w}`. -/
theorem cramerModel_mul_self (w : ℕ) (n : ℤ) :
    cramerModel w n * cramerModel w n =
      (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) * cramerModel w n := by
  unfold cramerModel
  split_ifs <;> simp

theorem mem_apSet {r : ℕ} {a : ℤ} {lo hi : ℕ} {n : ℤ} :
    n ∈ apSet r a lo hi ↔ (lo : ℤ) < n ∧ n ≤ hi ∧ n ≡ a [ZMOD r] := by
  simp [apSet, and_assoc]

/-- A residue class `v` modulo `m` has `(hi - lo)/m + θ`, `|θ| ≤ 1`, elements in `(lo, hi]`. -/
theorem abs_card_filter_modEq_sub_le {m : ℕ} (hm : 0 < m) (v : ℤ) {lo hi : ℕ} (h : lo ≤ hi) :
    |(((Finset.Ioc (lo : ℤ) hi).filter (fun n => n ≡ v [ZMOD m])).card : ℝ) -
        ((hi : ℝ) - lo) / m| ≤ 1 := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hc := Int.Ioc_filter_modEq_card (lo : ℤ) hi hm' v
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hxy : (((lo : ℤ) : ℚ) - v) / ((m : ℤ) : ℚ) ≤ (((hi : ℤ) : ℚ) - v) / ((m : ℤ) : ℚ) := by
    refine div_le_div_of_nonneg_right ?_ (by exact_mod_cast hmQ.le)
    have : (lo : ℚ) ≤ hi := by exact_mod_cast h
    push_cast
    linarith
  rw [max_eq_left (by have := Int.floor_le_floor hxy; omega)] at hc
  have h1 := Int.floor_le ((((hi : ℤ) : ℚ) - v) / ((m : ℤ) : ℚ))
  have h2 := Int.lt_floor_add_one ((((hi : ℤ) : ℚ) - v) / ((m : ℤ) : ℚ))
  have h3 := Int.floor_le ((((lo : ℤ) : ℚ) - v) / ((m : ℤ) : ℚ))
  have h4 := Int.lt_floor_add_one ((((lo : ℤ) : ℚ) - v) / ((m : ℤ) : ℚ))
  have key : (((Finset.Ioc (lo : ℤ) hi).filter (fun n => n ≡ v [ZMOD m])).card : ℚ) =
      (⌊(((hi : ℤ) : ℚ) - v) / ((m : ℤ) : ℚ)⌋ : ℚ) -
        (⌊(((lo : ℤ) : ℚ) - v) / ((m : ℤ) : ℚ)⌋ : ℚ) := by
    exact_mod_cast hc
  have hdiff : (((hi : ℤ) : ℚ) - v) / ((m : ℤ) : ℚ) - (((lo : ℤ) : ℚ) - v) / ((m : ℤ) : ℚ) =
      ((hi : ℚ) - lo) / m := by
    push_cast
    ring
  have hQ : |(((Finset.Ioc (lo : ℤ) hi).filter (fun n => n ≡ v [ZMOD m])).card : ℚ) -
      ((hi : ℚ) - lo) / m| ≤ 1 := by
    rw [key, ← hdiff, abs_le]
    constructor <;> linarith
  have := (Rat.cast_le (K := ℝ)).mpr hQ
  push_cast at this
  exact this

/-- The progression `{lo < n ≤ hi, n ≡ a mod r}` has `(hi - lo)/r + θ`, `|θ| ≤ 1`, elements. -/
theorem abs_card_apSet_sub_le {r : ℕ} (hr : 1 ≤ r) (a : ℤ) {lo hi : ℕ} (h : lo ≤ hi) :
    |((apSet r a lo hi).card : ℝ) - ((hi : ℝ) - lo) / r| ≤ 1 :=
  abs_card_filter_modEq_sub_le hr a h

/-- `|{n ∈ (lo, hi] : n ≡ a mod r}| ≤ (hi - lo)/r + 1`. -/
theorem card_apSet_le {r : ℕ} (hr : 1 ≤ r) (a : ℤ) {lo hi : ℕ} (h : lo ≤ hi) :
    ((apSet r a lo hi).card : ℝ) ≤ ((hi : ℝ) - lo) / r + 1 := by
  have := abs_card_apSet_sub_le hr a h
  rw [abs_le] at this
  linarith [this.2]

/-- On a progression `a mod r` with `1 ≤ r < w` and `gcd(a, r) > 1`, the Cramér model vanishes:
a prime `p ∣ gcd(a, r)` has `p ≤ r < w` and divides every element of the progression. -/
theorem cramerModel_eq_zero_of_not_coprime {r w : ℕ} (hr : 1 ≤ r) (hrw : r < w) {a : ℤ}
    (h : ¬ IsCoprime a (r : ℤ)) {lo hi : ℕ} {n : ℤ} (hn : n ∈ apSet r a lo hi) :
    cramerModel w n = 0 := by
  rw [Int.isCoprime_iff_gcd_eq_one] at h
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h
  have hpa : (p : ℤ) ∣ a := by
    have := Int.gcd_dvd_left (a := a) (b := (r : ℤ))
    exact_mod_cast (Int.natCast_dvd_natCast.mpr hpd).trans this
  have hpr : (p : ℤ) ∣ (r : ℤ) := by
    have := Int.gcd_dvd_right (a := a) (b := (r : ℤ))
    exact (Int.natCast_dvd_natCast.mpr hpd).trans this
  have hpr' : p ≤ r := Nat.le_of_dvd hr (by exact_mod_cast hpr)
  have hpn : (p : ℤ) ∣ n :=
    ((mem_apSet.mp hn).2.2.of_dvd hpr).dvd_iff.mpr hpa
  unfold cramerModel
  refine ite_eq_right_iff.mpr fun hg => ?_
  exact absurd hpn ((gcd_primorialBelow_eq_one_iff w n).mp hg p
    (Nat.mem_primesBelow.mpr ⟨by omega, hp⟩))

end PrimeCarleson.Proof.Fplus31

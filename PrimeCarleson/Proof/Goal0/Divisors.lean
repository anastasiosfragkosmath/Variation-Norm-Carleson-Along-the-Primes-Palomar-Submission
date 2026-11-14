module

public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Divisor and totient bounds

Elementary arithmetic inputs to the proof of the proposition `p:goal0` of
`sources/Variational_Carleson.tex`:

* `exists_card_divisors_le_rpow`: the divisor bound
  `τ(n) ≤ C_δ n^δ` for every `δ > 0`. Mathlib has no such statement. The proof writes
  `τ(n) = ∏_{p ∣ n} (v_p(n) + 1)` (`Nat.card_divisors`) and bounds each factor
  by `c_p (p^δ)^{v_p(n)}`, where `c_p = 1` if `p^δ ≥ 2` (then `k + 1 ≤ 2^k ≤ p^{δk}`) and
  `c_p = 2^δ / (2^δ - 1)` otherwise (Bernoulli: `(k + 1)(a - 1) ≤ a^{k + 1}` for `a = 2^δ ≤ p^δ`).
  Only the primes `p < ⌈2^{1/δ}⌉` have `c_p > 1`, so the product of the `c_p` is at most
  `(2^δ / (2^δ - 1))^{⌈2^{1/δ}⌉}`, which is the constant `C`, and `∏ (p^δ)^{v_p(n)} = n^δ`;
* `le_card_divisors_mul_totient` (Gauss's identity for `φ`; used with the totient bound
  `e:totientbound` of the main paper, L591–L593):
  `n = ∑_{e ∣ n} φ(e) ≤ τ(n) φ(n)`, because `φ(e) ∣ φ(n)` for `e ∣ n`;
* `card_divisors_le_of_dvd`: `τ(m) ≤ τ(n)` for `m ∣ n`;
* `squarefree_lcm_of_forall` and `coprime_div_of_squarefree` (Source: main paper `s:per`,
  L2091–L2096): `𝒬_B = lcm(q ∈ B)` is squarefree when every `q ∈ B`
  is, and `(d, 𝒬_B / d) = 1` for every `d ∣ 𝒬_B`.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Goal0

/-- A divisor of `n` has at most as many divisors as `n`. -/
theorem card_divisors_le_of_dvd {m n : ℕ} (hn : 0 < n) (h : m ∣ n) :
    m.divisors.card ≤ n.divisors.card :=
  Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' h)

/-- `n = ∑_{e ∣ n} φ(e) ≤ τ(n) φ(n)`. -/
theorem le_card_divisors_mul_totient (n : ℕ) : n ≤ n.divisors.card * n.totient := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  calc n = ∑ e ∈ n.divisors, e.totient := (Nat.sum_totient n).symm
    _ ≤ ∑ _e ∈ n.divisors, n.totient := Finset.sum_le_sum fun e he =>
        Nat.le_of_dvd (Nat.totient_pos.2 hn) (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors he))
    _ = n.divisors.card * n.totient := by rw [Finset.sum_const, smul_eq_mul]

/-- If `N` is squarefree and `d ∣ N`, then `(d, N / d) = 1`. -/
theorem coprime_div_of_squarefree {N d : ℕ} (hN : Squarefree N) (hd : d ∣ N) :
    d.Coprime (N / d) := by
  apply Nat.coprime_of_squarefree_mul
  rwa [Nat.mul_div_cancel' hd]

/-- The lcm of a finite family of squarefree numbers is squarefree. -/
theorem squarefree_lcm_of_forall {s : Finset ℕ} (h : ∀ q ∈ s, Squarefree q) :
    Squarefree (s.lcm id) := by
  have hne : ∀ q ∈ s, id q ≠ 0 := fun q hq => (h q hq).ne_zero
  have hlcm : s.lcm id ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨q, hq, hq0⟩
    exact hne q hq hq0
  rw [Nat.squarefree_iff_factorization_le_one hlcm]
  intro p
  rw [Finset.factorization_lcm hne]
  exact Finset.sup_le fun q hq => (h q hq).natFactorization_le_one p

/-- Bernoulli's inequality in the form `(k + 1) (a - 1) ≤ a ^ (k + 1)`, for `1 ≤ a`. -/
theorem succ_mul_sub_one_le_mul_pow {a : ℝ} (ha : 1 ≤ a) (k : ℕ) :
    ((k : ℝ) + 1) * (a - 1) ≤ a * a ^ k := by
  have h1 : 1 + k * (a - 1) ≤ a ^ k := by
    have := one_add_mul_le_pow (a := a - 1) (by linarith) k
    simpa using this
  have h2 : 1 ≤ a ^ k := one_le_pow₀ ha
  nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 h2)]

/-- `k + 1 ≤ a / (a - 1) * a ^ k` for `1 < a`. -/
theorem succ_le_div_mul_pow {a : ℝ} (ha : 1 < a) (k : ℕ) :
    (k : ℝ) + 1 ≤ a / (a - 1) * a ^ k := by
  rw [div_mul_eq_mul_div, le_div_iff₀ (sub_pos.2 ha)]
  exact succ_mul_sub_one_le_mul_pow ha.le k

theorem one_le_div_sub_one {a : ℝ} (ha : 1 < a) : 1 ≤ a / (a - 1) :=
  (one_le_div (sub_pos.2 ha)).2 (by linarith)

/-- Per-prime-power bound: `k + 1 ≤ c_p (p ^ δ) ^ k` where `c_p = 1` for the large primes
(`p ≥ ⌈2 ^ (1 / δ)⌉`) and `c_p = 2 ^ δ / (2 ^ δ - 1)` for the small ones. -/
theorem succ_le_ite_mul_rpow_pow {δ : ℝ} (hδ : 0 < δ) {p : ℕ} (hp : 2 ≤ p) (k : ℕ) :
    (k : ℝ) + 1 ≤
      (if p < ⌈(2 : ℝ) ^ (1 / δ)⌉₊ then (2 : ℝ) ^ δ / ((2 : ℝ) ^ δ - 1) else 1) *
        ((p : ℝ) ^ δ) ^ k := by
  have h2 : (1 : ℝ) < (2 : ℝ) ^ δ := Real.one_lt_rpow (by norm_num) hδ
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  split_ifs with hlt
  · have ha : (2 : ℝ) ^ δ ≤ (p : ℝ) ^ δ := Real.rpow_le_rpow (by norm_num) hp' hδ.le
    calc (k : ℝ) + 1 ≤ (2 : ℝ) ^ δ / ((2 : ℝ) ^ δ - 1) * ((2 : ℝ) ^ δ) ^ k :=
          succ_le_div_mul_pow h2 k
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ha k)
          (zero_le_one.trans (one_le_div_sub_one h2))
  · have hM : ⌈(2 : ℝ) ^ (1 / δ)⌉₊ ≤ p := not_lt.1 hlt
    have hq : (2 : ℝ) ^ (1 / δ) ≤ p :=
      (Nat.le_ceil _).trans (by exact_mod_cast hM)
    have h3 : (2 : ℝ) ≤ (p : ℝ) ^ δ := by
      calc (2 : ℝ) = ((2 : ℝ) ^ (1 / δ)) ^ δ := by
            rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hδ.ne', Real.rpow_one]
        _ ≤ (p : ℝ) ^ δ := Real.rpow_le_rpow (by positivity) hq hδ.le
    have h4 : (k : ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
    rw [one_mul]
    exact h4.trans (pow_le_pow_left₀ (by norm_num) h3 k)

/-- The divisor bound `τ(n) ≤ C_δ n^δ`. -/
theorem exists_card_divisors_le_rpow {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ := by
  have h2 : (1 : ℝ) < (2 : ℝ) ^ δ := Real.one_lt_rpow (by norm_num) hδ
  have hC₀ := one_le_div_sub_one h2
  refine ⟨((2 : ℝ) ^ δ / ((2 : ℝ) ^ δ - 1)) ^ ⌈(2 : ℝ) ^ (1 / δ)⌉₊, one_le_pow₀ hC₀,
    fun n hn => ?_⟩
  have hn0 : n ≠ 0 := hn.ne'
  rw [Nat.card_divisors hn0]
  push_cast
  have hprod : ∏ p ∈ n.primeFactors, ((p : ℝ) ^ δ) ^ n.factorization p = (n : ℝ) ^ δ := by
    have e : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
      exact_mod_cast Nat.prod_primeFactors_pow_factorization hn0
    calc ∏ p ∈ n.primeFactors, ((p : ℝ) ^ δ) ^ n.factorization p
        = (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) ^ δ := by
          rw [← Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
          refine Finset.prod_congr rfl fun p _ => ?_
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
            ← Real.rpow_mul (by positivity), mul_comm]
      _ = (n : ℝ) ^ δ := by rw [← e]
  have hc : ∏ p ∈ n.primeFactors,
      (if p < ⌈(2 : ℝ) ^ (1 / δ)⌉₊ then (2 : ℝ) ^ δ / ((2 : ℝ) ^ δ - 1) else 1) ≤
        ((2 : ℝ) ^ δ / ((2 : ℝ) ^ δ - 1)) ^ ⌈(2 : ℝ) ^ (1 / δ)⌉₊ := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    refine pow_le_pow_right₀ hC₀ ?_
    calc (n.primeFactors.filter fun p => p < ⌈(2 : ℝ) ^ (1 / δ)⌉₊).card
        ≤ (Finset.range ⌈(2 : ℝ) ^ (1 / δ)⌉₊).card :=
          Finset.card_le_card fun p hp => Finset.mem_range.2 (Finset.mem_filter.1 hp).2
      _ = _ := Finset.card_range _
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors,
        ((if p < ⌈(2 : ℝ) ^ (1 / δ)⌉₊ then (2 : ℝ) ^ δ / ((2 : ℝ) ^ δ - 1) else 1) *
          ((p : ℝ) ^ δ) ^ n.factorization p) :=
        Finset.prod_le_prod₀ (fun _ _ => by positivity) fun p hp =>
          succ_le_ite_mul_rpow_pow hδ (Nat.prime_of_mem_primeFactors hp).two_le _
    _ = (∏ p ∈ n.primeFactors,
          (if p < ⌈(2 : ℝ) ^ (1 / δ)⌉₊ then (2 : ℝ) ^ δ / ((2 : ℝ) ^ δ - 1) else 1)) *
        ∏ p ∈ n.primeFactors, ((p : ℝ) ^ δ) ^ n.factorization p := Finset.prod_mul_distrib
    _ ≤ _ := by
      rw [hprod]
      exact mul_le_mul_of_nonneg_right hc (by positivity)

end PrimeCarleson.Proof.Goal0

module

public import PrimeCarleson.Proof.KMTT.TypeI
public import PrimeCarleson.Proof.KMTT.LogScale
public import PrimeCarleson.Proof.Common.ChebyshevPrimeCount
public import PrimeCarleson.Proof.Common.EulerProductFinite
public import PrimeCarleson.Proof.Common.TotientBound

/-!
# The bound `|λ_ℓ| ≲ ⟨Log Q⟩` for the Type I weights

Source: [KMTT] `lambdad`, L857–L860, with the proof at L881–L888 (display (4.6),
[KMTT] TeX): for `1 ≤ ℓ < Q`,
`∑_{r < Q/ℓ, (ℓ, r) = 1} μ²(r)/φ(r) ≤ 4 ∑_{r ≥ 1, (ℓ, r) = 1} μ²(r) / (φ(r) r^σ)` (Rankin's trick,
`σ = 1/⟨Log Q⟩`, `r^σ ≤ 4`), the finite Euler product bound for the multiplicative function
`r ↦ 1_{(ℓ, r) = 1} μ²(r) / (φ(r) r^σ)`, and the extraction of the factor `φ(ℓ)/ℓ`
(`∏_{p ∣ ℓ} p^σ ≤ ℓ^σ ≤ 4`).

Deviation from KMTT. The printed proof bounds the Euler product by `ζ(1 + σ) ≲ 1/σ`; here
`∑_p p^(-1-σ) ≤ log log Q + O(1)` is obtained instead from Mertens' second theorem for the primes
`p < Q` and the Chebyshev tail bound (`sum_primes_le_log_log_add`) for `p ≥ Q`, which gives the same
conclusion `∏_p (1 + u_p) ≲ log Q ≲ ⟨Log Q⟩` without the Euler product for `ζ` and without the pole
bound `ζ(1 + σ) ≲ 1/σ`.
-/

@[expose] public noncomputable section

open PrimeCarleson ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

set_option autoImplicit false

namespace PrimeCarleson.Proof.KMTT

open PrimeCarleson.Proof.Common

/-- The Rankin series summand `1_{(ℓ, r) = 1} μ²(r) / (φ(r) r^σ)`. -/
def rankinTerm (ℓ : ℕ) (σ : ℝ) (r : ℕ) : ℝ :=
  if Nat.Coprime ℓ r then (μ r : ℝ) ^ 2 / ((Nat.totient r : ℝ) * (r : ℝ) ^ σ) else 0

/-- The Rankin summand is nonnegative. -/
theorem rankinTerm_nonneg (ℓ : ℕ) (σ : ℝ) (r : ℕ) : 0 ≤ rankinTerm ℓ σ r := by
  unfold rankinTerm
  split_ifs
  · positivity
  · exact le_rfl

/-- The Rankin summand at `r = 1` is `1`. -/
theorem rankinTerm_one (ℓ : ℕ) (σ : ℝ) : rankinTerm ℓ σ 1 = 1 := by
  simp [rankinTerm]

/-- The Rankin summand is multiplicative on coprime arguments. -/
theorem rankinTerm_mul (ℓ : ℕ) (σ : ℝ) {m n : ℕ} (h : Nat.Coprime m n) :
    rankinTerm ℓ σ (m * n) = rankinTerm ℓ σ m * rankinTerm ℓ σ n := by
  unfold rankinTerm
  have h1 : (μ (m * n) : ℝ) = (μ m : ℝ) * (μ n : ℝ) := by
    have := isMultiplicative_moebius.map_mul_of_coprime h
    exact_mod_cast this
  have h2 : (Nat.totient (m * n) : ℝ) = (Nat.totient m : ℝ) * (Nat.totient n : ℝ) := by
    exact_mod_cast Nat.totient_mul h
  by_cases hm : Nat.Coprime ℓ m <;> by_cases hn : Nat.Coprime ℓ n
  · have hmn : Nat.Coprime ℓ (m * n) := Nat.Coprime.mul_right hm hn
    simp only [Nat.Coprime] at hm hn hmn ⊢
    simp only [hm, hn, hmn, ↓reduceIte]
    rw [h1, h2, Nat.cast_mul]
    by_cases hm0 : m = 0
    · subst hm0; simp
    by_cases hn0 : n = 0
    · subst hn0; simp
    have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
    have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
    rw [Real.mul_rpow hmr.le hnr.le]
    rw [div_mul_div_comm]
    congr 1
    · ring
    · ring
  · have : ¬ Nat.Coprime ℓ (m * n) := fun hc => hn (Nat.Coprime.coprime_mul_left_right hc)
    simp [hn, this]
  · have : ¬ Nat.Coprime ℓ (m * n) := fun hc => hm (Nat.Coprime.coprime_mul_right_right hc)
    simp [hm, this]
  · have : ¬ Nat.Coprime ℓ (m * n) := fun hc => hm (Nat.Coprime.coprime_mul_right_right hc)
    simp [hm, this]

/-- The Rankin summand vanishes at `p^a` for `a ≥ 2` (`μ(p^a) = 0`). -/
theorem rankinTerm_prime_pow_of_two_le (ℓ : ℕ) (σ : ℝ) {p : ℕ} (hp : p.Prime) {a : ℕ}
    (ha : 2 ≤ a) : rankinTerm ℓ σ (p ^ a) = 0 := by
  have h : μ (p ^ a) = 0 := by
    rw [moebius_apply_prime_pow hp (by omega)]
    simp only [show a ≠ 1 by omega, ↓reduceIte]
  simp [rankinTerm, h]

/-- The Rankin summand at a prime `p`: `1_{p ∤ ℓ} / ((p - 1) p^σ)`. -/
theorem rankinTerm_prime (ℓ : ℕ) (σ : ℝ) {p : ℕ} (hp : p.Prime) :
    rankinTerm ℓ σ p =
      if p ∣ ℓ then 0 else 1 / (((p : ℝ) - 1) * (p : ℝ) ^ σ) := by
  have hcop : Nat.Coprime ℓ p ↔ ¬ p ∣ ℓ := by
    rw [Nat.coprime_comm]; exact hp.coprime_iff_not_dvd
  have hμ : (μ p : ℝ) ^ 2 = 1 := by
    rw [moebius_apply_prime hp]; norm_num
  have hφ : (Nat.totient p : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le]; simp
  unfold rankinTerm
  by_cases h : p ∣ ℓ
  · have : ¬ Nat.Coprime ℓ p := fun hc => (hcop.mp hc) h
    simp [h, this]
  · have : Nat.Coprime ℓ p := hcop.mpr h
    simp only [Nat.Coprime] at this ⊢
    simp only [this, hμ, hφ, ↓reduceIte, h]

/-- The Rankin summand along `a ↦ p^a` has finite support. -/
theorem summable_rankinTerm_prime_pow (ℓ : ℕ) (σ : ℝ) {p : ℕ} (hp : p.Prime) :
    Summable fun a : ℕ => rankinTerm ℓ σ (p ^ a) := by
  refine summable_of_ne_finset_zero (s := Finset.range 2) fun a ha => ?_
  exact rankinTerm_prime_pow_of_two_le ℓ σ hp (by have := Finset.mem_range.not.mp ha; omega)

/-- The Euler factor of the Rankin series at `p`: `1 + 1_{p ∤ ℓ} / ((p - 1) p^σ)`. -/
theorem tsum_rankinTerm_prime_pow (ℓ : ℕ) (σ : ℝ) {p : ℕ} (hp : p.Prime) :
    ∑' a : ℕ, rankinTerm ℓ σ (p ^ a) = 1 + rankinTerm ℓ σ p := by
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, rankinTerm_one]
  · intro a ha
    exact rankinTerm_prime_pow_of_two_le ℓ σ hp (by have := Finset.mem_range.not.mp ha; omega)

/-- Finite Euler product for the Rankin series: `∑_{r ≤ M} 1_{(ℓ, r) = 1} μ²(r)/(φ(r) r^σ)
≤ ∏_{p ≤ M} (1 + 1_{p ∤ ℓ} / ((p - 1) p^σ))` ([KMTT], L881–L886). -/
theorem sum_rankinTerm_le_prod (ℓ : ℕ) (σ : ℝ) (M : ℕ) :
    ∑ r ∈ Finset.Icc 1 M, rankinTerm ℓ σ r ≤
      ∏ p ∈ (M + 1).primesBelow, (1 + rankinTerm ℓ σ p) := by
  refine (sum_Icc_le_prod_primesBelow (rankinTerm_nonneg ℓ σ) (rankinTerm_one ℓ σ)
    (fun h => rankinTerm_mul ℓ σ h) (fun hp => summable_rankinTerm_prime_pow ℓ σ hp) M).trans ?_
  refine le_of_eq (Finset.prod_congr rfl fun p hp => ?_)
  exact tsum_rankinTerm_prime_pow ℓ σ (Nat.prime_of_mem_primesBelow hp)

/-- The local factor `u_p = 1 / ((p - 1) p^σ)` of the Rankin series. -/
def rankinLocal (σ : ℝ) (p : ℕ) : ℝ := 1 / (((p : ℝ) - 1) * (p : ℝ) ^ σ)

/-- The local factor `u_p = 1 / ((p - 1) p^σ)` is nonnegative. -/
theorem rankinLocal_nonneg (σ : ℝ) {p : ℕ} (hp : p.Prime) : 0 ≤ rankinLocal σ p := by
  have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  unfold rankinLocal
  have : 0 ≤ (p : ℝ) - 1 := by linarith
  positivity

/-- Removing the condition `(ℓ, r) = 1`: each prime `p ∣ ℓ` costs the factor
`(p - 1) p^σ / p` (`1 ≤ (1 + u_p) (p - 1) p^σ / p`). -/
theorem one_add_rankinTerm_le {ℓ : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) {p : ℕ} (hp : p.Prime) :
    1 + rankinTerm ℓ σ p ≤
      (1 + rankinLocal σ p) * (if p ∣ ℓ then ((p : ℝ) - 1) * (p : ℝ) ^ σ / p else 1) := by
  rw [rankinTerm_prime ℓ σ hp]
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpσ : (1 : ℝ) ≤ (p : ℝ) ^ σ := Real.one_le_rpow h1.le hσ
  have hpσ0 : (0 : ℝ) < (p : ℝ) ^ σ := by linarith
  by_cases h : p ∣ ℓ
  · simp only [h, ↓reduceIte]
    unfold rankinLocal
    have hne : ((p : ℝ) - 1) * (p : ℝ) ^ σ ≠ 0 := by
      have : 0 < ((p : ℝ) - 1) * (p : ℝ) ^ σ := mul_pos (by linarith) hpσ0
      exact this.ne'
    rw [add_zero, ← sub_nonneg]
    have e : (1 + 1 / (((p : ℝ) - 1) * (p : ℝ) ^ σ)) * (((p : ℝ) - 1) * (p : ℝ) ^ σ / p) - 1 =
        (((p : ℝ) - 1) * (p : ℝ) ^ σ + 1 - p) / p := by
      field_simp
    rw [e]
    apply div_nonneg _ hp0.le
    nlinarith
  · simp only [h, ↓reduceIte]
    unfold rankinLocal
    ring_nf
    exact le_rfl

/-- The factor extracted from the primes dividing `ℓ`:
`∏_{p ∣ ℓ} (p - 1) p^σ / p = (φ(ℓ)/ℓ) (∏_{p ∣ ℓ} p)^σ`. -/
theorem prod_primeFactors_term {ℓ : ℕ} (hℓ : 0 < ℓ) (σ : ℝ) :
    ∏ p ∈ ℓ.primeFactors, (((p : ℝ) - 1) * (p : ℝ) ^ σ / p) =
      (Nat.totient ℓ : ℝ) / ℓ * (∏ p ∈ ℓ.primeFactors, (p : ℝ)) ^ σ := by
  have hpos : ∀ p ∈ ℓ.primeFactors, (0 : ℝ) < p := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hP : (0 : ℝ) < ∏ p ∈ ℓ.primeFactors, (p : ℝ) := Finset.prod_pos hpos
  have key : (Nat.totient ℓ : ℝ) * ∏ p ∈ ℓ.primeFactors, (p : ℝ) =
      ℓ * ∏ p ∈ ℓ.primeFactors, ((p : ℝ) - 1) := by
    have := Nat.totient_mul_prod_primeFactors ℓ
    have h2 := congrArg (fun x : ℕ => (x : ℝ)) this
    simp only [Nat.cast_mul, Nat.cast_prod] at h2
    rw [h2]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le]; simp
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Real.finsetProd_rpow _ _
    (fun p hp => (hpos p hp).le)]
  have hℓ' : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hAP : (∏ p ∈ ℓ.primeFactors, ((p : ℝ) - 1)) / ∏ p ∈ ℓ.primeFactors, (p : ℝ) =
      (Nat.totient ℓ : ℝ) / ℓ := by
    rw [div_eq_div_iff hP.ne' hℓ']
    linarith [key]
  rw [← hAP]
  ring

/-- The finite Euler product bound with the factor `φ(ℓ)/ℓ` extracted (for `ℓ ≤ M`). -/
theorem sum_rankinTerm_le {ℓ M : ℕ} (hℓ : 0 < ℓ) (hℓM : ℓ ≤ M) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∑ r ∈ Finset.Icc 1 M, rankinTerm ℓ σ r ≤
      (∏ p ∈ (M + 1).primesBelow, (1 + rankinLocal σ p)) *
        ((Nat.totient ℓ : ℝ) / ℓ * (∏ p ∈ ℓ.primeFactors, (p : ℝ)) ^ σ) := by
  refine (sum_rankinTerm_le_prod ℓ σ M).trans ?_
  have h1 : ∏ p ∈ (M + 1).primesBelow, (1 + rankinTerm ℓ σ p) ≤
      ∏ p ∈ (M + 1).primesBelow, ((1 + rankinLocal σ p) *
        (if p ∣ ℓ then ((p : ℝ) - 1) * (p : ℝ) ^ σ / p else 1)) := by
    refine Finset.prod_le_prod₀ (fun p hp => ?_) fun p hp => ?_
    · have := rankinTerm_nonneg ℓ σ p; linarith
    · exact one_add_rankinTerm_le hσ (Nat.prime_of_mem_primesBelow hp)
  refine h1.trans (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, ← prod_primeFactors_term hℓ σ]
  congr 1
  rw [← Finset.prod_filter]
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext p
  simp only [Finset.mem_filter, Nat.mem_primesBelow, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨_, hpp⟩, hpl⟩
    exact ⟨hpp, hpl, hℓ.ne'⟩
  · rintro ⟨hpp, hpl, -⟩
    exact ⟨⟨by have := Nat.le_of_dvd hℓ hpl; omega, hpp⟩, hpl⟩

/-- `∑_{p ≤ M} 1 / ((p - 1) p^σ) ≤ log log Q + 65` for `σ = 1 / ⟨Log Q⟩` and `Q ≥ 8`: Mertens'
second theorem for the primes `p < Q` and the Chebyshev tail bound for `p ≥ Q`. -/
theorem sum_rankinLocal_le {Q : ℝ} (hQ : 8 ≤ Q) (M : ℕ) :
    ∑ p ∈ (M + 1).primesBelow, rankinLocal (1 / logBracket Q) p ≤
      Real.log (Real.log Q) + 65 := by
  set σ : ℝ := 1 / logBracket Q with hσdef
  have hL := logBracket_pos Q
  have hσ : 0 < σ := by positivity
  have hσ1 : σ ≤ 1 := by
    rw [hσdef, div_le_one hL]; exact one_le_logBracket Q
  have hσQ : 1 / 2 ≤ σ * Real.log Q := half_le_inv_logBracket_mul_log hQ
  have hprime : ∀ p ∈ (M + 1).primesBelow, p.Prime := fun p hp => Nat.prime_of_mem_primesBelow hp
  have hsplit : ∀ p ∈ (M + 1).primesBelow, rankinLocal σ p =
      (p : ℝ) ^ (-σ) / p + (p : ℝ) ^ (-σ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hp
    have h1 : (1 : ℝ) < p := by exact_mod_cast (hprime p hp).one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hpσ : (0 : ℝ) < (p : ℝ) ^ σ := Real.rpow_pos_of_pos hp0 _
    unfold rankinLocal
    rw [Real.rpow_neg hp0.le]
    field_simp
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hA : ∑ p ∈ (M + 1).primesBelow, (p : ℝ) ^ (-σ) / p ≤ Real.log (Real.log Q) + 64 := by
    have := sum_primes_le_log_log_add (Q := Q) (σ := σ) (by linarith) hσ hσ1 hσQ
      (fun p => (p : ℝ) ^ (-σ) / p) (A := 1) (B := 1) zero_le_one zero_le_one
      (fun p hp => by
        have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
        have : (p : ℝ) ^ (-σ) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos h1.le (by linarith)
        rw [div_le_div_iff_of_pos_right (by linarith)]
        exact this)
      (fun p _ => by rw [one_mul])
      ((M + 1).primesBelow) hprime
    linarith
  have hB : ∑ p ∈ (M + 1).primesBelow, (p : ℝ) ^ (-σ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
    calc ∑ p ∈ (M + 1).primesBelow, (p : ℝ) ^ (-σ) / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ ∑ p ∈ (M + 1).primesBelow, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have h1 : (1 : ℝ) < p := by exact_mod_cast (hprime p hp).one_lt
          have : (p : ℝ) ^ (-σ) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos h1.le (by linarith)
          have hpos : 0 < (p : ℝ) * ((p : ℝ) - 1) := mul_pos (by linarith) (by linarith)
          exact div_le_div_of_nonneg_right this hpos.le
      _ ≤ ∑ n ∈ Finset.Icc 2 M, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n hn _ => ?_
          · intro p hp
            rw [Nat.mem_primesBelow] at hp
            exact Finset.mem_Icc.mpr ⟨hp.2.two_le, by omega⟩
          · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
            have : 0 < (n : ℝ) * ((n : ℝ) - 1) := mul_pos (by linarith) (by linarith)
            positivity
      _ ≤ 1 := sum_Icc_inv_mul_pred_le_one M
  linarith

/-- Rankin's trick ([KMTT], L881–L886): the restricted sum over `r < Q/ℓ` is at
most `4` times the full Rankin series up to `⌈Q⌉`. -/
theorem sum_filter_le_rankin {Q : ℝ} (hQ : 1 ≤ Q) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ∑ r ∈ (Finset.Icc 1 ⌈Q⌉₊).filter (fun r : ℕ => Nat.Coprime ℓ r ∧ (r : ℝ) < Q / ℓ),
        (μ r : ℝ) ^ 2 / (Nat.totient r : ℝ) ≤
      4 * ∑ r ∈ Finset.Icc 1 ⌈Q⌉₊, rankinTerm ℓ (1 / logBracket Q) r := by
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  calc ∑ r ∈ (Finset.Icc 1 ⌈Q⌉₊).filter (fun r : ℕ => Nat.Coprime ℓ r ∧ (r : ℝ) < Q / ℓ),
        (μ r : ℝ) ^ 2 / (Nat.totient r : ℝ)
      ≤ ∑ r ∈ (Finset.Icc 1 ⌈Q⌉₊).filter (fun r : ℕ => Nat.Coprime ℓ r ∧ (r : ℝ) < Q / ℓ),
        4 * rankinTerm ℓ (1 / logBracket Q) r := by
        refine Finset.sum_le_sum fun r hr => ?_
        rw [Finset.mem_filter, Finset.mem_Icc] at hr
        obtain ⟨⟨hr1, -⟩, hcop, hrQ⟩ := hr
        have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
        have hrQ' : (r : ℝ) ≤ Q := by
          have : Q / ℓ ≤ Q := div_le_self (by linarith) hℓ'
          linarith
        have h4 := rpow_inv_logBracket_le_four hQ hr0.le hrQ'
        have hpos : (0 : ℝ) < (r : ℝ) ^ (1 / logBracket Q) := Real.rpow_pos_of_pos hr0 _
        have hX : 0 ≤ (μ r : ℝ) ^ 2 / (Nat.totient r : ℝ) := by positivity
        have e : rankinTerm ℓ (1 / logBracket Q) r =
            (μ r : ℝ) ^ 2 / (Nat.totient r : ℝ) / (r : ℝ) ^ (1 / logBracket Q) := by
          simp only [rankinTerm, Nat.Coprime] at hcop ⊢
          simp only [hcop, ↓reduceIte, div_div]
        rw [e, ← mul_div_assoc, le_div_iff₀ hpos]
        nlinarith
    _ = 4 * ∑ r ∈ (Finset.Icc 1 ⌈Q⌉₊).filter
          (fun r : ℕ => Nat.Coprime ℓ r ∧ (r : ℝ) < Q / ℓ),
          rankinTerm ℓ (1 / logBracket Q) r := by rw [Finset.mul_sum]
    _ ≤ 4 * ∑ r ∈ Finset.Icc 1 ⌈Q⌉₊, rankinTerm ℓ (1 / logBracket Q) r := by
        gcongr
        · exact fun r _ _ => rankinTerm_nonneg _ _ _
        · exact Finset.filter_subset _ _

/-- `|λ_ℓ| ≤ 32 e^65 ⟨Log Q⟩` for `Q ≥ 8` and `1 ≤ ℓ < Q` ([KMTT] `lambdad`, L857–L860). -/
theorem abs_typeIWeight_le_of_eight_le {Q : ℝ} (hQ : 8 ≤ Q) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hℓQ : (ℓ : ℝ) < Q) : |typeIWeight Q ℓ| ≤ 32 * Real.exp 65 * logBracket Q := by
  have hQ1 : 1 ≤ Q := by linarith
  set σ : ℝ := 1 / logBracket Q with hσdef
  have hL := logBracket_pos Q
  have hσ : 0 ≤ σ := by positivity
  set M : ℕ := ⌈Q⌉₊ with hM
  have hℓM : ℓ ≤ M := by
    have : (ℓ : ℝ) ≤ M := hℓQ.le.trans (Nat.le_ceil Q)
    exact_mod_cast this
  have hℓpos : 0 < ℓ := hℓ
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
  have hφ : (0 : ℝ) < (Nat.totient ℓ : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hℓpos
  -- the three factors
  have hE := sum_rankinTerm_le hℓpos hℓM hσ
  have hS := sum_filter_le_rankin hQ1 hℓ
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hP : ∏ p ∈ (M + 1).primesBelow, (1 + rankinLocal σ p) ≤
      Real.log Q * Real.exp 65 := by
    refine (prod_one_add_le_exp_sum _ _ fun p hp => rankinLocal_nonneg σ
      (Nat.prime_of_mem_primesBelow hp)).trans ?_
    calc Real.exp (∑ p ∈ (M + 1).primesBelow, rankinLocal σ p)
        ≤ Real.exp (Real.log (Real.log Q) + 65) := Real.exp_le_exp.mpr (sum_rankinLocal_le hQ M)
      _ = Real.log Q * Real.exp 65 := by rw [Real.exp_add, Real.exp_log hlogQ]
  have hP0 : 0 ≤ ∏ p ∈ (M + 1).primesBelow, (1 + rankinLocal σ p) :=
    Finset.prod_nonneg fun p hp => by
      have := rankinLocal_nonneg σ (Nat.prime_of_mem_primesBelow hp); linarith
  have hPi : (∏ p ∈ ℓ.primeFactors, (p : ℝ)) ^ σ ≤ 4 := by
    have h1 : (∏ p ∈ ℓ.primeFactors, (p : ℝ)) ≤ ℓ := by
      have h := (Nat.cast_le (α := ℝ)).mpr (Nat.le_of_dvd hℓpos (Nat.prod_primeFactors_dvd ℓ))
      rwa [Nat.cast_prod] at h
    have h0 : 0 ≤ ∏ p ∈ ℓ.primeFactors, (p : ℝ) := Finset.prod_nonneg fun p _ => Nat.cast_nonneg p
    calc (∏ p ∈ ℓ.primeFactors, (p : ℝ)) ^ σ ≤ (ℓ : ℝ) ^ σ := Real.rpow_le_rpow h0 h1 hσ
      _ ≤ 4 := rpow_inv_logBracket_le_four hQ1 hℓr.le hℓQ.le
  have hPi0 : 0 ≤ (∏ p ∈ ℓ.primeFactors, (p : ℝ)) ^ σ :=
    Real.rpow_nonneg (Finset.prod_nonneg fun p _ => Nat.cast_nonneg p) _
  -- the weight
  have hSnn : 0 ≤ ∑ r ∈ (Finset.Icc 1 ⌈Q⌉₊).filter
      (fun r : ℕ => Nat.Coprime ℓ r ∧ (r : ℝ) < Q / ℓ),
      (μ r : ℝ) ^ 2 / (Nat.totient r : ℝ) :=
    Finset.sum_nonneg fun r _ => by positivity
  have hμ : |(μ ℓ : ℝ)| ≤ 1 := by
    have := abs_moebius_le_one (n := ℓ)
    exact_mod_cast this
  have hcoef : |(μ ℓ : ℝ) * ℓ / (Nat.totient ℓ : ℝ)| ≤ (ℓ : ℝ) / (Nat.totient ℓ : ℝ) := by
    rw [abs_div, abs_mul, abs_of_pos hℓr, abs_of_pos hφ]
    gcongr
    calc |(μ ℓ : ℝ)| * (ℓ : ℝ) ≤ 1 * ℓ := by gcongr
      _ = ℓ := one_mul _
  unfold typeIWeight
  rw [abs_mul, abs_of_nonneg hSnn]
  have hfinal : ∑ r ∈ (Finset.Icc 1 ⌈Q⌉₊).filter
      (fun r : ℕ => Nat.Coprime ℓ r ∧ (r : ℝ) < Q / ℓ), (μ r : ℝ) ^ 2 / (Nat.totient r : ℝ) ≤
        4 * ((Real.log Q * Real.exp 65) * ((Nat.totient ℓ : ℝ) / ℓ * 4)) := by
    refine hS.trans ?_
    gcongr
    refine hE.trans ?_
    gcongr
  have hlog := log_le_two_mul_logBracket hQ1
  calc |(μ ℓ : ℝ) * ℓ / (Nat.totient ℓ : ℝ)| * ∑ r ∈ (Finset.Icc 1 ⌈Q⌉₊).filter
        (fun r : ℕ => Nat.Coprime ℓ r ∧ (r : ℝ) < Q / ℓ), (μ r : ℝ) ^ 2 / (Nat.totient r : ℝ)
      ≤ ((ℓ : ℝ) / (Nat.totient ℓ : ℝ)) *
        (4 * ((Real.log Q * Real.exp 65) * ((Nat.totient ℓ : ℝ) / ℓ * 4))) := by
        gcongr
    _ = 16 * (Real.log Q * Real.exp 65) := by field_simp; ring
    _ ≤ 16 * ((2 * logBracket Q) * Real.exp 65) := by gcongr
    _ = 32 * Real.exp 65 * logBracket Q := by ring

/-- The crude bound `|λ_ℓ| ≤ 64` for `Q < 8` and `1 ≤ ℓ < Q` (the trivial range of [KMTT], L890). -/
theorem abs_typeIWeight_le_of_lt_eight {Q : ℝ} (hQ : Q < 8) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hℓQ : (ℓ : ℝ) < Q) : |typeIWeight Q ℓ| ≤ 64 := by
  have hℓpos : 0 < ℓ := hℓ
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
  have hφ1 : (1 : ℝ) ≤ (Nat.totient ℓ : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hℓpos
  have hSle : ∑ r ∈ (Finset.Icc 1 ⌈Q⌉₊).filter
      (fun r : ℕ => Nat.Coprime ℓ r ∧ (r : ℝ) < Q / ℓ),
        (μ r : ℝ) ^ 2 / (Nat.totient r : ℝ) ≤ 8 := by
    calc ∑ r ∈ (Finset.Icc 1 ⌈Q⌉₊).filter
          (fun r : ℕ => Nat.Coprime ℓ r ∧ (r : ℝ) < Q / ℓ), (μ r : ℝ) ^ 2 / (Nat.totient r : ℝ)
        ≤ ∑ r ∈ (Finset.Icc 1 ⌈Q⌉₊).filter
          (fun r : ℕ => Nat.Coprime ℓ r ∧ (r : ℝ) < Q / ℓ), (1 : ℝ) := by
          refine Finset.sum_le_sum fun r hr => ?_
          have hr1 : 1 ≤ r := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
          have hφr : (1 : ℝ) ≤ (Nat.totient r : ℝ) := by
            exact_mod_cast Nat.totient_pos.mpr (by omega)
          have hμr : (μ r : ℝ) ^ 2 ≤ 1 := by
            have := abs_moebius_le_one (n := r)
            have h2 : |(μ r : ℝ)| ≤ 1 := by exact_mod_cast this
            nlinarith [sq_abs (μ r : ℝ), abs_nonneg (μ r : ℝ)]
          rw [div_le_one (by linarith)]
          linarith
      _ ≤ ((Finset.Icc 1 ⌈Q⌉₊).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ 8 := by
          rw [Nat.card_Icc]
          have : ⌈Q⌉₊ ≤ 8 := Nat.ceil_le.mpr (by exact_mod_cast hQ.le)
          have : (⌈Q⌉₊ + 1 - 1 : ℕ) ≤ 8 := by omega
          exact_mod_cast this
  have hSnn : 0 ≤ ∑ r ∈ (Finset.Icc 1 ⌈Q⌉₊).filter
      (fun r : ℕ => Nat.Coprime ℓ r ∧ (r : ℝ) < Q / ℓ),
      (μ r : ℝ) ^ 2 / (Nat.totient r : ℝ) :=
    Finset.sum_nonneg fun r _ => by positivity
  have hμ : |(μ ℓ : ℝ)| ≤ 1 := by
    have := abs_moebius_le_one (n := ℓ)
    exact_mod_cast this
  have hcoef : |(μ ℓ : ℝ) * ℓ / (Nat.totient ℓ : ℝ)| ≤ 8 := by
    rw [abs_div, abs_mul, abs_of_pos hℓr, abs_of_pos (by linarith : (0 : ℝ) < Nat.totient ℓ)]
    rw [div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg (μ ℓ : ℝ)]
  unfold typeIWeight
  rw [abs_mul, abs_of_nonneg hSnn]
  nlinarith [abs_nonneg ((μ ℓ : ℝ) * ℓ / (Nat.totient ℓ : ℝ))]

/-- `|λ_ℓ| ≤ 32 e^65 ⟨Log Q⟩` for every `Q ≥ 1` and `1 ≤ ℓ < Q` (KMTT (4.6), L857–L860). -/
theorem abs_typeIWeight_le {Q : ℝ} {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hℓQ : (ℓ : ℝ) < Q) :
    |typeIWeight Q ℓ| ≤ 32 * Real.exp 65 * logBracket Q := by
  rcases le_or_gt 8 Q with h8 | h8
  · exact abs_typeIWeight_le_of_eight_le h8 hℓ hℓQ
  · refine (abs_typeIWeight_le_of_lt_eight h8 hℓ hℓQ).trans ?_
    have h1 := one_le_logBracket Q
    have h2 : (64 : ℝ) ≤ 32 * Real.exp 65 := by
      have : (2 : ℝ) ≤ Real.exp 65 := by
        have := Real.add_one_le_exp (65 : ℝ); linarith
      linarith
    nlinarith

/-- The pointwise bound (KMTT (4.7), `lambdaq-bound`, L861–L866):
`|Λ_{HB,Q}(n)| ≤ 32 e^65 τ(n, Q) ⟨Log Q⟩` for every real `Q` and every `n ≥ 1`. -/
theorem norm_blockWeight_hbIndex_le (Q : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖blockWeight (hbIndex Q) (n : ℤ)‖ ≤
      32 * Real.exp 65 * logBracket Q * (truncDivisor n Q : ℝ) := by
  rw [blockWeight_hbIndex_eq Q hn]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ ℓ ∈ n.divisors.filter (fun l : ℕ => (l : ℝ) < Q), ‖(typeIWeight Q ℓ : ℂ)‖
      ≤ ∑ _ℓ ∈ n.divisors.filter (fun l : ℕ => (l : ℝ) < Q),
        32 * Real.exp 65 * logBracket Q := by
        refine Finset.sum_le_sum fun ℓ hℓ => ?_
        rw [Finset.mem_filter] at hℓ
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_typeIWeight_le (Nat.pos_of_mem_divisors hℓ.1) hℓ.2
    _ = 32 * Real.exp 65 * logBracket Q * (truncDivisor n Q : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]; rfl

end PrimeCarleson.Proof.KMTT

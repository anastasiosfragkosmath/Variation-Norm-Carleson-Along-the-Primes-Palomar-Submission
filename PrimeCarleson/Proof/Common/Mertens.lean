module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Analysis.SpecialFunctions.Log.Sum

/-!
# Mertens' theorems (upper bounds)

The two elementary prime-sum estimates behind the totient bound of
`sources/Variational_Carleson.tex` L589-L593 (Source: main paper `e:totientbound`, L591–L593; the
totient bound itself is in `PrimeCarleson.Proof.Common.TotientBound`), with explicit absolute
constants:

* `sum_primesLE_log_div_le`: Mertens' first theorem,
  `∑_{p ≤ n} log p / p ≤ log n + log 4` for every natural number `n`;
* `sum_inv_prime_le_log_log`, `sum_primesLE_inv_le_log_log`, `sum_primesBelow_inv_le_log_log`:
  Mertens' second theorem, `∑_{p ≤ x} 1 / p ≤ log log x + 4` for every real `x ≥ 2`, and for
  `∑_{p < Q}` with `Q` a natural number `≥ 2`.

The proof of the first estimate is Legendre's formula `log n! = ∑_{d ≤ n} Λ(d) ⌊n/d⌋`
(`log_factorial_eq_sum_vonMangoldt`) with `n! ≤ nⁿ` and Chebyshev's `θ(n) ≤ n log 4`
(`Chebyshev.theta_le_log4_mul_x`). The second follows by (discrete) partial summation
(`sum_Icc_mul_eq_abel`) with the weight `1 / log k`.
-/

@[expose] public noncomputable section

open Finset
open scoped Nat.Prime

set_option autoImplicit false

namespace PrimeCarleson.Proof.Common

/-- Legendre's formula in the form `log n! = ∑_{d ≤ n} Λ(d) ⌊n / d⌋`. -/
theorem log_factorial_eq_sum_vonMangoldt (n : ℕ) :
    Real.log (Nat.factorial n : ℕ) =
      ∑ d ∈ Ioc 0 n, ArithmeticFunction.vonMangoldt d * ((n / d : ℕ) : ℝ) := by
  rw [← Real.sum_log_eq_log_factorial]
  have h1 : ∀ k ∈ Ioc 0 n,
      Real.log (k : ℝ) = ∑ d ∈ k.divisors, ArithmeticFunction.vonMangoldt d :=
    fun k _ => ArithmeticFunction.vonMangoldt_sum.symm
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_comm' (t' := Ioc 0 n) (s' := fun d => {k ∈ Ioc 0 n | d ∣ k})
    (f := fun _ d => ArithmeticFunction.vonMangoldt d)]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, mul_comm]
  · intro k d
    simp only [Finset.mem_Ioc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hk0, hkn⟩, hdk, hk⟩
      exact ⟨⟨⟨hk0, hkn⟩, hdk⟩, Nat.pos_of_dvd_of_pos hdk hk0, (Nat.le_of_dvd hk0 hdk).trans hkn⟩
    · rintro ⟨⟨⟨hk0, hkn⟩, hdk⟩, _, _⟩
      exact ⟨⟨hk0, hkn⟩, hdk, hk0.ne'⟩

/-- Mertens' first theorem (upper bound) for a natural number `n`:
`∑_{p ≤ n} log p / p ≤ log n + log 4`. -/
theorem sum_primesLE_log_div_le (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.primesLE_zero, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ∀ p ∈ Nat.primesLE n, (n : ℝ) * (Real.log p / p) ≤
      Real.log p * ((n / p : ℕ) : ℝ) + Real.log p := by
    intro p hp
    have hp' := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.pos
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp'.one_lt.le)
    have hdiv : (n : ℝ) / p ≤ ((n / p : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hp0]
      have h := Nat.lt_div_mul_add (a := n) hp'.pos
      have h' : (n : ℝ) < ((n / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
      nlinarith
    calc (n : ℝ) * (Real.log p / p) = Real.log p * ((n : ℝ) / p) := by ring
      _ ≤ Real.log p * (((n / p : ℕ) : ℝ) + 1) := by gcongr
      _ = Real.log p * ((n / p : ℕ) : ℝ) + Real.log p := by ring
  have h2 : ∑ p ∈ Nat.primesLE n, Real.log p * ((n / p : ℕ) : ℝ) ≤
      Real.log (Nat.factorial n : ℕ) := by
    rw [log_factorial_eq_sum_vonMangoldt]
    calc ∑ p ∈ Nat.primesLE n, Real.log p * ((n / p : ℕ) : ℝ)
        = ∑ p ∈ Nat.primesLE n, ArithmeticFunction.vonMangoldt p * ((n / p : ℕ) : ℝ) :=
          Finset.sum_congr rfl fun p hp => by
            rw [ArithmeticFunction.vonMangoldt_apply_prime (Nat.prime_of_mem_primesLE hp)]
      _ ≤ ∑ d ∈ Ioc 0 n, ArithmeticFunction.vonMangoldt d * ((n / d : ℕ) : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun d _ _ => by positivity
          intro p hp
          have := Nat.mem_primesLE.mp hp
          exact Finset.mem_Ioc.mpr ⟨this.2.pos, this.1⟩
  have h3 : ∑ p ∈ Nat.primesLE n, Real.log p ≤ Real.log 4 * n := by
    have := Chebyshev.theta_le_log4_mul_x (x := (n : ℝ)) (Nat.cast_nonneg n)
    rwa [Chebyshev.theta_eq_sum_primesLE_log] at this
  have h4 : Real.log (Nat.factorial n : ℕ) ≤ n * Real.log n := by
    calc Real.log (Nat.factorial n : ℕ) ≤ Real.log ((n : ℝ) ^ n) :=
          Real.log_le_log (by exact_mod_cast Nat.factorial_pos n)
            (by exact_mod_cast Nat.factorial_le_pow n)
      _ = n * Real.log n := Real.log_pow n _
  have h5 : (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p ≤
      (n : ℝ) * (Real.log n + Real.log 4) := by
    calc (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p
        = ∑ p ∈ Nat.primesLE n, (n : ℝ) * (Real.log p / p) := Finset.mul_sum _ _ _
      _ ≤ ∑ p ∈ Nat.primesLE n, (Real.log p * ((n / p : ℕ) : ℝ) + Real.log p) :=
          Finset.sum_le_sum h1
      _ = ∑ p ∈ Nat.primesLE n, Real.log p * ((n / p : ℕ) : ℝ) +
          ∑ p ∈ Nat.primesLE n, Real.log p := Finset.sum_add_distrib
      _ ≤ (n : ℝ) * (Real.log n + Real.log 4) := by nlinarith
  exact le_of_mul_le_mul_left h5 hn'

/-- Summation by parts on `{2, …, N}`. -/
theorem sum_Icc_mul_eq_abel (b h : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ Icc 2 N, b k * h k =
      (∑ k ∈ Icc 2 N, b k) * h N +
        ∑ n ∈ Ico 2 N, (∑ k ∈ Icc 2 n, b k) * (h n - h (n + 1)) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    have e1 : ∑ k ∈ Icc 2 (N + 1), b k * h k =
        ∑ k ∈ Icc 2 N, b k * h k + b (N + 1) * h (N + 1) :=
      Finset.sum_Icc_succ_top (by omega) _
    have e2 : ∑ k ∈ Icc 2 (N + 1), b k = ∑ k ∈ Icc 2 N, b k + b (N + 1) :=
      Finset.sum_Icc_succ_top (by omega) _
    have e3 : ∑ n ∈ Ico 2 (N + 1), (∑ k ∈ Icc 2 n, b k) * (h n - h (n + 1)) =
        ∑ n ∈ Ico 2 N, (∑ k ∈ Icc 2 n, b k) * (h n - h (n + 1)) +
          (∑ k ∈ Icc 2 N, b k) * (h N - h (N + 1)) :=
      Finset.sum_Ico_succ_top hN _
    rw [e1, e2, e3, ih]
    ring

/-- Telescoping on `Ico 2 N`. -/
theorem sum_Ico_two_sub (f : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ∑ n ∈ Ico 2 N, (f (n + 1) - f n) = f N - f 2 := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top hN, ih]
    ring

/-- The primes `≤ n` are the primes in `{2, …, n}`. -/
theorem primesLE_eq_filter_Icc_two (n : ℕ) : Nat.primesLE n = (Icc 2 n).filter Nat.Prime := by
  ext p
  simp only [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h2.two_le, h1⟩, h2⟩
  · rintro ⟨⟨_, h1⟩, h2⟩
    exact ⟨h1, h2⟩

/-- Mertens' second theorem (upper bound) for a natural number `N ≥ 2`, with the constant of the
proof: `∑_{p ≤ N} 1 / p ≤ log log N + 3 - log log 2`. -/
theorem sum_primesLE_inv_le_aux {N : ℕ} (hN : 2 ≤ N) :
    ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p ≤
      Real.log (Real.log N) + 3 - Real.log (Real.log 2) := by
  set b : ℕ → ℝ := fun k => if k.Prime then Real.log k / k else 0 with hb
  set h : ℕ → ℝ := fun k => 1 / Real.log k with hh
  have hA : ∀ n, ∑ k ∈ Icc 2 n, b k = ∑ p ∈ Nat.primesLE n, Real.log p / p := by
    intro n
    rw [primesLE_eq_filter_Icc_two, Finset.sum_filter]
  have hlogpos : ∀ n : ℕ, 2 ≤ n → 0 < Real.log n := fun n hn =>
    Real.log_pos (by exact_mod_cast hn)
  have hS : ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p = ∑ k ∈ Icc 2 N, b k * h k := by
    rw [primesLE_eq_filter_Icc_two, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    by_cases hp : k.Prime
    · simp only [hb, hh, hp, ↓reduceIte]
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      have := (hlogpos k hk2).ne'
      field_simp
    · simp [hb, hp]
  have hmono : ∀ n : ℕ, 2 ≤ n → h (n + 1) ≤ h n := by
    intro n hn
    simp only [hh]
    have h1 := hlogpos n hn
    have h2 : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by push_cast; linarith)
    exact one_div_le_one_div_of_le h1 h2
  have hstep : ∀ n ∈ Ico 2 N,
      (∑ k ∈ Icc 2 n, b k) * (h n - h (n + 1)) ≤
        (Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log n)) +
          Real.log 4 * (h n - h (n + 1)) := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Ico.mp hn).1
    have hd : 0 ≤ h n - h (n + 1) := sub_nonneg.mpr (hmono n hn2)
    have hAn : ∑ k ∈ Icc 2 n, b k ≤ Real.log n + Real.log 4 := by
      rw [hA]; exact sum_primesLE_log_div_le n
    have h1 := hlogpos n hn2
    have h2 := hlogpos (n + 1) (by omega)
    have h3 : Real.log n * (h n - h (n + 1)) ≤
        Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log n) := by
      have := Real.one_sub_inv_le_log_of_pos (x := Real.log ((n + 1 : ℕ) : ℝ) / Real.log n)
        (div_pos h2 h1)
      rw [Real.log_div h2.ne' h1.ne', inv_div] at this
      have e : Real.log n * (h n - h (n + 1)) =
          1 - Real.log n / Real.log ((n + 1 : ℕ) : ℝ) := by
        simp only [hh]
        field_simp
      rw [e]; exact this
    calc (∑ k ∈ Icc 2 n, b k) * (h n - h (n + 1))
        ≤ (Real.log n + Real.log 4) * (h n - h (n + 1)) := mul_le_mul_of_nonneg_right hAn hd
      _ = Real.log n * (h n - h (n + 1)) + Real.log 4 * (h n - h (n + 1)) := by ring
      _ ≤ _ := by linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN0 := hlogpos N hN
  have hAN : ∑ k ∈ Icc 2 N, b k ≤ Real.log N + Real.log 4 := by
    rw [hA]; exact sum_primesLE_log_div_le N
  have hhN : 0 ≤ h N := by simp only [hh]; positivity
  have hT := sum_Ico_two_sub (fun n => Real.log (Real.log (n : ℝ))) hN
  have hU := sum_Ico_two_sub (fun n => - h n) hN
  simp only [Nat.cast_add, Nat.cast_one] at hT
  calc ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p = ∑ k ∈ Icc 2 N, b k * h k := hS
    _ = (∑ k ∈ Icc 2 N, b k) * h N +
        ∑ n ∈ Ico 2 N, (∑ k ∈ Icc 2 n, b k) * (h n - h (n + 1)) := sum_Icc_mul_eq_abel b h hN
    _ ≤ (Real.log N + Real.log 4) * h N +
        ∑ n ∈ Ico 2 N, ((Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log n)) +
          Real.log 4 * (h n - h (n + 1))) := by
      gcongr 1
      · exact mul_le_mul_of_nonneg_right hAN hhN
      · exact Finset.sum_le_sum hstep
    _ = (Real.log N + Real.log 4) * h N +
        ((Real.log (Real.log N) - Real.log (Real.log 2)) + Real.log 4 * (h 2 - h N)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 2
      · simpa using hT
      · have : ∑ n ∈ Ico 2 N, (h n - h (n + 1)) = h 2 - h N := by
          have e : ∑ n ∈ Ico 2 N, (h n - h (n + 1)) =
              ∑ n ∈ Ico 2 N, ((-h (n + 1)) - (-h n)) :=
            Finset.sum_congr rfl fun n _ => by ring
          rw [e, hU]; ring
        rw [this]
    _ = Real.log (Real.log N) + 3 - Real.log (Real.log 2) := by
      have e1 : Real.log N * h N = 1 := by
        simp only [hh]; field_simp
      have e2 : Real.log 4 * h 2 = 2 := by
        simp only [hh]; rw [hlog4]; push_cast; field_simp
      nlinarith [e1, e2]

/-- `log log 2 ≥ -1`. -/
theorem neg_one_le_log_log_two : -1 ≤ Real.log (Real.log 2) := by
  have h1 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
    linarith
  have h2 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num)
    linarith
  calc (-1 : ℝ) ≤ -Real.log 2 := by linarith
    _ = Real.log (1 / 2) := by rw [one_div, Real.log_inv]
    _ ≤ Real.log (Real.log 2) := Real.log_le_log (by norm_num) h1

/-- Mertens' second theorem (upper bound): for every real `x ≥ 2`,
`∑_{p ≤ x, p prime} 1 / p ≤ log log x + 4`. -/
theorem sum_primesLE_inv_le_log_log {x : ℝ} (hx : 2 ≤ x) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p ≤ Real.log (Real.log x) + 4 := by
  have h2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlogpos : 0 < Real.log (⌊x⌋₊ : ℝ) := Real.log_pos (by exact_mod_cast h2)
  have hll : Real.log (Real.log (⌊x⌋₊ : ℝ)) ≤ Real.log (Real.log x) :=
    Real.log_le_log hlogpos
      (Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊x⌋₊)) hfl)
  linarith [sum_primesLE_inv_le_aux h2, neg_one_le_log_log_two]

/-- Mertens' second theorem (upper bound) for an arbitrary finite set `S` of primes `≤ x`:
`∑_{p ∈ S} 1 / p ≤ log log x + 4` for `x ≥ 2`. -/
theorem sum_inv_prime_le_log_log {x : ℝ} (hx : 2 ≤ x) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ x) :
    ∑ p ∈ S, (1 : ℝ) / p ≤ Real.log (Real.log x) + 4 := by
  refine le_trans ?_ (sum_primesLE_inv_le_log_log hx)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => by positivity
  intro p hp
  exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hS p hp).2, (hS p hp).1⟩

/-- Mertens' second theorem (upper bound), strict form for a natural number `Q ≥ 2`:
`∑_{p < Q, p prime} 1 / p ≤ log log Q + 4`. -/
theorem sum_primesBelow_inv_le_log_log {Q : ℕ} (hQ : 2 ≤ Q) :
    ∑ p ∈ Nat.primesBelow Q, (1 : ℝ) / p ≤ Real.log (Real.log Q) + 4 :=
  sum_inv_prime_le_log_log (by exact_mod_cast hQ) _ fun p hp =>
    ⟨Nat.prime_of_mem_primesBelow hp, by exact_mod_cast (Nat.lt_of_mem_primesBelow hp).le⟩

end PrimeCarleson.Proof.Common

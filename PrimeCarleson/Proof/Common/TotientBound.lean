module

public import PrimeCarleson.Proof.Common.Mertens
public import Mathlib.Data.Nat.Totient
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The lower bound `φ(q) ≳ q / log log (10 + q)` for the totient function

The classical lower bound for Euler's totient function used (without proof) in
`sources/Variational_Carleson.tex` L589-L593 (the displayed bound `e:totientbound`) and applied at
L1710-L1713, L1960-L1969 and L2071 (Source: main paper `e:totientbound`, L591–L593), with the
explicit constant `c = exp (-8)`:

* `totient_lower_bound`: `exp (-8) * q / log (log (10 + q)) ≤ φ q` for every natural `q ≥ 1`;
* `exists_totient_lower_bound`: the same as `∃ c > 0, ∀ q ≥ 1, c * q / log (log (10 + q)) ≤ φ q`.

Proof. From Euler's product formula
`q / φ(q) = ∏_{p ∣ q} p / (p - 1) ≤ exp (∑_{p ∣ q} 1 / (p - 1))`.
Split the prime divisors at `y = log (10 + q)`: the primes `p ≤ y` contribute at most
`∑_{p ≤ y} 1 / p + ∑_{n ≥ 2} 1 / (n (n - 1)) ≤ log log y + 5` by Mertens' second theorem
(`PrimeCarleson.Proof.Common.sum_inv_prime_le_log_log`); the primes `p > y` number at most
`log q / log y ≤ y / log y` (their product divides `q`) and each contributes at most `2 / y`, so
they contribute at most `2 / log y ≤ 3`. Exponentiating gives `q / φ(q) ≤ e⁸ log y`.
-/

@[expose] public noncomputable section

open Finset
open scoped Nat.Prime

set_option autoImplicit false

namespace PrimeCarleson.Proof.Common

/-- The telescoping sum `∑_{2 ≤ n ≤ M} 1 / (n (n - 1))` is at most `1`. -/
theorem sum_Icc_inv_mul_pred_le_one (M : ℕ) :
    ∑ n ∈ Icc 2 M, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 := by
  have key : ∀ M : ℕ, 1 ≤ M →
      ∑ n ∈ Icc 2 M, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 - 1 / (M : ℝ) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
      have hM0 : (M : ℝ) ≠ 0 := by positivity
      push_cast
      have e : (1 : ℝ) / (((M : ℝ) + 1) * (((M : ℝ) + 1) - 1)) = 1 / M - 1 / ((M : ℝ) + 1) := by
        rw [show ((M : ℝ) + 1) - 1 = M by ring]
        field_simp
        ring
      linarith
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  · have h1 := key M hM
    have h2 : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
    linarith

/-- The totient lower bound with the explicit constant `exp (-8)`:
`exp (-8) * q / log (log (10 + q)) ≤ φ q` for every natural number `q ≥ 1`. -/
theorem totient_lower_bound {q : ℕ} (hq : 1 ≤ q) :
    Real.exp (-8) * (q : ℝ) / Real.log (Real.log (10 + (q : ℝ))) ≤ (Nat.totient q : ℝ) := by
  set P := q.primeFactors with hP
  set y : ℝ := Real.log (10 + (q : ℝ)) with hy
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hy2 : 2 ≤ y := by
    rw [hy, Real.le_log_iff_exp_le (by positivity)]
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  have hlog2 : (2 : ℝ) / 3 ≤ Real.log y :=
    le_trans (by have := Real.log_two_gt_d9; linarith) (Real.log_le_log (by norm_num) hy2)
  have hlogy : 0 < Real.log y := by linarith
  have hprime : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hp2 : ∀ p ∈ P, (2 : ℝ) ≤ p := fun p hp => by exact_mod_cast (hprime p hp).two_le
  set S : ℝ := ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1) with hS
  set Ps : Finset ℕ := P.filter (fun p : ℕ => (p : ℝ) ≤ y) with hPs
  -- Step 1: `q / φ(q) ≤ exp S`.
  have step1 : (q : ℝ) ≤ (Nat.totient q : ℝ) * Real.exp S := by
    have h := Nat.totient_mul_prod_primeFactors q
    have hcast : (Nat.totient q : ℝ) * ∏ p ∈ P, (p : ℝ) = (q : ℝ) * ∏ p ∈ P, ((p : ℝ) - 1) := by
      have := congrArg (Nat.cast : ℕ → ℝ) h
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod] at this
      rw [this]
      congr 1
      refine Finset.prod_congr rfl fun p hp => ?_
      exact Nat.cast_pred (hprime p hp).pos
    have hprod : ∏ p ∈ P, (p : ℝ) ≤ (∏ p ∈ P, ((p : ℝ) - 1)) * Real.exp S := by
      rw [hS, Real.exp_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod₀ (fun p _ => by positivity) fun p hp => ?_
      have hpos : 0 < (p : ℝ) - 1 := by linarith [hp2 p hp]
      have := Real.add_one_le_exp (1 / ((p : ℝ) - 1))
      calc (p : ℝ) = ((p : ℝ) - 1) * (1 / ((p : ℝ) - 1) + 1) := by field_simp; ring
        _ ≤ ((p : ℝ) - 1) * Real.exp (1 / ((p : ℝ) - 1)) := by gcongr
    have hpos : 0 < ∏ p ∈ P, ((p : ℝ) - 1) :=
      Finset.prod_pos fun p hp => by linarith [hp2 p hp]
    have h3 : (q : ℝ) * ∏ p ∈ P, ((p : ℝ) - 1) ≤
        ((Nat.totient q : ℝ) * Real.exp S) * ∏ p ∈ P, ((p : ℝ) - 1) := by
      calc (q : ℝ) * ∏ p ∈ P, ((p : ℝ) - 1) = (Nat.totient q : ℝ) * ∏ p ∈ P, (p : ℝ) :=
            hcast.symm
        _ ≤ (Nat.totient q : ℝ) * ((∏ p ∈ P, ((p : ℝ) - 1)) * Real.exp S) := by
            gcongr
        _ = _ := by ring
    exact le_of_mul_le_mul_right h3 hpos
  -- Step 2: `S ≤ log log y + 8`.
  have step2 : S ≤ Real.log (Real.log y) + 8 := by
    have hsplit : S = ∑ p ∈ Ps, (1 : ℝ) / ((p : ℝ) - 1) +
        ∑ p ∈ P.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y), (1 : ℝ) / ((p : ℝ) - 1) :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hsmall : ∑ p ∈ Ps, (1 : ℝ) / ((p : ℝ) - 1) ≤
        Real.log (Real.log y) + 5 := by
      have e : ∀ p ∈ Ps, (1 : ℝ) / ((p : ℝ) - 1) =
          1 / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
        intro p hp
        have h2 := hp2 p (Finset.mem_filter.mp hp).1
        have h0 : (p : ℝ) ≠ 0 := by positivity
        have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp
        ring
      rw [Finset.sum_congr rfl e, Finset.sum_add_distrib]
      have h1 : ∑ p ∈ Ps, (1 : ℝ) / p ≤ Real.log (Real.log y) + 4 :=
        sum_inv_prime_le_log_log hy2 _ fun p hp =>
          ⟨hprime p (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
      have h2 : ∑ p ∈ Ps, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
        calc ∑ p ∈ Ps, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
            ≤ ∑ p ∈ Icc 2 q, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ => ?_
              · intro p hp
                have hpP := (Finset.mem_filter.mp hp).1
                exact Finset.mem_Icc.mpr ⟨(hprime p hpP).two_le,
                  Nat.le_of_dvd hq (Nat.dvd_of_mem_primeFactors hpP)⟩
              · have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Icc.mp hp).1
                have : 0 ≤ (p : ℝ) - 1 := by linarith
                positivity
          _ ≤ 1 := sum_Icc_inv_mul_pred_le_one q
      linarith
    have hlarge : ∑ p ∈ P.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y), (1 : ℝ) / ((p : ℝ) - 1) ≤ 3 := by
      set L : Finset ℕ := P.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y) with hL
      have hLP : L ⊆ P := Finset.filter_subset _ _
      have hLy : ∀ p ∈ L, y < p := fun p hp => not_le.mp (Finset.mem_filter.mp hp).2
      have hterm : ∀ p ∈ L, (1 : ℝ) / ((p : ℝ) - 1) ≤ 2 / y := by
        intro p hp
        have := hLy p hp
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        linarith
      have hcard : (L.card : ℝ) * Real.log y ≤ y := by
        have hdvd : (∏ p ∈ L, p) ∣ q :=
          (Finset.prod_dvd_prod_of_subset L P id hLP).trans (Nat.prod_primeFactors_dvd q)
        have hle : ∏ p ∈ L, p ≤ q := Nat.le_of_dvd hq hdvd
        have h1 : y ^ L.card ≤ ∏ p ∈ L, (p : ℝ) := by
          rw [← Finset.prod_const]
          exact Finset.prod_le_prod₀ (fun _ _ => by linarith) fun p hp => (hLy p hp).le
        have h2 : ∏ p ∈ L, (p : ℝ) ≤ q := by rw [← Nat.cast_prod]; exact_mod_cast hle
        have h3 : Real.log (y ^ L.card) ≤ Real.log q :=
          Real.log_le_log (by positivity) (h1.trans h2)
        rw [Real.log_pow] at h3
        have h4 : Real.log q ≤ y := Real.log_le_log hq0 (by linarith)
        linarith
      calc ∑ p ∈ L, (1 : ℝ) / ((p : ℝ) - 1) ≤ ∑ p ∈ L, 2 / y := Finset.sum_le_sum hterm
        _ = L.card * (2 / y) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 3 := by
          have hy0 : 0 < y := by linarith
          have hc0 : (0 : ℝ) ≤ L.card := Nat.cast_nonneg _
          rw [mul_div_assoc', div_le_iff₀ hy0]
          nlinarith [mul_le_mul_of_nonneg_left hlog2 hc0]
    linarith
  -- Conclusion.
  have hexp : Real.exp S ≤ Real.log y * Real.exp 8 := by
    calc Real.exp S ≤ Real.exp (Real.log (Real.log y) + 8) := Real.exp_le_exp.mpr step2
      _ = Real.log y * Real.exp 8 := by rw [Real.exp_add, Real.exp_log hlogy]
  rw [div_le_iff₀ hlogy]
  have h1 : (q : ℝ) ≤ (Nat.totient q : ℝ) * (Real.log y * Real.exp 8) :=
    step1.trans (mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _))
  have h2 : Real.exp (-8) * Real.exp 8 = 1 := by rw [← Real.exp_add]; simp
  have h3 : 0 < Real.exp (-8) := Real.exp_pos _
  calc Real.exp (-8) * (q : ℝ)
      ≤ Real.exp (-8) * ((Nat.totient q : ℝ) * (Real.log y * Real.exp 8)) :=
        mul_le_mul_of_nonneg_left h1 h3.le
    _ = (Nat.totient q : ℝ) * Real.log y * (Real.exp (-8) * Real.exp 8) := by ring
    _ = (Nat.totient q : ℝ) * Real.log y := by rw [h2, mul_one]

/-- The totient lower bound `φ(q) ≳ q / log log (10 + q)` of
`sources/Variational_Carleson.tex` L591-L593 with an absolute implicit constant. -/
theorem exists_totient_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, 1 ≤ q →
      c * (q : ℝ) / Real.log (Real.log (10 + (q : ℝ))) ≤ (Nat.totient q : ℝ) :=
  ⟨Real.exp (-8), Real.exp_pos _, fun _ hq => totient_lower_bound hq⟩

end PrimeCarleson.Proof.Common

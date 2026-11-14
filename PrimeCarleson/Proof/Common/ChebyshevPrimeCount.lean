module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Analysis.Complex.ExponentialBounds
public import PrimeCarleson.Proof.Common.Mertens

/-!
# Chebyshev's upper bound for the prime counting function and tails of prime sums

Chebyshev's upper bound for the prime counting function, a standard result used in place of the
prime number theorem in [KMTT] L912-L916, and the prime sums of the large-prime step there:

* `primeCounting_floor_le`: `π(⌊t⌋) ≤ 5 t / log t` for every real `t ≥ 2`, from Chebyshev's
  `θ(x) ≤ x log 4` (`Chebyshev.theta_le_log4_mul_x`) by splitting the primes at `√t`;
* `sum_primes_block_le`: the primes of a dyadic block `[x, 2x)` satisfy
  `∑ p^(-σ) / p ≤ 10 x^(-σ) / log x`;
* `sum_primes_rpow_neg_div_le`: for `σ ∈ (0, 1]` with `σ log Q ≥ 1/2`, the primes `p ≥ Q` satisfy
  `∑ p^(-σ) / p ≤ 60` (the tail `∑_{p ≥ Q} p^(-1-σ)` is `O(1)`; dyadic decomposition and the
  geometric series, no integral);
* `sum_primes_le_log_log_add`: with Mertens' second theorem (`sum_inv_prime_le_log_log`), for
  `a p ≤ A / p` and `a p ≤ B p^(-σ) / p`, `∑_p a p ≤ A (log log Q + 4) + 60 B`.
-/

@[expose] public noncomputable section

open Finset
open scoped Nat.Prime

set_option autoImplicit false

namespace PrimeCarleson.Proof.Common

/-- Chebyshev's upper bound for the prime counting function: `π(⌊t⌋) ≤ 5 t / log t` for every
real `t ≥ 2`. -/
theorem primeCounting_floor_le {t : ℝ} (ht : 2 ≤ t) :
    (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ 5 * t / Real.log t := by
  have hlog : 0 < Real.log t := Real.log_pos (by linarith)
  have ht0 : 0 < t := by linarith
  set n := ⌊t⌋₊ with hn
  have hnt : (n : ℝ) ≤ t := Nat.floor_le ht0.le
  rw [← Nat.primesLE_card_eq_primeCounting]
  set P := Nat.primesLE n with hP
  have hsplit := Finset.card_filter_add_card_filter_not (s := P) (fun p : ℕ => (p : ℝ) ^ 2 ≤ t)
  -- small primes: at most √t
  have hsmall : ((P.filter (fun p : ℕ => (p : ℝ) ^ 2 ≤ t)).card : ℝ) ≤ Real.sqrt t := by
    have hsub : P.filter (fun p : ℕ => (p : ℝ) ^ 2 ≤ t) ⊆ Finset.Icc 1 ⌊Real.sqrt t⌋₊ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hp' := (Nat.mem_primesLE.mp hp.1).2
      rw [Finset.mem_Icc]
      refine ⟨hp'.one_lt.le, Nat.le_floor ?_⟩
      exact Real.le_sqrt_of_sq_le hp.2
    calc ((P.filter (fun p : ℕ => (p : ℝ) ^ 2 ≤ t)).card : ℝ)
        ≤ ((Finset.Icc 1 ⌊Real.sqrt t⌋₊).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ = ⌊Real.sqrt t⌋₊ := by simp
      _ ≤ Real.sqrt t := Nat.floor_le (Real.sqrt_nonneg _)
  -- large primes
  have hlarge : ((P.filter (fun p : ℕ => ¬ (p : ℝ) ^ 2 ≤ t)).card : ℝ) * (Real.log t / 2) ≤
      Real.log 4 * t := by
    have h1 : ((P.filter (fun p : ℕ => ¬ (p : ℝ) ^ 2 ≤ t)).card) • (Real.log t / 2) ≤
        ∑ p ∈ P.filter (fun p : ℕ => ¬ (p : ℝ) ^ 2 ≤ t), Real.log p := by
      refine Finset.card_nsmul_le_sum _ _ _ fun p hp => ?_
      rw [Finset.mem_filter] at hp
      have hp' := (Nat.mem_primesLE.mp hp.1).2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.pos
      have hpt : t < (p : ℝ) ^ 2 := not_le.mp hp.2
      have : Real.log t < Real.log ((p : ℝ) ^ 2) := Real.log_lt_log ht0 hpt
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    have h2 : ∑ p ∈ P.filter (fun p : ℕ => ¬ (p : ℝ) ^ 2 ≤ t), Real.log p ≤
        ∑ p ∈ P, Real.log p := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p hp _ => ?_
      have hp' := (Nat.mem_primesLE.mp hp).2
      exact Real.log_nonneg (by exact_mod_cast hp'.one_lt.le)
    have h3 : ∑ p ∈ P, Real.log p ≤ Real.log 4 * t := by
      have := Chebyshev.theta_le_log4_mul_x ht0.le
      rw [Chebyshev.theta_eq_theta_coe_floor, Chebyshev.theta_eq_sum_primesLE_log] at this
      exact this
    rw [nsmul_eq_mul] at h1
    linarith
  have hcard : (P.card : ℝ) =
      ((P.filter (fun p : ℕ => (p : ℝ) ^ 2 ≤ t)).card : ℝ) +
        ((P.filter (fun p : ℕ => ¬ (p : ℝ) ^ 2 ≤ t)).card : ℝ) := by
    rw [← hsplit]; push_cast; ring
  have hsqrt : Real.sqrt t ≤ 2 * t / Real.log t := by
    rw [le_div_iff₀ hlog]
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have h1 : Real.log t = 2 * Real.log (Real.sqrt t) := by
      rw [← Real.log_rpow hs]
      · rw [show Real.sqrt t ^ (2 : ℝ) = t by
          rw [Real.rpow_two]; exact Real.sq_sqrt ht0.le]
    have h2 : Real.log (Real.sqrt t) ≤ Real.sqrt t := by
      have := Real.log_le_sub_one_of_pos hs; linarith
    have h3 : t = Real.sqrt t * Real.sqrt t := (Real.mul_self_sqrt ht0.le).symm
    nlinarith
  have hlarge' : ((P.filter (fun p : ℕ => ¬ (p : ℝ) ^ 2 ≤ t)).card : ℝ) ≤
      2 * Real.log 4 * t / Real.log t := by
    rw [le_div_iff₀ hlog]; nlinarith
  have hlog4 : Real.log 4 ≤ 3 / 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  have : 2 * Real.log 4 * t / Real.log t ≤ 3 * t / Real.log t := by
    gcongr; linarith
  calc (P.card : ℝ) ≤ 2 * t / Real.log t + 3 * t / Real.log t := by
        rw [hcard]; linarith
    _ = 5 * t / Real.log t := by ring

/-- A dyadic block of primes `[x, 2x)`. -/
theorem sum_primes_block_le {x σ : ℝ} (hx : 2 ≤ x) (hσ : 0 ≤ σ) (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime ∧ x ≤ p ∧ (p : ℝ) < 2 * x) :
    ∑ p ∈ T, (p : ℝ) ^ (-σ) / p ≤ 10 * x ^ (-σ) / Real.log x := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hsub : T ⊆ Nat.primesLE ⌊2 * x⌋₊ := by
    intro p hp
    obtain ⟨hpp, -, hp2⟩ := hT p hp
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor hp2.le, hpp⟩
  have hcard : (T.card : ℝ) ≤ 10 * x / Real.log x := by
    have h1 : (T.card : ℝ) ≤ (Nat.primeCounting ⌊2 * x⌋₊ : ℝ) := by
      rw [← Nat.primesLE_card_eq_primeCounting]
      exact_mod_cast Finset.card_le_card hsub
    have h2 := primeCounting_floor_le (t := 2 * x) (by linarith)
    have h3 : Real.log x ≤ Real.log (2 * x) :=
      Real.log_le_log hx0 (by linarith)
    calc (T.card : ℝ) ≤ 5 * (2 * x) / Real.log (2 * x) := h1.trans h2
      _ ≤ 5 * (2 * x) / Real.log x := by
          gcongr
      _ = 10 * x / Real.log x := by ring
  have hterm : ∀ p ∈ T, (p : ℝ) ^ (-σ) / p ≤ x ^ (-σ) / x := by
    intro p hp
    obtain ⟨hpp, hxp, -⟩ := hT p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have h1 : (p : ℝ) ^ (-σ) ≤ x ^ (-σ) := Real.rpow_le_rpow_of_nonpos hx0 hxp (by linarith)
    exact div_le_div₀ (Real.rpow_nonneg hx0.le _) h1 hx0 hxp
  calc ∑ p ∈ T, (p : ℝ) ^ (-σ) / p ≤ ∑ _p ∈ T, x ^ (-σ) / x := Finset.sum_le_sum hterm
    _ = (T.card : ℝ) * (x ^ (-σ) / x) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (10 * x / Real.log x) * (x ^ (-σ) / x) := by
        gcongr
    _ = 10 * x ^ (-σ) / Real.log x := by field_simp

/-- `1 - 2^(-σ) ≥ σ / 3` for `0 < σ ≤ 1`. -/
theorem one_sub_two_rpow_neg_ge {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    σ / 3 ≤ 1 - (2 : ℝ) ^ (-σ) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ σ := Real.rpow_pos_of_pos (by norm_num) _
  have hle : (2 : ℝ) ^ σ ≤ 2 := by
    calc (2 : ℝ) ^ σ ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ1
      _ = 2 := Real.rpow_one 2
  have hge : 1 + σ * Real.log 2 ≤ (2 : ℝ) ^ σ := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
    exact Real.add_one_le_exp _ |>.trans' (by linarith)
  have hlog2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  rw [Real.rpow_neg (by norm_num)]
  set y : ℝ := (2 : ℝ) ^ σ with hy
  have hy1 : 0 ≤ y - 1 := by nlinarith [mul_pos hσ (by linarith : (0 : ℝ) < Real.log 2)]
  have h3 : 1 - y⁻¹ = (y - 1) / y := by field_simp
  have h4 : (y - 1) / 2 ≤ (y - 1) / y := div_le_div_of_nonneg_left hy1 h2 hle
  rw [h3]
  nlinarith

/-- The tail of the prime sum `∑ p ^ (-1 - σ)` over primes `p ≥ Q` is bounded when `σ log Q`
is bounded below. -/
theorem sum_primes_rpow_neg_div_le {Q σ : ℝ} (hQ : 2 ≤ Q) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσQ : 1 / 2 ≤ σ * Real.log Q) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ Q ≤ p) :
    ∑ p ∈ S, (p : ℝ) ^ (-σ) / p ≤ 60 := by
  set Q₀ : ℕ := ⌈Q⌉₊ with hQ₀
  have hQ₀Q : Q ≤ Q₀ := Nat.le_ceil Q
  have hQ₀2 : (2 : ℝ) ≤ Q₀ := hQ.trans hQ₀Q
  have hQ₀2' : 2 ≤ Q₀ := by exact_mod_cast hQ₀2
  have hQ₀pos : 0 < Q₀ := by omega
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hlogQ₀ : Real.log Q ≤ Real.log Q₀ := Real.log_le_log (by linarith) hQ₀Q
  set r : ℝ := (2 : ℝ) ^ (-σ) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : σ / 3 ≤ 1 - r := one_sub_two_rpow_neg_ge hσ hσ1
  set J := (S.sup fun p => Nat.log 2 (p / Q₀)) + 1 with hJ
  have hmaps : ∀ p ∈ S, Nat.log 2 (p / Q₀) ∈ range J := by
    intro p hp
    rw [Finset.mem_range, hJ]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun p => Nat.log 2 (p / Q₀)) hp)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ j ∈ range J,
      ∑ p ∈ S with Nat.log 2 (p / Q₀) = j, (p : ℝ) ^ (-σ) / p ≤ 20 * σ * r ^ j := by
    intro j _
    set x : ℝ := (Q₀ : ℝ) * 2 ^ j with hx
    have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hx2 : 2 ≤ x := by
      calc (2 : ℝ) ≤ Q₀ * 1 := by linarith
        _ ≤ x := by rw [hx]; gcongr
    have hT : ∀ p ∈ S.filter (fun p => Nat.log 2 (p / Q₀) = j),
        p.Prime ∧ x ≤ p ∧ (p : ℝ) < 2 * x := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpS, hpj⟩ := hp
      obtain ⟨hpp, hpQ⟩ := hS p hpS
      have hQ₀p : Q₀ ≤ p := Nat.ceil_le.mpr hpQ
      have hdiv : p / Q₀ ≠ 0 := by
        have := (Nat.div_pos hQ₀p hQ₀pos).ne'
        exact this
      have h1 : 2 ^ j ≤ p / Q₀ := by
        rw [← hpj]; exact Nat.pow_log_le_self 2 hdiv
      have h2 : p / Q₀ < 2 ^ (j + 1) := by
        rw [← hpj]; exact Nat.lt_pow_succ_log_self (by norm_num) _
      have h1' : 2 ^ j * Q₀ ≤ p := (Nat.le_div_iff_mul_le hQ₀pos).mp h1
      have h2' : p < 2 ^ (j + 1) * Q₀ := (Nat.div_lt_iff_lt_mul hQ₀pos).mp h2
      refine ⟨hpp, ?_, ?_⟩
      · have : ((2 ^ j * Q₀ : ℕ) : ℝ) ≤ p := by exact_mod_cast h1'
        rw [hx]; push_cast at this; linarith
      · have : (p : ℝ) < ((2 ^ (j + 1) * Q₀ : ℕ) : ℝ) := by exact_mod_cast h2'
        rw [hx]; push_cast at this; rw [pow_succ] at this; linarith
    refine (sum_primes_block_le hx2 hσ.le _ hT).trans ?_
    have hlogx : Real.log Q₀ ≤ Real.log x :=
      Real.log_le_log (by linarith) (by
        rw [hx]; calc (Q₀ : ℝ) = Q₀ * 1 := (mul_one _).symm
          _ ≤ _ := by gcongr)
    have hxσ : x ^ (-σ) ≤ r ^ j := by
      rw [hx, Real.mul_rpow (by positivity) (by positivity), hr]
      have h3 : ((2 : ℝ) ^ j) ^ (-σ) = ((2 : ℝ) ^ (-σ)) ^ j := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
          Real.rpow_mul (by norm_num), Real.rpow_natCast]
      have h4 : (Q₀ : ℝ) ^ (-σ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
      rw [h3]
      calc (Q₀ : ℝ) ^ (-σ) * ((2 : ℝ) ^ (-σ)) ^ j ≤ 1 * ((2 : ℝ) ^ (-σ)) ^ j := by
            gcongr
        _ = _ := one_mul _
    have hlog' : 1 / Real.log x ≤ 2 * σ := by
      have : 1 / 2 ≤ σ * Real.log x := by
        calc (1 : ℝ) / 2 ≤ σ * Real.log Q := hσQ
          _ ≤ σ * Real.log x := mul_le_mul_of_nonneg_left (hlogQ₀.trans hlogx) hσ.le
      rw [div_le_iff₀ (by linarith [hlogQ])]
      linarith
    calc 10 * x ^ (-σ) / Real.log x = 10 * x ^ (-σ) * (1 / Real.log x) := by ring
      _ ≤ 10 * r ^ j * (2 * σ) := by
          have h0 : 0 ≤ 1 / Real.log x := div_nonneg zero_le_one (by linarith)
          have h5 : 0 ≤ x ^ (-σ) := Real.rpow_nonneg (by linarith) _
          gcongr
      _ = 20 * σ * r ^ j := by ring
  calc ∑ j ∈ range J, ∑ p ∈ S with Nat.log 2 (p / Q₀) = j, (p : ℝ) ^ (-σ) / p
      ≤ ∑ j ∈ range J, 20 * σ * r ^ j := Finset.sum_le_sum hfib
    _ = 20 * σ * ∑ j ∈ range J, r ^ j := by rw [Finset.mul_sum]
    _ ≤ 20 * σ * (1 / (1 - r)) := by
        have hr1' : 0 < 1 - r := by linarith
        have hr2 : r < 1 := by linarith
        have hgeom : (∑ j ∈ range J, r ^ j) * (1 - r) = 1 - r ^ J := geom_sum_mul_neg r J
        have hrJ : 0 ≤ r ^ J := pow_nonneg hr0 _
        have : ∑ j ∈ range J, r ^ j ≤ 1 / (1 - r) := by
          rw [le_div_iff₀ hr1']; linarith
        gcongr
    _ ≤ 60 := by
        have hr1' : 0 < 1 - r := by linarith
        have : 1 / (1 - r) ≤ 3 / σ := by
          rw [div_le_div_iff₀ hr1' hσ]; linarith
        calc 20 * σ * (1 / (1 - r)) ≤ 20 * σ * (3 / σ) := by gcongr
          _ = 60 := by field_simp; ring

/-- Prime sums with a Rankin weight: if `a p ≤ A / p` and `a p ≤ B p^(-σ) / p` for all primes `p`,
then `∑_{p ∈ S} a p ≤ A (log log Q + 4) + 60 B` for every finite set `S` of primes. -/
theorem sum_primes_le_log_log_add {Q σ : ℝ} (hQ : 2 ≤ Q) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσQ : 1 / 2 ≤ σ * Real.log Q) (a : ℕ → ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha1 : ∀ p : ℕ, p.Prime → a p ≤ A / p)
    (ha2 : ∀ p : ℕ, p.Prime → a p ≤ B * ((p : ℝ) ^ (-σ) / p))
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, a p ≤ A * (Real.log (Real.log Q) + 4) + 60 * B := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p : ℕ => (p : ℝ) < Q)]
  have h1 : ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) < Q), a p ≤
      A * (Real.log (Real.log Q) + 4) := by
    calc ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) < Q), a p
        ≤ ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) < Q), A * ((1 : ℝ) / p) := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [Finset.mem_filter] at hp
          have := ha1 p (hS p hp.1)
          calc a p ≤ A / p := this
            _ = A * ((1 : ℝ) / p) := by ring
      _ = A * ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) < Q), (1 : ℝ) / p := by rw [Finset.mul_sum]
      _ ≤ A * (Real.log (Real.log Q) + 4) := by
          gcongr
          exact sum_inv_prime_le_log_log hQ _ fun p hp => by
            rw [Finset.mem_filter] at hp
            exact ⟨hS p hp.1, hp.2.le⟩
  have h2 : ∑ p ∈ S.filter (fun p : ℕ => ¬ (p : ℝ) < Q), a p ≤ 60 * B := by
    calc ∑ p ∈ S.filter (fun p : ℕ => ¬ (p : ℝ) < Q), a p
        ≤ ∑ p ∈ S.filter (fun p : ℕ => ¬ (p : ℝ) < Q), B * ((p : ℝ) ^ (-σ) / p) := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [Finset.mem_filter] at hp
          exact ha2 p (hS p hp.1)
      _ = B * ∑ p ∈ S.filter (fun p : ℕ => ¬ (p : ℝ) < Q), (p : ℝ) ^ (-σ) / p := by
          rw [Finset.mul_sum]
      _ ≤ B * 60 := by
          gcongr
          exact sum_primes_rpow_neg_div_le hQ hσ hσ1 hσQ _ fun p hp => by
            rw [Finset.mem_filter] at hp
            exact ⟨hS p hp.1, not_lt.mp hp.2⟩
      _ = 60 * B := by ring
  linarith

end PrimeCarleson.Proof.Common

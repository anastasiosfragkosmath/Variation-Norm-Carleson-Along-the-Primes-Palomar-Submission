module

public import PrimeCarleson.Proof.Fplus31.Brun.Divisors
public import PrimeCarleson.Proof.FplusProp21.Arith

/-!
# Cramér–Heath-Brown comparison, step 4: Rankin's trick for the tail `∑_{q ∣ P(w), q > R} 1/φ(q)`

The tail estimate of piece `D₂` of the comparison of the Cramér model with the Heath-Brown model:
`S = ∑_{q ∣ P(w)} 1/φ(q) = P(w)/φ(P(w))`, and for the tail `S - S_R = ∑_{q ∣ P(w), q > R} 1/φ(q)`

* `sum_divisors_primorialBelow_rpow`: `∑_{d ∣ P(w)} d^σ/φ(d) = ∏_{p < w} (1 + p^σ/(p-1))`;
* `sum_divisors_inv_totient`: the case `σ = 0`;
* `sum_tail_inv_totient_le_sq`: if `p^σ ≤ 2` for all `p < w` then the tail is at most
  `R^{-σ} (P(w)/φ(P(w)))²`, since `1 + p^σ/(p-1) ≤ (1 + 1/(p-1))²`.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- **Euler product for the divisors of `P(w)`**: for every real `σ`,
`∑_{d ∣ P(w)} d^σ/φ(d) = ∏_{p < w} (1 + p^σ/(p-1))`. -/
theorem sum_divisors_primorialBelow_rpow (w : ℕ) (σ : ℝ) :
    ∑ d ∈ (primorialBelow w).divisors, (d : ℝ) ^ σ / (Nat.totient d : ℝ) =
      ∏ p ∈ Nat.primesBelow w, (1 + (p : ℝ) ^ σ / ((p : ℝ) - 1)) := by
  rw [sum_divisors_primorialBelow w (fun d => (d : ℝ) ^ σ / (Nat.totient d : ℝ)),
    Finset.prod_one_add]
  refine Finset.sum_congr rfl fun D hD => ?_
  rw [Finset.mem_powerset] at hD
  have hprime : ∀ p ∈ D, p.Prime := fun p hp => Nat.prime_of_mem_primesBelow (hD hp)
  have hsqf : Squarefree (∏ p ∈ D, p) :=
    (squarefree_primorialBelow w).squarefree_of_dvd (Finset.prod_dvd_prod_of_subset _ _ _ hD)
  rw [FplusProp21.totient_eq_prod_of_squarefree hsqf, Nat.primeFactors_prod hprime]
  have hp1 : ∀ p ∈ D, 1 ≤ p := fun p hp => (hprime p hp).one_lt.le
  rw [Nat.cast_prod, Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p),
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [Nat.cast_sub (hp1 p hp)]
  simp

/-- `∑_{d ∣ P(w)} 1/φ(d) = P(w)/φ(P(w))`. -/
theorem sum_divisors_inv_totient (w : ℕ) :
    ∑ d ∈ (primorialBelow w).divisors, 1 / (Nat.totient d : ℝ) =
      (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) := by
  have h := sum_divisors_primorialBelow_rpow w 0
  simp only [Real.rpow_zero] at h
  rw [primorialBelow_div_totient, ← h]

/-- **Rankin's trick** for the tail of `∑_{d ∣ P(w)} 1/φ(d)`. -/
theorem sum_tail_inv_totient_le (w : ℕ) {R : ℕ} (hR : 0 < R) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∑ d ∈ (primorialBelow w).divisors.filter (fun q => R < q), 1 / (Nat.totient d : ℝ) ≤
      (R : ℝ) ^ (-σ) * ∏ p ∈ Nat.primesBelow w, (1 + (p : ℝ) ^ σ / ((p : ℝ) - 1)) := by
  rw [← sum_divisors_primorialBelow_rpow, Finset.mul_sum]
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  refine (Finset.sum_le_sum fun d hd => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun d _ _ => ?_))
  · have hd0 := mem_filter.1 hd
    have hd' : (R : ℝ) < d := by exact_mod_cast hd0.2
    have h1 : (1 : ℝ) ≤ ((d : ℝ) / R) ^ σ := Real.one_le_rpow ((one_le_div hR').2 hd'.le) hσ
    have hφ : (0 : ℝ) < Nat.totient d := by
      exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_mem_divisors hd0.1)
    have h2 : 1 ≤ (R : ℝ) ^ (-σ) * (d : ℝ) ^ σ := by
      rw [Real.div_rpow (by positivity) hR'.le] at h1
      rw [Real.rpow_neg hR'.le, ← div_eq_inv_mul]
      exact h1
    calc 1 / (Nat.totient d : ℝ) ≤ ((R : ℝ) ^ (-σ) * (d : ℝ) ^ σ) / (Nat.totient d : ℝ) :=
          div_le_div_of_nonneg_right h2 hφ.le
      _ = _ := by ring
  · positivity


/-- Each factor `1 + p^σ/(p-1) ≤ (1 + 1/(p-1))²` once `p^σ ≤ 2`, so the Euler product at the
Rankin exponent is at most `(P(w)/φ(P(w)))²`. -/
theorem prod_one_add_rpow_le_sq (w : ℕ) {σ : ℝ}
    (h2 : ∀ p ∈ Nat.primesBelow w, (p : ℝ) ^ σ ≤ 2) :
    ∏ p ∈ Nat.primesBelow w, (1 + (p : ℝ) ^ σ / ((p : ℝ) - 1)) ≤
      ((primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ)) ^ 2 := by
  rw [primorialBelow_div_totient, ← Finset.prod_pow]
  refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast Nat.two_le_of_mem_primesBelow hp
    have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have : 0 ≤ (p : ℝ) ^ σ / ((p : ℝ) - 1) := by positivity
    linarith
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast Nat.two_le_of_mem_primesBelow hp
    have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have h1 : (p : ℝ) ^ σ / ((p : ℝ) - 1) ≤ 2 * (1 / ((p : ℝ) - 1)) := by
      rw [← mul_one_div]
      exact mul_le_mul_of_nonneg_right (h2 p hp) (by positivity)
    nlinarith [sq_nonneg (1 / ((p : ℝ) - 1))]

/-- **The tail of `∑_{d ∣ P(w)} 1/φ(d)` above `R`** (Rankin's trick): if `p^σ ≤ 2` for all
`p < w`, it is at most `R^{-σ} (P(w)/φ(P(w)))²`. -/
theorem sum_tail_inv_totient_le_sq (w : ℕ) {R : ℕ} (hR : 0 < R) {σ : ℝ} (hσ : 0 ≤ σ)
    (h2 : ∀ p ∈ Nat.primesBelow w, (p : ℝ) ^ σ ≤ 2) :
    ∑ d ∈ (primorialBelow w).divisors.filter (fun q => R < q), 1 / (Nat.totient d : ℝ) ≤
      (R : ℝ) ^ (-σ) * ((primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ)) ^ 2 :=
  (sum_tail_inv_totient_le w hR hσ).trans
    (mul_le_mul_of_nonneg_left (prod_one_add_rpow_le_sq w h2) (by positivity))

end PrimeCarleson.Proof.Fplus31

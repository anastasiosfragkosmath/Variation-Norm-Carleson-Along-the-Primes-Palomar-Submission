module

public import PrimeCarleson.Proof.Fplus31.TypeIII.Reindex

/-!
# Divisor moments for the divisor-bounded type II coefficients

Part of the Vaughan decomposition in the proof of [F+] Proposition 3.1: the type II coefficients of
Vaughan's identity are `b_w = ∑_{e ∣ w, e > N^{1/3}} μ(e)`, with `|b_w| ≤ τ(w)`, so the bilinear
Cauchy–Schwarz step (Leng23 Proposition `p:type1type2correlation`, third bullet, via TT21
Proposition 7.2) needs the second divisor moment `∑_{n ≤ M} τ(n)² ≪ M log³ M`.

* `sum_Icc_inv_le`: `∑_{a ≤ M} 1/a ≤ 1 + log M`;
* `card_divisors_mul_le`: `τ(d m) ≤ τ(d) τ(m)`;
* `sum_Icc_card_divisors_le`: `∑_{m ≤ M} τ(m) ≤ M (1 + log M)`;
* `sum_Icc_card_divisors_div_le`: `∑_{d ≤ M} τ(d)/d ≤ (1 + log M)²`;
* `sum_Icc_card_divisors_sq_le`: `∑_{n ≤ M} τ(n)² ≤ M (1 + log M)³`.
-/

@[expose] public noncomputable section

open Finset
open scoped Pointwise

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- `∑_{a ≤ M} 1/a ≤ 1 + log M`. -/
theorem sum_Icc_inv_le (M : ℕ) : ∑ a ∈ Icc 1 M, (1 : ℝ) / a ≤ 1 + Real.log M := by
  have h := harmonic_le_one_add_log M
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

/-- `∑_{a ≤ M} 1/a ≥ 0`. -/
theorem sum_Icc_inv_nonneg (M : ℕ) : 0 ≤ ∑ a ∈ Icc 1 M, (1 : ℝ) / a :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- `τ(d m) ≤ τ(d) τ(m)`. -/
theorem card_divisors_mul_le (d m : ℕ) :
    (d * m).divisors.card ≤ d.divisors.card * m.divisors.card := by
  rw [Nat.divisors_mul]
  exact Finset.card_mul_le

/-- `∑_{m ≤ M} τ(m) ≤ M (1 + log M)`. -/
theorem sum_Icc_card_divisors_le (M : ℕ) :
    ∑ m ∈ Icc 1 M, (m.divisors.card : ℝ) ≤ M * (1 + Real.log M) := by
  have h1 : ∀ m ∈ Icc 1 M,
      (m.divisors.card : ℝ) = ∑ c ∈ m.divisors, ((fun _ _ : ℕ => (1 : ℝ)) c (m / c)) := by
    intro m _
    simp
  rw [Finset.sum_congr rfl h1, sum_Icc_divisors M (fun _ _ => (1 : ℝ))]
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  calc ∑ c ∈ Icc 1 M, ((M / c : ℕ) : ℝ) ≤ ∑ c ∈ Icc 1 M, (M : ℝ) * (1 / c) := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [mul_one_div]
        exact Nat.cast_div_le
    _ = M * ∑ c ∈ Icc 1 M, (1 : ℝ) / c := by rw [Finset.mul_sum]
    _ ≤ M * (1 + Real.log M) := mul_le_mul_of_nonneg_left (sum_Icc_inv_le M) (Nat.cast_nonneg _)

/-- `∑_{d ≤ M} τ(d)/d ≤ (1 + log M)²`. -/
theorem sum_Icc_card_divisors_div_le (M : ℕ) :
    ∑ d ∈ Icc 1 M, (d.divisors.card : ℝ) / d ≤ (1 + Real.log M) ^ 2 := by
  have h1 : ∀ d ∈ Icc 1 M, (d.divisors.card : ℝ) / d =
      ∑ a ∈ d.divisors, ((fun a b : ℕ => (1 : ℝ) / ((a : ℝ) * b)) a (d / a)) := by
    intro d hd
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hdvd : a ∣ d := Nat.dvd_of_mem_divisors ha
    simp only [Nat.cast_one]
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
  rw [Finset.sum_congr rfl h1, sum_Icc_divisors M (fun a b : ℕ => (1 : ℝ) / ((a : ℝ) * b))]
  calc ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 (M / a), (1 : ℝ) / ((a : ℝ) * b)
      ≤ ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, (1 : ℝ) / ((a : ℝ) * b) := by
        refine Finset.sum_le_sum fun a ha => ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun b _ _ => by positivity
        exact Finset.Icc_subset_Icc_right (Nat.div_le_self _ _)
    _ = (∑ a ∈ Icc 1 M, (1 : ℝ) / a) * ∑ b ∈ Icc 1 M, (1 : ℝ) / b := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [one_div_mul_one_div]
    _ ≤ (1 + Real.log M) * (1 + Real.log M) :=
        mul_le_mul (sum_Icc_inv_le M) (sum_Icc_inv_le M) (sum_Icc_inv_nonneg M)
          (le_trans (sum_Icc_inv_nonneg M) (sum_Icc_inv_le M))
    _ = (1 + Real.log M) ^ 2 := by ring

/-- `∑_{w ≤ M/d} τ(w) ≤ (M/d)(1 + log M)`. -/
theorem sum_Icc_div_card_divisors_le {M d : ℕ} (hM : 1 ≤ M) :
    ∑ w ∈ Icc 1 (M / d), (w.divisors.card : ℝ) ≤ (M : ℝ) / d * (1 + Real.log M) := by
  have hlog : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  refine (sum_Icc_card_divisors_le (M / d)).trans ?_
  have hdiv : ((M / d : ℕ) : ℝ) ≤ (M : ℝ) / d := Nat.cast_div_le
  have hlog' : Real.log ((M / d : ℕ) : ℝ) ≤ Real.log M := by
    rcases Nat.eq_zero_or_pos (M / d) with h0 | h0
    · rw [h0]
      simpa using hlog
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast Nat.div_le_self M d)
  have hnn : 0 ≤ 1 + Real.log ((M / d : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (M / d) with h0 | h0
    · rw [h0]
      simp
    · have := Real.log_nonneg (by exact_mod_cast h0 : (1 : ℝ) ≤ ((M / d : ℕ) : ℝ))
      linarith
  exact mul_le_mul hdiv (by linarith) hnn (by positivity)

/-- **The second divisor moment**: `∑_{n ≤ M} τ(n)² ≤ M (1 + log M)³`. -/
theorem sum_Icc_card_divisors_sq_le (M : ℕ) :
    ∑ n ∈ Icc 1 M, ((n.divisors.card : ℝ)) ^ 2 ≤ M * (1 + Real.log M) ^ 3 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  have hlog : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  have h1 : ∀ n ∈ Icc 1 M, ((n.divisors.card : ℝ)) ^ 2 =
      ∑ d ∈ n.divisors, ((fun d w : ℕ => ((d * w).divisors.card : ℝ)) d (n / d)) := by
    intro n _
    rw [sq, ← nsmul_eq_mul']
    rw [← Finset.sum_const]
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  rw [Finset.sum_congr rfl h1, sum_Icc_divisors M (fun d w : ℕ => ((d * w).divisors.card : ℝ))]
  have h2 : ∑ d ∈ Icc 1 M, ∑ w ∈ Icc 1 (M / d), (((d * w).divisors.card : ℕ) : ℝ) ≤
      ∑ d ∈ Icc 1 M, (d.divisors.card : ℝ) * ((M : ℝ) / d * (1 + Real.log M)) := by
    refine Finset.sum_le_sum fun d _ => ?_
    calc ∑ w ∈ Icc 1 (M / d), (((d * w).divisors.card : ℕ) : ℝ)
        ≤ ∑ w ∈ Icc 1 (M / d), (d.divisors.card : ℝ) * (w.divisors.card : ℝ) :=
          Finset.sum_le_sum fun w _ => by exact_mod_cast card_divisors_mul_le d w
      _ = (d.divisors.card : ℝ) * ∑ w ∈ Icc 1 (M / d), (w.divisors.card : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Icc_div_card_divisors_le hM) (Nat.cast_nonneg _)
  have h3 : ∑ d ∈ Icc 1 M, (d.divisors.card : ℝ) * ((M : ℝ) / d * (1 + Real.log M)) =
      M * (1 + Real.log M) * ∑ d ∈ Icc 1 M, (d.divisors.card : ℝ) / d := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  have h4 : M * (1 + Real.log M) * ∑ d ∈ Icc 1 M, (d.divisors.card : ℝ) / d ≤
      M * (1 + Real.log M) * (1 + Real.log M) ^ 2 :=
    mul_le_mul_of_nonneg_left (sum_Icc_card_divisors_div_le M) (by positivity)
  calc _ ≤ _ := h2
    _ = _ := h3
    _ ≤ _ := h4
    _ = M * (1 + Real.log M) ^ 3 := by ring

end PrimeCarleson.Proof.Fplus31

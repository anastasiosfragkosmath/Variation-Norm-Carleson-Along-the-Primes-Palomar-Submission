module

public import PrimeCarleson.Proof.Paper.P9.GlobalShell
public import PrimeCarleson.Proof.Paper.Defs.Weights
public import PrimeCarleson.Proof.Common.TotientBound
public import PrimeCarleson.Proof.Goal0.Divisors

/-!
# The divisor and totient weights, and the interpolation weight

Source: main paper `s:red`, L1530–L1543, and the numerical half of `l:red-var-l2` (L1706–L1715).

* `weight_sum_le`: `∑_{Q/2 < q ≤ Q} φ(q)⁻¹ ∑_{d ∣ q} d^a ≤ C_{a,δ} Q^{a+δ}` for `a ≥ 0`, `δ > 0`
  (the paper's `Q^{a+o(1)}`), from the totient lower bound `φ(q) ≫ q / log log (10 + q)` and the
  divisor bound;
* `exists_interp_theta`: if `p` lies strictly between `2` and `s`, then `1/p = θ/2 + (1-θ)/s` for
  a unique `θ ∈ (0, 1)`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

/-- `log log (10 + y) > 0` for `y ≥ 0`. -/
theorem loglog_pos {y : ℝ} (hy : 0 ≤ y) : 0 < Real.log (Real.log (10 + y)) := by
  have h10 : Real.exp 1 < 10 + y := by
    have := Real.exp_one_lt_d9
    linarith
  have h1 : 1 < Real.log (10 + y) := (Real.lt_log_iff_exp_lt (by linarith)).2 h10
  exact Real.log_pos h1

/-- `log log (10 + y)` is monotone in `y ≥ 0`. -/
theorem loglog_mono {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) :
    Real.log (Real.log (10 + y)) ≤ Real.log (Real.log (10 + z)) := by
  have h1 : 0 < Real.log (10 + y) := Real.log_pos (by linarith)
  exact Real.log_le_log h1 (Real.log_le_log (by linarith) (by linarith))

/-- **The numerical half of the crude `ℓ^s` bound of `l:red-var-l2`** (L1710–L1715): for `a ≥ 0` and
`δ > 0` there is `C` with `∑_{Q/2 < q ≤ Q} φ(q)⁻¹ ∑_{d ∣ q} d^a ≤ C Q^{a+δ}` for every integer
`Q ≥ 1` (the paper's `Q^{a + o(1)}`; the totient lower bound `e:totientbound` and the divisor
bound). -/
theorem weight_sum_le {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℕ, 1 ≤ Q →
      ∑ q ∈ Finset.Ioc (Q / 2) Q, (1 / (Nat.totient q : ℝ)) * ∑ d ∈ q.divisors, (d : ℝ) ^ a ≤
        C * (Q : ℝ) ^ (a + δ) := by
  obtain ⟨c, hc, hφ⟩ := exists_totient_lower_bound
  obtain ⟨Cτ, hCτ1, hτ⟩ := exists_card_divisors_le_rpow (δ := δ / 2) (by positivity)
  obtain ⟨Cl, hCl, hll⟩ := loglog_le_rpow (ε := δ / 2) (by positivity)
  refine ⟨2 * Cτ * Cl / c, by positivity, fun Q hQ => ?_⟩
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  set L : ℝ := Real.log (Real.log (10 + (Q : ℝ))) with hL
  have hL0 : 0 < L := loglog_pos hQ0.le
  have hLb : L ≤ Cl * (Q : ℝ) ^ (δ / 2) := hll _ hQ1
  have hterm : ∀ q ∈ Finset.Ioc (Q / 2) Q, (1 / (Nat.totient q : ℝ)) *
      ∑ d ∈ q.divisors, (d : ℝ) ^ a ≤
        (2 / c) * (L / Q) * (Cτ * (Q : ℝ) ^ (δ / 2 + a)) := by
    intro q hq
    rw [Finset.mem_Ioc] at hq
    have hqQ : q ≤ Q := hq.2
    have hq2 : (Q : ℝ) / 2 < q := nat_div_two_lt_iff.1 hq.1
    have hq1 : 1 ≤ q := by
      have : (0 : ℝ) < q := by linarith
      exact_mod_cast this
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    have hqQ' : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    have hLq := loglog_pos hq0.le
    have hLqL : Real.log (Real.log (10 + (q : ℝ))) ≤ L := loglog_mono hq0.le hqQ'
    have hφq := hφ q hq1
    have hφpos : 0 < c * (q : ℝ) / Real.log (Real.log (10 + (q : ℝ))) := by positivity
    have h1 : 1 / (Nat.totient q : ℝ) ≤ 2 / c * (L / Q) := by
      calc 1 / (Nat.totient q : ℝ) ≤ 1 / (c * (q : ℝ) / Real.log (Real.log (10 + (q : ℝ)))) :=
            one_div_le_one_div_of_le hφpos hφq
        _ = Real.log (Real.log (10 + (q : ℝ))) / (c * q) := by field_simp
        _ ≤ L / (c * q) := by gcongr
        _ ≤ L / (c * (Q / 2)) := by gcongr
        _ = 2 / c * (L / Q) := by field_simp
    have h2 : ∑ d ∈ q.divisors, (d : ℝ) ^ a ≤ Cτ * (Q : ℝ) ^ (δ / 2 + a) := by
      have hd : ∀ d ∈ q.divisors, (d : ℝ) ^ a ≤ (q : ℝ) ^ a := fun d hd =>
        Real.rpow_le_rpow (by positivity)
          (by exact_mod_cast Nat.divisor_le hd) ha
      calc ∑ d ∈ q.divisors, (d : ℝ) ^ a ≤ ∑ _d ∈ q.divisors, (q : ℝ) ^ a :=
            Finset.sum_le_sum hd
        _ = (q.divisors.card : ℝ) * (q : ℝ) ^ a := by simp
        _ ≤ (Cτ * (q : ℝ) ^ (δ / 2)) * (q : ℝ) ^ a := by
            gcongr
            exact hτ q hq1
        _ ≤ (Cτ * (Q : ℝ) ^ (δ / 2)) * (Q : ℝ) ^ a := by
            have hCτ0 : 0 ≤ Cτ := by linarith
            gcongr
        _ = Cτ * (Q : ℝ) ^ (δ / 2 + a) := by
            rw [Real.rpow_add hQ0]; ring
    have h3 : 0 ≤ ∑ d ∈ q.divisors, (d : ℝ) ^ a := Finset.sum_nonneg fun d _ => by positivity
    exact mul_le_mul h1 h2 h3 (by positivity)
  calc ∑ q ∈ Finset.Ioc (Q / 2) Q, (1 / (Nat.totient q : ℝ)) * ∑ d ∈ q.divisors, (d : ℝ) ^ a
      ≤ ∑ _q ∈ Finset.Ioc (Q / 2) Q, (2 / c) * (L / Q) * (Cτ * (Q : ℝ) ^ (δ / 2 + a)) :=
        Finset.sum_le_sum hterm
    _ = ((Finset.Ioc (Q / 2) Q).card : ℝ) *
        ((2 / c) * (L / Q) * (Cτ * (Q : ℝ) ^ (δ / 2 + a))) := by simp
    _ ≤ (Q : ℝ) * ((2 / c) * (L / Q) * (Cτ * (Q : ℝ) ^ (δ / 2 + a))) := by
        have hcard : ((Finset.Ioc (Q / 2) Q).card : ℝ) ≤ Q := by
          rw [Nat.card_Ioc]; exact_mod_cast Nat.sub_le _ _
        have : 0 ≤ (2 / c) * (L / Q) * (Cτ * (Q : ℝ) ^ (δ / 2 + a)) := by
          have : 0 ≤ Cτ := by linarith
          positivity
        exact mul_le_mul_of_nonneg_right hcard this
    _ = (2 * Cτ / c) * L * (Q : ℝ) ^ (δ / 2 + a) := by field_simp
    _ ≤ (2 * Cτ / c) * (Cl * (Q : ℝ) ^ (δ / 2)) * (Q : ℝ) ^ (δ / 2 + a) := by
        have : 0 ≤ Cτ := by linarith
        gcongr
    _ = 2 * Cτ * Cl / c * (Q : ℝ) ^ (a + δ) := by
        have h : (Q : ℝ) ^ (δ / 2) * (Q : ℝ) ^ (δ / 2 + a) = (Q : ℝ) ^ (a + δ) := by
          rw [← Real.rpow_add hQ0]; congr 1; ring
        rw [← h]; ring

/-- The interpolation weight: if `p` lies strictly between `2` and `s` then
`1/p = θ/2 + (1-θ)/s` for a unique `θ ∈ (0, 1)`. -/
theorem exists_interp_theta {p s : ℝ} (hp : 0 < p) (hs : 0 < s)
    (h : (p < 2 ∧ s < p) ∨ (2 < p ∧ p < s)) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ 1 / p = θ / 2 + (1 - θ) / s := by
  rcases h with ⟨hp2, hsp⟩ | ⟨hp2, hps⟩
  · have hden : 1 / 2 - 1 / s < 0 := by
      have : 1 / 2 < 1 / s := by
        rw [div_lt_div_iff₀ (by norm_num) hs]; linarith
      linarith
    have hnum : 1 / p - 1 / s < 0 := by
      have : 1 / p < 1 / s := one_div_lt_one_div_of_lt hs hsp
      linarith
    set θ : ℝ := (1 / p - 1 / s) / (1 / 2 - 1 / s) with hθ
    have hθ1 : θ * (1 / 2 - 1 / s) = 1 / p - 1 / s := div_mul_cancel₀ _ hden.ne
    refine ⟨θ, div_pos_of_neg_of_neg hnum hden, ?_, ?_⟩
    · rw [hθ, div_lt_one_of_neg hden]
      have : 1 / 2 < 1 / p := by rw [div_lt_div_iff₀ (by norm_num) hp]; linarith
      linarith
    · linear_combination (-1 : ℝ) * hθ1
  · have hs2 : 2 < s := hp2.trans hps
    have hden : 0 < 1 / 2 - 1 / s := by
      have : 1 / s < 1 / 2 := by rw [div_lt_div_iff₀ hs (by norm_num)]; linarith
      linarith
    have hnum : 0 < 1 / p - 1 / s := by
      have : 1 / s < 1 / p := one_div_lt_one_div_of_lt hp hps
      linarith
    set θ : ℝ := (1 / p - 1 / s) / (1 / 2 - 1 / s) with hθ
    have hθ1 : θ * (1 / 2 - 1 / s) = 1 / p - 1 / s := div_mul_cancel₀ _ hden.ne'
    refine ⟨θ, div_pos hnum hden, ?_, ?_⟩
    · rw [hθ, div_lt_one hden]
      have : 1 / p < 1 / 2 := by rw [div_lt_div_iff₀ hp (by norm_num)]; linarith
      linarith
    · linear_combination (-1 : ℝ) * hθ1

end PrimeCarleson.Proof.Paper

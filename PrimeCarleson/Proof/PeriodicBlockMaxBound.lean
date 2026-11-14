module

public import PrimeCarleson.Frozen.PeriodicBlockMax
public import PrimeCarleson.Proof.Goal0.Assembly
public import PrimeCarleson.Proof.Goal0.Exponents

/-!
# Provider for `PrimeCarleson.periodicBlockMax_bound`

Proves the statement under the separate name `PrimeCarleson.Proof.periodicBlockMax_bound`.
Only `PrimeCarleson.Frozen.PeriodicBlockMaxBound` imports this module.

Source: main paper `p:goal0`, L2545–L2550, with the implied constant made explicit. With `Q = 2^j`,
the divisor-bound constant `C` for `δ = ε` (`τ(n) ≤ C n^ε`), and `κ₀ = 1`, run the bound for one
period (`Goal0.l2_periodicBlockMax_le_of_bounds`) with `M = 2CQ^{ε-1}`, `σ = 2C⁴Q^{4ε-1}`,
`η = Q^{-3ε}/(2C²)` and `X = Q^{-1-ε}|B|`; then `X + σ √(3/η³) ≤ (A + 48C^{10}) Q^{κ-1-ε}`
(`Goal0.exponent_bound`). The constant is `A + 48 C^{10}`, depending on `ε` and `A` only.
-/

@[expose] public noncomputable section

open Finset Real

namespace PrimeCarleson.Proof

open Goal0

/-- Proposition `p:goal0`, with an explicit constant. -/
theorem periodicBlockMax_bound :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ ε : ℝ, 0 < ε → ε ≤ κ / 100 →
      ∀ A : ℝ, ∃ C : ℝ, ∀ (j : ℕ) (B : Finset ℕ),
        B ⊆ (Finset.Ioc (2 ^ j / 2) (2 ^ j)).filter Squarefree →
        ((2 : ℝ) ^ j) ^ κ ≤ A * B.card → (B.card : ℝ) ≤ A * ((2 : ℝ) ^ j) ^ κ →
        ∀ f : ℤ → ℂ, Function.Periodic f ((B.lcm id : ℕ) : ℤ) →
          ∑ x ∈ Finset.range (B.lcm id), periodicBlockMax B f x ^ 2 ≤
            (C * ((2 : ℝ) ^ j) ^ (κ - 1 - ε)) ^ 2 *
              ∑ x ∈ Finset.range (B.lcm id), ‖f x‖ ^ 2 := by
  refine ⟨1, one_pos, fun κ hκ hκ1 ε hε hεκ A => ?_⟩
  obtain ⟨Cτ, hCτ1, hCτ⟩ := exists_card_divisors_le_rpow hε
  refine ⟨A + 48 * Cτ ^ 10, fun j B hB _ hup f hf => ?_⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = (2 : ℝ) ^ j := ⟨_, rfl⟩
  rw [← hQdef] at hup ⊢
  have hQ1 : 1 ≤ Q := hQdef ▸ one_le_pow₀ (by norm_num)
  have hQ0 : 0 < Q := by linarith
  have hε1 : ε < 1 := by linarith
  have hmem : ∀ q ∈ B, 0 < q ∧ Squarefree q ∧ Q / 2 ≤ q ∧ (q : ℝ) ≤ Q :=
    fun q hq => hQdef ▸ mem_block_bounds (hB hq)
  have hCτ0 : 0 ≤ Cτ := by linarith
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = Cτ * Q ^ ε := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := hKdef ▸ by positivity
  -- divisor bound below `Q`
  have hτQ : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ Q → (n.divisors.card : ℝ) ≤ K := by
    intro n hn hnQ
    rw [hKdef]
    exact (hCτ n hn).trans
      (mul_le_mul_of_nonneg_left (rpow_le_rpow (Nat.cast_nonneg n) hnQ hε.le) hCτ0)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = 2 * Cτ * Q ^ (ε - 1) := ⟨_, rfl⟩
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = 2 * Cτ ^ 4 * Q ^ (4 * ε - 1) := ⟨_, rfl⟩
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = Q ^ (-3 * ε) / (2 * Cτ ^ 2) := ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = Q ^ (-1 - ε) * B.card := ⟨_, rfl⟩
  have hM : ∀ q ∈ B, ((q.totient : ℝ))⁻¹ ≤ M := fun q hq =>
    hMdef ▸ inv_totient_le hε hε1 hCτ (hmem q hq).1 (hmem q hq).2.2.1 hQ1
  have hM0 : 0 ≤ M := hMdef ▸ by positivity
  have hη0 : 0 < η := hηdef ▸ by positivity
  have hη1 : η ≤ 1 := by
    rw [hηdef, div_le_one (by positivity)]
    calc Q ^ (-3 * ε) ≤ 1 := rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith)
      _ ≤ 2 * Cτ ^ 2 := by nlinarith
  have hσ : ∀ q ∈ B, ∀ d ∈ q.divisors,
      d.divisors.card * M * ∑ r ∈ d.divisors, (r.divisors.card : ℝ) ≤ σ := by
    intro q hq d hd
    have hq0 := (hmem q hq).1
    have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hdQ : (d : ℝ) ≤ Q :=
      (by exact_mod_cast Nat.le_of_dvd hq0 hdq : (d : ℝ) ≤ q).trans (hmem q hq).2.2.2
    have hτd : (d.divisors.card : ℝ) ≤ K := hτQ d hd0 hdQ
    have hsum : ∑ r ∈ d.divisors, (r.divisors.card : ℝ) ≤ d.divisors.card * K := by
      calc ∑ r ∈ d.divisors, (r.divisors.card : ℝ)
          ≤ ∑ _r ∈ d.divisors, (d.divisors.card : ℝ) := Finset.sum_le_sum fun r hr => by
            exact_mod_cast card_divisors_le_of_dvd hd0 (Nat.dvd_of_mem_divisors hr)
        _ = d.divisors.card * d.divisors.card := by rw [sum_const, nsmul_eq_mul]
        _ ≤ d.divisors.card * K := mul_le_mul_of_nonneg_left hτd (Nat.cast_nonneg _)
    have hτ2 : (d.divisors.card : ℝ) * d.divisors.card ≤ K * K :=
      mul_le_mul hτd hτd (Nat.cast_nonneg _) hK0
    calc (d.divisors.card : ℝ) * M * ∑ r ∈ d.divisors, (r.divisors.card : ℝ)
        ≤ (d.divisors.card : ℝ) * M * (d.divisors.card * K) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg (Nat.cast_nonneg _) hM0)
      _ = ((d.divisors.card : ℝ) * d.divisors.card) * (M * K) := by ring
      _ ≤ (K * K) * (M * K) := mul_le_mul_of_nonneg_right hτ2 (mul_nonneg hM0 hK0)
      _ = σ := by
          rw [hKdef, hMdef, hσdef, show 4 * ε - 1 = ε + (ε - 1) + ε + ε by ring,
            rpow_add hQ0, rpow_add hQ0, rpow_add hQ0]
          ring
  have hβ : (∑ q ∈ B, ((q.totient : ℝ))⁻¹ * q.divisors.card) * η ≤ X := by
    have h1 : ∑ q ∈ B, ((q.totient : ℝ))⁻¹ * q.divisors.card ≤ ∑ _q ∈ B, M * K :=
      Finset.sum_le_sum fun q hq => mul_le_mul (hM q hq) (hτQ q (hmem q hq).1 (hmem q hq).2.2.2)
        (Nat.cast_nonneg _) hM0
    calc (∑ q ∈ B, ((q.totient : ℝ))⁻¹ * q.divisors.card) * η
        ≤ (∑ _q ∈ B, M * K) * η := mul_le_mul_of_nonneg_right h1 hη0.le
      _ = X := by
          rw [sum_const, nsmul_eq_mul, hXdef, hMdef, hKdef, hηdef,
            show (-1 - ε) = (ε - 1) + ε + -3 * ε by ring, rpow_add hQ0, rpow_add hQ0]
          field_simp
  have hX0 : 0 ≤ X := hXdef ▸ by positivity
  have hσ0 : 0 ≤ σ := hσdef ▸ by positivity
  have key := l2_periodicBlockMax_le_of_bounds (fun q hq => (hmem q hq).2.1)
    (fun q hq => (hmem q hq).1) hX0 hσ0 hη0 hη1 hM0 hM hσ hβ hf
  have hK : X + σ * √(3 / η ^ 3) ≤ (A + 48 * Cτ ^ 10) * Q ^ (κ - 1 - ε) := by
    rw [hXdef, hσdef, hηdef]
    exact exponent_bound hε (by linarith) hCτ1 hQ1 hup
  have hl2f := l2_nonneg (B.lcm id) (fun x => ‖f x‖)
  have hsq : l2 (B.lcm id) (periodicBlockMax B f) ^ 2 ≤
      ((A + 48 * Cτ ^ 10) * Q ^ (κ - 1 - ε)) ^ 2 * l2 (B.lcm id) (fun x => ‖f x‖) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (l2_nonneg _ _)
      (key.trans (mul_le_mul_of_nonneg_right hK hl2f)) 2
  rw [l2_sq, l2_sq] at hsq
  exact hsq

end PrimeCarleson.Proof

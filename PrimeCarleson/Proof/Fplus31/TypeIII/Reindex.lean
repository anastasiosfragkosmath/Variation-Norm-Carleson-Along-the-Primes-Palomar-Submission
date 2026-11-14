module

public import Mathlib.Data.Finset.NatDivisors
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Reindexing of divisor sums, and partial summation against `log`

Part of the Vaughan decomposition in the proof of [F+] Proposition 3.1: the elementary bookkeeping
behind the type I / type II decomposition of `Λ - Λ_C` (Leng23 Lemma `l:type1type2decomposition`,
arXiv:2312.10772v5 TeX L1186).

* `sum_Icc_divisors`: `∑_{n ≤ N} ∑_{c ∣ n} G c (n/c) = ∑_{c ≤ N} ∑_{w ≤ N/c} G c w`;
* `dvdSum f d K = ∑_{n ≤ K, d ∣ n} f n`, the type I atom `∑_{m ≤ K/d} f (d m)`
  (`dvdSum_eq_sum_mul`), with `norm_dvdSum_le`: `‖dvdSum f d K‖ ≤ K/d` for a 1-bounded `f`;
* `sum_Icc_mul_divisors`: `∑_{n ≤ N} (∑_{d ∣ n} α d) f n = ∑_{d ≤ N} α d · dvdSum f d N`;
* `sum_dvd_mul_log`: partial summation against `log n = ∑_{K < n} (log (K+1) - log K)`,
  `∑_{n ≤ N, d ∣ n} f n log n
    = log N · dvdSum f d N - ∑_{K < N} (log (K+1) - log K) · dvdSum f d K`
  (the "fundamental theorem of calculus" for `log (n/d)` in Tao–Teräväinen's Vaughan-type
  decomposition, arXiv:2107.02158v4 TeX (`orthogonality.tex`) L218-L222).
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- `∑_{n ≤ N} ∑_{c ∣ n} G c (n / c) = ∑_{c ≤ N} ∑_{w ≤ N / c} G c w`
(the substitution `n = c w`). -/
theorem sum_Icc_divisors {M : Type*} [AddCommMonoid M] (N : ℕ) (G : ℕ → ℕ → M) :
    ∑ n ∈ Icc 1 N, ∑ c ∈ n.divisors, G c (n / c) =
      ∑ c ∈ Icc 1 N, ∑ w ∈ Icc 1 (N / c), G c w := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => (⟨x.2, x.1 / x.2⟩ : Σ _ : ℕ, ℕ))
    (fun y _ => (⟨y.1 * y.2, y.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, c⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at h ⊢
    obtain ⟨⟨hn1, hnN⟩, hcn, hn0⟩ := h
    have hc1 : 1 ≤ c := Nat.pos_of_dvd_of_pos hcn (by omega)
    have hcn' : c ≤ n := Nat.le_of_dvd (by omega) hcn
    refine ⟨⟨hc1, by omega⟩, Nat.div_pos hcn' (by omega), Nat.div_le_div_right hnN⟩
  · rintro ⟨c, w⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at h ⊢
    obtain ⟨⟨hc1, hcN⟩, hw1, hwN⟩ := h
    have : c * w ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp hwN |> fun h => by
      simpa [mul_comm] using h
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (by positivity), this⟩, dvd_mul_right _ _, ?_⟩
    positivity
  · rintro ⟨n, c⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at h
    obtain ⟨_, hcn, _⟩ := h
    simp [Nat.mul_div_cancel' hcn]
  · rintro ⟨c, w⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Icc] at h
    obtain ⟨⟨hc1, _⟩, _, _⟩ := h
    simp [Nat.mul_div_cancel_left _ (by omega : 0 < c)]
  · intro x _
    rfl

/-- The type I atom `∑_{n ≤ K, d ∣ n} f n`. -/
def dvdSum (f : ℕ → ℂ) (d K : ℕ) : ℂ := ∑ n ∈ (Icc 1 K).filter (d ∣ ·), f n

/-- `∑_{n ≤ K, d ∣ n} f n = ∑_{m ≤ K/d} f (d m)` for `d ≥ 1`. -/
theorem dvdSum_eq_sum_mul (f : ℕ → ℂ) {d : ℕ} (hd : 1 ≤ d) (K : ℕ) :
    dvdSum f d K = ∑ m ∈ Icc 1 (K / d), f (d * m) := by
  unfold dvdSum
  refine Finset.sum_nbij' (fun n => n / d) (fun m => d * m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    obtain ⟨⟨hn1, hnK⟩, hdn⟩ := hn
    have : d ≤ n := Nat.le_of_dvd (by omega) hdn
    exact ⟨Nat.div_pos this (by omega), Nat.div_le_div_right hnK⟩
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    obtain ⟨hm1, hmK⟩ := hm
    have : m * d ≤ K := (Nat.le_div_iff_mul_le (by omega)).mp hmK
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (by positivity), by rwa [mul_comm]⟩, dvd_mul_right _ _⟩
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m hm
    exact Nat.mul_div_cancel_left _ (by omega)
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Nat.mul_div_cancel' hn.2]

/-- The number of multiples of `d` in `[1, K]` is `K / d`. -/
theorem card_filter_dvd_Icc (d K : ℕ) : ((Icc 1 K).filter (d ∣ ·)).card = K / d := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  congr 1

/-- `‖∑_{n ≤ K, d ∣ n} f n‖ ≤ K / d` for a function bounded by `1` on `[1, K]`. -/
theorem norm_dvdSum_le (f : ℕ → ℂ) (d K : ℕ) (hf : ∀ n ∈ Icc 1 K, ‖f n‖ ≤ 1) :
    ‖dvdSum f d K‖ ≤ (K : ℝ) / d := by
  unfold dvdSum
  calc ‖∑ n ∈ (Icc 1 K).filter (d ∣ ·), f n‖
      ≤ ∑ n ∈ (Icc 1 K).filter (d ∣ ·), ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ (Icc 1 K).filter (d ∣ ·), (1 : ℝ) :=
        Finset.sum_le_sum fun n hn => hf n (Finset.mem_filter.mp hn).1
    _ = (K / d : ℕ) := by rw [Finset.sum_const, card_filter_dvd_Icc]; simp
    _ ≤ (K : ℝ) / d := Nat.cast_div_le

/-- Interchange of summation: `∑_{n ≤ N} (∑_{d ∣ n} α d) f n = ∑_{d ≤ N} α d · dvdSum f d N`. -/
theorem sum_Icc_mul_divisors (N : ℕ) (α f : ℕ → ℂ) :
    ∑ n ∈ Icc 1 N, (∑ d ∈ n.divisors, α d) * f n = ∑ d ∈ Icc 1 N, α d * dvdSum f d N := by
  simp_rw [Finset.sum_mul, dvdSum, Finset.mul_sum]
  refine Finset.sum_comm' fun n d => ?_
  simp only [Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hn1, hnN⟩, hdn, _⟩
    have h1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdn (by omega)
    have h2 : d ≤ n := Nat.le_of_dvd (by omega) hdn
    exact ⟨⟨⟨hn1, hnN⟩, hdn⟩, h1, by omega⟩
  · rintro ⟨⟨⟨hn1, hnN⟩, hdn⟩, _, _⟩
    exact ⟨⟨hn1, hnN⟩, hdn, by omega⟩

/-- The increment `log (K+1) - log K`. -/
def logStep (K : ℕ) : ℝ := Real.log ((K : ℝ) + 1) - Real.log K

/-- The increments `log (K+1) - log K` are nonnegative. -/
theorem logStep_nonneg (K : ℕ) : 0 ≤ logStep K := by
  unfold logStep
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  · have : (0 : ℝ) < K := by exact_mod_cast hK
    have := Real.log_le_log this (by linarith : (K : ℝ) ≤ K + 1)
    linarith

/-- `log n = ∑_{K < n} (log (K+1) - log K)`. -/
theorem sum_range_logStep (n : ℕ) : ∑ K ∈ range n, logStep K = Real.log n := by
  have := Finset.sum_range_sub (fun i : ℕ => Real.log (i : ℝ)) n
  simpa [logStep] using this

/-- Partial summation against `log n = ∑_{K < n} (log (K+1) - log K)`:
`∑_{n ≤ N, d ∣ n} f n log n
  = log N · dvdSum f d N - ∑_{K < N} (log (K+1) - log K) · dvdSum f d K`. -/
theorem sum_dvd_mul_log (f : ℕ → ℂ) (d N : ℕ) :
    ∑ n ∈ (Icc 1 N).filter (d ∣ ·), f n * (Real.log n : ℂ) =
      (Real.log N : ℂ) * dvdSum f d N -
        ∑ K ∈ range N, (logStep K : ℂ) * dvdSum f d K := by
  have h1 : ∀ n ∈ (Icc 1 N).filter (d ∣ ·), f n * (Real.log n : ℂ) =
      ∑ K ∈ range N, (logStep K : ℂ) * (if K < n then f n else 0) := by
    intro n hn
    have hnN : n ≤ N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    have : (Real.log n : ℂ) = ∑ K ∈ range N, (logStep K : ℂ) * (if K < n then 1 else 0) := by
      rw [← sum_range_logStep n]
      push_cast
      have hsub : range n ⊆ range N := Finset.range_subset_range.mpr hnN
      rw [← Finset.sum_subset hsub (fun K hK hK' => by
        simp only [Finset.mem_range] at hK hK'
        simp [show ¬ K < n by omega])]
      refine Finset.sum_congr rfl fun K hK => ?_
      simp [Finset.mem_range.mp hK]
    rw [mul_comm, this, Finset.sum_mul]
    refine Finset.sum_congr rfl fun K _ => ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 : ∀ K ∈ range N, ∑ n ∈ (Icc 1 N).filter (d ∣ ·), (logStep K : ℂ) *
      (if K < n then f n else 0) =
      (logStep K : ℂ) * dvdSum f d N - (logStep K : ℂ) * dvdSum f d K := by
    intro K hK
    have hKN : K ≤ N := (Finset.mem_range.mp hK).le
    rw [← Finset.mul_sum, ← mul_sub]
    congr 1
    have hsplit := Finset.sum_filter_add_sum_filter_not ((Icc 1 N).filter (d ∣ ·))
      (fun n => n ≤ K) f
    have hset : ((Icc 1 N).filter (d ∣ ·)).filter (fun n => n ≤ K) = (Icc 1 K).filter (d ∣ ·) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨h1, _⟩, h3⟩, h4⟩
        exact ⟨⟨h1, h4⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨⟨h1, by omega⟩, h3⟩, h2⟩
    rw [hset] at hsplit
    have hite : ∑ n ∈ (Icc 1 N).filter (d ∣ ·), (if K < n then f n else 0) =
        ∑ n ∈ ((Icc 1 N).filter (d ∣ ·)).filter (fun n => ¬ n ≤ K), f n := by
      conv_rhs => rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp [not_le]
    rw [hite]
    unfold dvdSum
    linear_combination hsplit
  rw [Finset.sum_congr rfl h2, Finset.sum_sub_distrib, ← Finset.sum_mul]
  congr 1
  rw [← Complex.ofReal_sum, sum_range_logStep]

end PrimeCarleson.Proof.Fplus31

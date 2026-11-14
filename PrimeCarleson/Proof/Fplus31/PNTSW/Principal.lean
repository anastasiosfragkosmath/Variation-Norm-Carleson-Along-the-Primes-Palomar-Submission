module

public import PrimeCarleson.Proof.Fplus31.PNTSW.Zeta
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Data.Nat.Log
public import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# The Riesz mean of the principal character from the classical zero-free region

Part of the prime number theorem in progressions on the classical zero-free region
(`PNTSW/Main.lean`). The principal character modulo `q` is `Λ` with the prime powers dividing `q`
removed:

* `sum_vonMangoldt_not_coprime_le`: `∑_{n ≤ M, (n,q) > 1} Λ(n) ≤ (log₂ M) log q`;
* `riesz_principal_sw`: for `y ≥ y₀` and `log q ≤ √(log y)`,
  `‖∑_{n ≤ y} χ₀(n)Λ(n)(y-n) - (y-1)²/2‖ ≤ 2 y² exp (-c₁ √(log y))`.
-/

@[expose] public noncomputable section

open Complex ArithmeticFunction Filter
open scoped Real

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.PNTSW

/-- `∑_{n ≤ M, gcd(n,q) > 1} Λ(n) ≤ (log₂ M) log q`. -/
theorem sum_vonMangoldt_not_coprime_le {q : ℕ} (hq : 1 ≤ q) (M : ℕ) :
    ∑ n ∈ (Finset.Icc 1 M).filter (fun n : ℕ => ¬ Nat.Coprime n q), Λ n ≤
      (Nat.log 2 M : ℝ) * Real.log q := by
  set J : ℕ := Nat.log 2 M with hJ
  have hsub : ((Finset.Icc 1 M).filter (fun n : ℕ => ¬ Nat.Coprime n q)).filter
      (fun m => Λ m ≠ 0) ⊆ (q ^ J).divisors := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨⟨hm1, hmM⟩, hcop⟩, hΛ⟩ := hm
    obtain ⟨p, k, hp, hk, hpk⟩ := vonMangoldt_ne_zero_iff.mp hΛ
    have hp' : p.Prime := Nat.prime_iff.mpr hp
    have hpq : p ∣ q := by
      by_contra hn
      exact hcop (hpk ▸ ((Nat.Prime.coprime_iff_not_dvd hp').mpr hn).pow_left k)
    have hkJ : k ≤ J := by
      refine Nat.le_log_of_pow_le (by norm_num) ?_
      calc 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp'.two_le k
        _ = m := hpk
        _ ≤ M := hmM
    rw [Nat.mem_divisors]
    refine ⟨?_, (pow_pos hq J).ne'⟩
    rw [← hpk]
    exact (pow_dvd_pow_of_dvd hpq k).trans (pow_dvd_pow q hkJ)
  calc ∑ n ∈ (Finset.Icc 1 M).filter (fun n : ℕ => ¬ Nat.Coprime n q), Λ n
      = ∑ n ∈ ((Finset.Icc 1 M).filter (fun n : ℕ => ¬ Nat.Coprime n q)).filter
          (fun m => Λ m ≠ 0), Λ n := (Finset.sum_filter_ne_zero _).symm
    _ ≤ ∑ m ∈ (q ^ J).divisors, Λ m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => vonMangoldt_nonneg
    _ = Real.log ((q ^ J : ℕ) : ℝ) := vonMangoldt_sum
    _ = (J : ℝ) * Real.log q := by rw [Nat.cast_pow, Real.log_pow]

/-- The principal character modulo `q` is the indicator of `(n, q) = 1`. -/
theorem principal_char_apply {q : ℕ} [NeZero q] (n : ℕ) :
    (1 : DirichletCharacter ℂ q) n = if Nat.Coprime n q then 1 else 0 := by
  split_ifs with h
  · exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr h)
  · exact MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime n q).mp hu))

/-- **The Riesz mean of the principal character**, for `y ≥ y₀` and `log q ≤ √(log y)`. -/
theorem riesz_principal_sw (hZ : ClassicalZeroFreeRegion) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ y₀ : ℝ, 1 ≤ y₀ ∧ ∀ y : ℝ, y₀ ≤ y → ∀ (q : ℕ) [NeZero q],
      Real.log q ≤ √(Real.log y) →
      ‖∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ) * ((y : ℂ) - n) -
          (((y - 1) ^ 2 / 2 : ℝ) : ℂ)‖ ≤ 2 * (y ^ 2 * Real.exp (-(c₁ * √(Real.log y)))) := by
  obtain ⟨c, hc, y₁, hy₁, hz⟩ := riesz_zeta_sw hZ
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c₁ : ℝ := min c 1 with hc₁
  have hc₁0 : 0 < c₁ := lt_min hc one_pos
  have hc₁c : c₁ ≤ c := min_le_left _ _
  have hc₁1 : c₁ ≤ 1 := min_le_right _ _
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp
    (Fplus31.eventually_poly_le_exp 3 (1 / Real.log 2) 1 one_pos)
  set u₁ : ℝ := max (max u₀ 2) (√(Real.log y₁)) with hu₁
  have hu₁2 : 2 ≤ u₁ := le_trans (le_max_right u₀ 2) (le_max_left (max u₀ 2) _)
  refine ⟨c₁, hc₁0, Real.exp (u₁ ^ 2), Real.one_le_exp (by positivity), ?_⟩
  intro y hy q _ hqy
  have hy1 : 1 ≤ y := le_trans (Real.one_le_exp (by positivity)) hy
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
  have hlogy : u₁ ^ 2 ≤ Real.log y := by
    have := Real.log_le_log (Real.exp_pos _) hy
    rwa [Real.log_exp] at this
  set u : ℝ := √(Real.log y) with hu
  have hlog : Real.log y = u ^ 2 := by
    rw [hu, Real.sq_sqrt (Real.log_nonneg hy1)]
  have hu1 : u₁ ≤ u := by
    rw [hu]
    exact Real.le_sqrt_of_sq_le hlogy
  have hu2 : 2 ≤ u := le_trans hu₁2 hu1
  have hu0u : u₀ ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu1
  have hyy₁ : y₁ ≤ y := by
    have h1 : √(Real.log y₁) ≤ u := le_trans (le_max_right _ _) hu1
    have h2 : Real.log y₁ ≤ u ^ 2 := by
      calc Real.log y₁ = √(Real.log y₁) ^ 2 := (Real.sq_sqrt (Real.log_nonneg hy₁)).symm
        _ ≤ u ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    have : Real.log y₁ ≤ Real.log y := by rw [hlog]; exact h2
    exact (Real.log_le_log_iff (lt_of_lt_of_le one_pos hy₁) hy0).mp this
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set M : ℕ := ⌊y⌋₊ with hM
  set RΛ : ℝ := ∑ n ∈ Finset.Icc 1 M, Λ n * (y - n) with hRΛ
  set corr : ℝ := ∑ n ∈ (Finset.Icc 1 M).filter (fun n : ℕ => ¬ Nat.Coprime n q),
    Λ n * (y - n) with hcorr
  have hsplit : ∑ n ∈ Finset.Icc 1 M, (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ) *
      ((y : ℂ) - n) = ((RΛ - corr : ℝ) : ℂ) := by
    have h1 : ∀ n ∈ Finset.Icc 1 M, (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ) * ((y : ℂ) - n) =
        ((if Nat.Coprime n q then Λ n * (y - n) else 0 : ℝ) : ℂ) := by
      intro n _
      rw [principal_char_apply]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl h1, ← Complex.ofReal_sum, ← Finset.sum_filter]
    have h2 := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 M) (fun n : ℕ => Nat.Coprime n q)
      (fun n => Λ n * (y - n))
    congr 1
    rw [hRΛ, hcorr, ← h2]
    ring
  rw [hsplit]
  have hcorr0 : 0 ≤ corr := by
    refine Finset.sum_nonneg fun n hn => mul_nonneg vonMangoldt_nonneg ?_
    have := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    have : (n : ℝ) ≤ y := (Nat.cast_le.mpr this.2).trans (Nat.floor_le hy0.le)
    exact sub_nonneg.mpr this
  have hcorr1 : corr ≤ y * ((Nat.log 2 M : ℝ) * Real.log q) := by
    have hterm : ∀ n ∈ (Finset.Icc 1 M).filter (fun n : ℕ => ¬ Nat.Coprime n q),
        Λ n * (y - n) ≤ Λ n * y := by
      intro n hn
      exact mul_le_mul_of_nonneg_left (sub_le_self _ (Nat.cast_nonneg n))
        vonMangoldt_nonneg
    calc corr ≤ ∑ n ∈ (Finset.Icc 1 M).filter (fun n : ℕ => ¬ Nat.Coprime n q), Λ n * y :=
          Finset.sum_le_sum hterm
      _ = (∑ n ∈ (Finset.Icc 1 M).filter (fun n : ℕ => ¬ Nat.Coprime n q), Λ n) * y := by
          rw [Finset.sum_mul]
      _ ≤ ((Nat.log 2 M : ℝ) * Real.log q) * y :=
          mul_le_mul_of_nonneg_right (sum_vonMangoldt_not_coprime_le (NeZero.pos q) M) hy0.le
      _ = _ := by ring
  have hlogJ : (Nat.log 2 M : ℝ) * Real.log 2 ≤ Real.log y := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · have : Nat.log 2 M = 0 := by rw [h0]; simp
      rw [this]; simp [Real.log_nonneg hy1]
    · have h1 : 2 ^ Nat.log 2 M ≤ M := Nat.pow_log_le_self 2 h0.ne'
      have h2 : ((2 ^ Nat.log 2 M : ℕ) : ℝ) ≤ y :=
        (Nat.cast_le.mpr h1).trans (Nat.floor_le hy0.le)
      have h3 := Real.log_le_log (by positivity) h2
      rw [Nat.cast_pow, Real.log_pow] at h3
      simpa using h3
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq
  -- `corr ≤ y u³ / log 2 ≤ y e^u ≤ y² e^{-c₁ u}`
  have hcorr2 : corr ≤ y * (u ^ 3 / Real.log 2) := by
    have hJ' : (Nat.log 2 M : ℝ) ≤ u ^ 2 / Real.log 2 := by
      rw [le_div_iff₀ hl2, ← hlog]; exact hlogJ
    calc corr ≤ y * ((Nat.log 2 M : ℝ) * Real.log q) := hcorr1
      _ ≤ y * ((u ^ 2 / Real.log 2) * u) := by
          refine mul_le_mul_of_nonneg_left ?_ hy0.le
          exact mul_le_mul hJ' hqy hlq0 (by positivity)
      _ = _ := by ring
  have hpoly := hu₀ u hu0u
  have hu3 : u ^ 3 / Real.log 2 ≤ Real.exp u := by
    have : 1 / Real.log 2 * u ^ 3 ≤ Real.exp (1 * u) := hpoly
    rw [one_mul] at this
    calc u ^ 3 / Real.log 2 = 1 / Real.log 2 * u ^ 3 := by ring
      _ ≤ _ := this
  have hexp : y * Real.exp u ≤ y ^ 2 * Real.exp (-(c₁ * u)) := by
    have hyexp : y = Real.exp (u ^ 2) := by rw [← hlog, Real.exp_log hy0]
    have h1 : Real.exp u * Real.exp (c₁ * u) ≤ y := by
      rw [← Real.exp_add, hyexp]
      refine Real.exp_le_exp.mpr ?_
      have hu0' : 0 ≤ u := zero_le_two.trans hu2
      have h3 : c₁ * u ≤ u := (mul_le_mul_of_nonneg_right hc₁1 hu0').trans_eq (one_mul u)
      calc u + c₁ * u ≤ u + u := add_le_add_right h3 u
        _ = 2 * u := (two_mul u).symm
        _ ≤ u * u := mul_le_mul_of_nonneg_right hu2 hu0'
        _ = u ^ 2 := (sq u).symm
    have h2 : Real.exp (c₁ * u) * Real.exp (-(c₁ * u)) = 1 := by
      rw [← Real.exp_add]; simp
    calc y * Real.exp u = y * (Real.exp u * 1) := by ring
      _ = y * (Real.exp u * (Real.exp (c₁ * u) * Real.exp (-(c₁ * u)))) := by rw [h2]
      _ = y * (Real.exp u * Real.exp (c₁ * u)) * Real.exp (-(c₁ * u)) := by ring
      _ ≤ y * y * Real.exp (-(c₁ * u)) := by
          gcongr
      _ = _ := by ring
  have hcorr3 : corr ≤ y ^ 2 * Real.exp (-(c₁ * u)) :=
    hcorr2.trans ((mul_le_mul_of_nonneg_left hu3 hy0.le).trans hexp)
  have hz' := hz y hyy₁
  have hz'' : |RΛ - (y - 1) ^ 2 / 2| ≤ y ^ 2 * Real.exp (-(c₁ * u)) := by
    refine hz'.trans ?_
    have : Real.exp (-(c * u)) ≤ Real.exp (-(c₁ * u)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (mul_le_mul_of_nonneg_right hc₁c (Real.sqrt_nonneg _))
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hcast : ((RΛ - corr : ℝ) : ℂ) - (((y - 1) ^ 2 / 2 : ℝ) : ℂ) =
      ((RΛ - (y - 1) ^ 2 / 2 - corr : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  calc |RΛ - (y - 1) ^ 2 / 2 - corr| ≤ |RΛ - (y - 1) ^ 2 / 2| + |corr| := abs_sub _ _
    _ ≤ y ^ 2 * Real.exp (-(c₁ * u)) + y ^ 2 * Real.exp (-(c₁ * u)) := by
        rw [abs_of_nonneg hcorr0]
        exact add_le_add hz'' hcorr3
    _ = _ := by ring

end PrimeCarleson.Proof.Fplus31.PNTSW

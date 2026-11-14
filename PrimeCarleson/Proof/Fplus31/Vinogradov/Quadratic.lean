module

public import PrimeCarleson.Proof.Fplus31.Vinogradov.Differencing

/-!
# The quadratic Vinogradov lemma

Vinogradov-type estimate used by the extrapolation step of the iteration of `C2/CMain.lean` (proof
of [F+] Proposition 3.1), degree two (Leng's `l:vinogradov` = [GT14, Lemma 2.3],
arXiv:2312.10772v5 TeX L1471, with a lower bound on the length and an upper
bound on `ε`).

The proof is Weyl differencing with the linear lemma (`Linear.lean`) applied twice:

1. `quadratic_leading`: for `h` in a dense set of shifts, `P(ℓ + h) - P(ℓ) = 2 a₂ h ℓ + (a₂ h² +
   a₁ h)` is small on the dense set `Λ ∩ (Λ - h)`, so the linear lemma gives `q_h` with
   `‖q_h · 2 a₂ h‖` small; the pigeonhole `q_h = q*` on a dense set of `h`, followed by the linear
   lemma in `h`, gives `Q` with `‖Q a₂‖ ≤ C ε D^{10} / M²`;
2. `quadratic_vinogradov`: `Q P(ℓ) - (Q a₂) ℓ²` is linear in `ℓ` and still small, and the linear
   lemma with constant term finishes.

Everything is a polynomial in `D = κ⁻¹ ≥ 1`, with `κ M ≤ |Λ|` the density of `Λ` in a real interval
`[a, a + M]`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- The leading coefficient of a quadratic polynomial that is small on a dense set of integers. -/
theorem quadratic_leading {D ε a M a₂ a₁ a₀ : ℝ} (hD : 1 ≤ D) (hε0 : 0 ≤ ε)
    (hε : 10 ^ 12 * ε * D ^ 12 ≤ 1) (hM : 10 ^ 6 * D ^ 6 ≤ M) (ha0 : 0 ≤ a)
    (K : Finset ℤ) (hK : ∀ k ∈ K, a ≤ (k : ℝ) ∧ (k : ℝ) ≤ a + M) (hcard : M / D ≤ K.card)
    (h : ∀ k ∈ K, ‖((a₂ * (k : ℝ) ^ 2 + a₁ * k + a₀ : ℝ) : UnitAddCircle)‖ ≤ ε) :
    ∃ Q : ℕ, 0 < Q ∧ (Q : ℝ) ≤ 36000 * D ^ 5 ∧
      ‖((Q * a₂ : ℝ) : UnitAddCircle)‖ ≤ 10 ^ 9 * ε * D ^ 10 / M ^ 2 := by
  have hD0 : 0 < D := by linarith
  have hD6 : 1 ≤ D ^ 6 := one_le_pow₀ hD
  have hM1 : 1 ≤ M := by linarith only [hM, hD6]
  have hM0 : 0 < M := by linarith
  have hDM : M / D > 0 := by positivity
  have hKne : K.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < K.card := lt_of_lt_of_le hDM hcard
    exact_mod_cast this
  -- the set of possible shifts
  set Dset : Finset ℤ := Finset.Icc ⌈-M⌉ ⌊M⌋ with hDset
  have hDdiff : ∀ ℓ ∈ K, ∀ ℓ' ∈ K, ℓ' - ℓ ∈ Dset := by
    intro ℓ hℓ ℓ' hℓ'
    obtain ⟨h1, h2⟩ := hK ℓ hℓ
    obtain ⟨h3, h4⟩ := hK ℓ' hℓ'
    rw [hDset, Finset.mem_Icc]
    constructor
    · apply Int.ceil_le.mpr
      push_cast
      linarith
    · apply Int.le_floor.mpr
      push_cast
      linarith
  have hDcard : (Dset.card : ℝ) ≤ 3 * M := by
    have := card_Icc_int_le (-M) M (by linarith)
    linarith
  obtain ⟨H, hHD, hHcard, hH⟩ := exists_dense_shifts K Dset hDdiff hKne
  have hDsetpos : (0 : ℝ) < Dset.card := by
    obtain ⟨ℓ₀, hℓ₀⟩ := hKne
    have : (0 : ℤ) ∈ Dset := by simpa using hDdiff ℓ₀ hℓ₀ ℓ₀ hℓ₀
    exact_mod_cast Finset.card_pos.mpr ⟨0, this⟩
  -- powers of `D` against `ε` and `M`
  have hεj : ∀ j : ℕ, j ≤ 12 → ε * D ^ j ≤ 1 / 10 ^ 12 := by
    intro j hj
    have h1 : D ^ j ≤ D ^ 12 := pow_le_pow_right₀ hD hj
    have h2 : ε * D ^ j ≤ ε * D ^ 12 := mul_le_mul_of_nonneg_left h1 hε0
    have h3 : ε * D ^ 12 ≤ 1 / 10 ^ 12 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    linarith
  have hMj : ∀ j : ℕ, j ≤ 6 → 10 ^ 6 * D ^ j ≤ M := by
    intro j hj
    have h1 : D ^ j ≤ D ^ 6 := pow_le_pow_right₀ hD hj
    linarith only [h1, hM]
  -- the shifted linear problems
  have hden : ∀ t ∈ H, M / (6 * D ^ 2) ≤ ((K.filter (fun ℓ => ℓ + t ∈ K)).card : ℝ) := by
    intro t ht
    refine le_trans ?_ (hH t ht)
    calc M / (6 * D ^ 2) = (M / D) ^ 2 / (6 * M) := by field_simp
      _ ≤ (K.card : ℝ) ^ 2 / (2 * Dset.card) := by
          apply div_le_div₀ (by positivity) (pow_le_pow_left₀ hDM.le hcard 2)
            (by positivity) (by linarith)
  have hq : ∀ t ∈ H, ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ 30 * D ^ 2 ∧
      ‖(((q : ℝ) * (2 * a₂ * (t : ℝ)) : ℝ) : UnitAddCircle)‖ ≤ 2880 * ε * D ^ 4 / M := by
    intro t ht
    have hmem : ∀ k ∈ K.filter (fun ℓ => ℓ + t ∈ K), k ∈ K ∧ k + t ∈ K := fun k hk =>
      Finset.mem_filter.mp hk
    have h1 := hεj 2 (by norm_num)
    have h2 := hMj 4 (by norm_num)
    obtain ⟨q, hq0, hq5, hα, -⟩ := linear_vinogradov_inv (D := 6 * D ^ 2) (ε := 2 * ε) (a := a)
      (M := M) (R := a + M) (α := 2 * a₂ * (t : ℝ)) (β := a₂ * (t : ℝ) ^ 2 + a₁ * t)
      (by linarith only [one_le_pow₀ (n := 2) hD]) (by positivity) (by linarith only [h1])
      (by linarith only [h2, pow_nonneg hD0.le 4])
      (K.filter (fun ℓ => ℓ + t ∈ K)) (fun k hk => hK k (hmem k hk).1) (hden t ht)
      (fun k hk => by
        have := (hK k (hmem k hk).1).1
        rw [abs_of_nonneg (by linarith)]
        linarith [(hK k (hmem k hk).1).2])
      (fun k hk => by
        obtain ⟨hk1, hk2⟩ := hmem k hk
        have e : (2 * a₂ * (t : ℝ)) * (k : ℝ) + (a₂ * (t : ℝ) ^ 2 + a₁ * t)
            = (a₂ * ((k + t : ℤ) : ℝ) ^ 2 + a₁ * ((k + t : ℤ) : ℝ) + a₀)
              - (a₂ * (k : ℝ) ^ 2 + a₁ * k + a₀) := by
          push_cast
          ring
        rw [e]
        refine (norm_coe_sub_le _ _).trans ?_
        linarith [h _ hk1, h _ hk2])
    refine ⟨q, hq0, by linarith, ?_⟩
    have e : 40 * (2 * ε) * (6 * D ^ 2) ^ 2 / M = 2880 * ε * D ^ 4 / M := by ring
    rw [e] at hα
    exact hα
  choose! qf hqf using hq
  -- pigeonhole on the value of `q_h`
  set N : ℕ := ⌊30 * D ^ 2⌋₊ with hN
  have hN30 : (N : ℝ) ≤ 30 * D ^ 2 := Nat.floor_le (by positivity)
  have hN1 : 1 ≤ N := by
    apply Nat.le_floor
    have : (1 : ℝ) ≤ D ^ 2 := one_le_pow₀ hD
    push_cast
    linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hmaps : ∀ t ∈ H, qf t ∈ Finset.Icc 1 N := by
    intro t ht
    obtain ⟨h1, h2, -⟩ := hqf t ht
    rw [Finset.mem_Icc]
    exact ⟨h1, Nat.le_floor h2⟩
  obtain ⟨qs, hqs, hqs'⟩ := exists_fiber_ge H (Finset.Icc 1 N) qf hmaps
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN1⟩⟩
  set Hs := H.filter (fun t => qf t = qs) with hHs
  have hqsN : (qs : ℝ) ≤ 30 * D ^ 2 := by
    have : qs ≤ N := (Finset.mem_Icc.mp hqs).2
    exact (by exact_mod_cast this : (qs : ℝ) ≤ N).trans hN30
  have hqs1 : 0 < qs := (Finset.mem_Icc.mp hqs).1
  have hHscard : 2 * M / (120 * D ^ 3) ≤ Hs.card := by
    have h1 : ((Finset.Icc 1 N).card : ℝ) = N := by simp
    rw [h1] at hqs'
    refine le_trans ?_ hqs'
    have h2 : M / D / 2 ≤ (H.card : ℝ) := by
      have : M / D / 2 ≤ (K.card : ℝ) / 2 := by linarith
      linarith
    calc 2 * M / (120 * D ^ 3) = (M / D / 2) / (30 * D ^ 2) := by field_simp; ring
      _ ≤ (H.card : ℝ) / (30 * D ^ 2) := div_le_div_of_nonneg_right h2 (by positivity)
      _ ≤ (H.card : ℝ) / N := div_le_div_of_nonneg_left (by positivity) hNpos hN30
  -- the second application of the linear lemma, in the shift variable
  have hHsb : ∀ t ∈ Hs, -M ≤ (t : ℝ) ∧ (t : ℝ) ≤ M := by
    intro t ht
    have h1 := hHD (Finset.mem_filter.mp ht).1
    rw [hDset, Finset.mem_Icc] at h1
    have h2 : -M ≤ (⌈-M⌉ : ℝ) := Int.le_ceil _
    have h3 : (⌊M⌋ : ℝ) ≤ M := Int.floor_le _
    have h4 : ((⌈-M⌉ : ℤ) : ℝ) ≤ t := by exact_mod_cast h1.1
    have h5 : (t : ℝ) ≤ ((⌊M⌋ : ℤ) : ℝ) := by exact_mod_cast h1.2
    constructor <;> linarith
  have h7 := hεj 7 (by norm_num)
  have h6 := hMj 6 le_rfl
  obtain ⟨q₂, hq₂0, hq₂5, hα₂, -⟩ := linear_vinogradov_inv (D := 120 * D ^ 3)
    (ε := 2880 * ε * D ^ 4 / M) (a := -M) (M := 2 * M) (R := M) (α := (qs : ℝ) * (2 * a₂))
    (β := 0) (by linarith only [one_le_pow₀ (n := 3) hD])
    (by positivity)
    (by
      have e : 16 * (2880 * ε * D ^ 4 / M) * (120 * D ^ 3) = 5529600 * (ε * D ^ 7) / M := by
        ring
      rw [e, div_le_one hM0]
      linarith)
    (by linarith only [h6, hD6]) Hs (fun t ht => by have := hHsb t ht; constructor <;> linarith)
    (by simpa using hHscard)
    (fun t ht => by
      have := hHsb t ht
      rw [abs_le]
      constructor <;> linarith)
    (fun t ht => by
      obtain ⟨ht1, ht2⟩ := Finset.mem_filter.mp ht
      obtain ⟨-, -, h3⟩ := hqf t ht1
      rw [ht2] at h3
      have e : (qs : ℝ) * (2 * a₂) * (t : ℝ) + 0 = (qs : ℝ) * (2 * a₂ * (t : ℝ)) := by ring
      rw [e]
      exact h3)
  refine ⟨2 * qs * q₂, by positivity, ?_, ?_⟩
  · push_cast
    have h1 : (qs : ℝ) * q₂ ≤ (30 * D ^ 2) * (600 * D ^ 3) := by
      apply mul_le_mul hqsN (by linarith) (by positivity) (by positivity)
    have h56 : D ^ 5 ≤ D ^ 6 := pow_le_pow_right₀ hD (by norm_num)
    linarith only [h1, h56, hD6]
  · have e : ((2 * qs * q₂ : ℕ) : ℝ) * a₂ = (q₂ : ℝ) * ((qs : ℝ) * (2 * a₂)) := by
      push_cast
      ring
    rw [e]
    refine hα₂.trans ?_
    have e2 : 40 * (2880 * ε * D ^ 4 / M) * (120 * D ^ 3) ^ 2 / (2 * M)
        = 829440000 * (ε * D ^ 10 / M ^ 2) := by
      field_simp
      ring
    rw [e2]
    have : 0 ≤ ε * D ^ 10 / M ^ 2 := by positivity
    calc 829440000 * (ε * D ^ 10 / M ^ 2) ≤ 10 ^ 9 * (ε * D ^ 10 / M ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ this
          norm_num
      _ = _ := by ring

/-- **Quadratic Vinogradov lemma** (Leng's `l:vinogradov`, [GT14, Lemma 2.3], degree two, one
variable, with a lower bound on the length and an upper bound on `ε`). Let `K` be a set of integers
in a real interval `[a, a + M]` with `0 ≤ a ≤ M` and `M / D ≤ |K|`, where `D ≥ 1`, `M ≥ 10⁶ D⁶` and
`10¹² ε D¹² ≤ 1`. If `‖a₂ k² + a₁ k + a₀‖_{ℝ/ℤ} ≤ ε` for all `k ∈ K`, then there is an integer
`0 < q ≤ 2·10⁵ D⁶` with `‖q a₂‖ ≤ 10¹² ε D¹² / M²`, `‖q a₁‖ ≤ 10¹² ε D¹² / M` and
`‖q a₀‖ ≤ 10¹² ε D¹²`. -/
theorem quadratic_vinogradov {D ε a M a₂ a₁ a₀ : ℝ} (hD : 1 ≤ D) (hε0 : 0 ≤ ε)
    (hε : 10 ^ 12 * ε * D ^ 12 ≤ 1) (hM : 10 ^ 6 * D ^ 6 ≤ M) (ha0 : 0 ≤ a) (haM : a ≤ M)
    (K : Finset ℤ) (hK : ∀ k ∈ K, a ≤ (k : ℝ) ∧ (k : ℝ) ≤ a + M) (hcard : M / D ≤ K.card)
    (h : ∀ k ∈ K, ‖((a₂ * (k : ℝ) ^ 2 + a₁ * k + a₀ : ℝ) : UnitAddCircle)‖ ≤ ε) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ 2 * 10 ^ 5 * D ^ 6 ∧
      ‖((q * a₂ : ℝ) : UnitAddCircle)‖ ≤ 10 ^ 12 * ε * D ^ 12 / M ^ 2 ∧
      ‖((q * a₁ : ℝ) : UnitAddCircle)‖ ≤ 10 ^ 12 * ε * D ^ 12 / M ∧
      ‖((q * a₀ : ℝ) : UnitAddCircle)‖ ≤ 10 ^ 12 * ε * D ^ 12 := by
  have hD0 : 0 < D := by linarith
  have hD6 : 1 ≤ D ^ 6 := one_le_pow₀ hD
  have hM1 : 1 ≤ M := by linarith only [hM, hD6]
  have hM0 : 0 < M := by linarith
  obtain ⟨Q, hQ0, hQ, hQa⟩ := quadratic_leading hD hε0 hε hM ha0 K hK hcard h
  have hQ0' : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hεj : ∀ j : ℕ, j ≤ 12 → ε * D ^ j ≤ 1 / 10 ^ 12 := by
    intro j hj
    have h1 : D ^ j ≤ D ^ 12 := pow_le_pow_right₀ hD hj
    have h2 : ε * D ^ j ≤ ε * D ^ 12 := mul_le_mul_of_nonneg_left h1 hε0
    have h3 : ε * D ^ 12 ≤ 1 / 10 ^ 12 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    linarith
  have hD5 : D ^ 5 ≤ D ^ 10 := pow_le_pow_right₀ hD (by norm_num)
  -- the remaining linear problem
  have hlin : ∀ k ∈ K, ‖(((Q * a₁ : ℝ) * (k : ℝ) + Q * a₀ : ℝ) : UnitAddCircle)‖
      ≤ 5 * 10 ^ 9 * ε * D ^ 10 := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := hK k hk
    have e : (Q * a₁ : ℝ) * (k : ℝ) + Q * a₀
        = ((Q : ℤ) : ℝ) * (a₂ * (k : ℝ) ^ 2 + a₁ * k + a₀) - ((k ^ 2 : ℤ) : ℝ) * (Q * a₂) := by
      push_cast
      ring
    rw [e]
    refine (norm_coe_sub_le _ _).trans ?_
    have h1 : ‖((((Q : ℤ) : ℝ) * (a₂ * (k : ℝ) ^ 2 + a₁ * k + a₀) : ℝ) : UnitAddCircle)‖
        ≤ 36000 * D ^ 5 * ε := by
      refine (norm_intCast_mul_coe_le (Q : ℤ) _).trans ?_
      simp only [Int.cast_natCast, abs_of_nonneg hQ0']
      calc (Q : ℝ) * ‖((a₂ * (k : ℝ) ^ 2 + a₁ * k + a₀ : ℝ) : UnitAddCircle)‖
          ≤ (36000 * D ^ 5) * ε :=
            mul_le_mul hQ (h k hk) (norm_nonneg _) (by positivity)
        _ = _ := rfl
    have h2 : ‖((((k ^ 2 : ℤ) : ℝ) * (Q * a₂) : ℝ) : UnitAddCircle)‖
        ≤ 4 * 10 ^ 9 * ε * D ^ 10 := by
      refine (norm_intCast_mul_coe_le (k ^ 2) _).trans ?_
      have hk0 : 0 ≤ (k : ℝ) := by linarith
      have hk2M : (k : ℝ) ≤ 2 * M := by linarith
      have hsq : |((k ^ 2 : ℤ) : ℝ)| ≤ 4 * M ^ 2 := by
        rw [abs_of_nonneg (by positivity)]
        push_cast
        linarith only [pow_le_pow_left₀ hk0 hk2M 2]
      calc |((k ^ 2 : ℤ) : ℝ)| * ‖((Q * a₂ : ℝ) : UnitAddCircle)‖
          ≤ (4 * M ^ 2) * (10 ^ 9 * ε * D ^ 10 / M ^ 2) :=
            mul_le_mul hsq hQa (norm_nonneg _) (by positivity)
        _ = 4 * 10 ^ 9 * ε * D ^ 10 := by field_simp
    have h3 : 36000 * D ^ 5 * ε ≤ 10 ^ 9 * ε * D ^ 10 := by
      have : 36000 * D ^ 5 ≤ 10 ^ 9 * D ^ 10 := by linarith only [hD5, pow_pos hD0 5]
      linarith only [mul_le_mul_of_nonneg_right this hε0]
    linarith
  have h11 := hεj 11 (by norm_num)
  have h6 : 10 ^ 6 * D ^ 2 ≤ M := by
    have : D ^ 2 ≤ D ^ 6 := pow_le_pow_right₀ hD (by norm_num)
    linarith only [this, hM]
  obtain ⟨q₁, hq₁0, hq₁5, hα₁, hβ₁⟩ := linear_vinogradov_inv (D := D) (ε := 5 * 10 ^ 9 * ε * D ^ 10)
    (a := a) (M := M) (R := 2 * M) (α := Q * a₁) (β := Q * a₀) hD (by positivity)
    (by linarith only [h11]) (by linarith only [h6, pow_pos hD0 2]) K hK hcard
    (fun k hk => by
      obtain ⟨hk1, hk2⟩ := hK k hk
      rw [abs_of_nonneg (by linarith)]
      linarith)
    hlin
  refine ⟨q₁ * Q, by positivity, ?_, ?_, ?_, ?_⟩
  · push_cast
    have : (q₁ : ℝ) * Q ≤ (5 * D) * (36000 * D ^ 5) :=
      mul_le_mul hq₁5 hQ hQ0' (by positivity)
    linarith only [this, hD6]
  · have e : ((q₁ * Q : ℕ) : ℝ) * a₂ = ((q₁ : ℤ) : ℝ) * (Q * a₂) := by
      push_cast
      ring
    rw [e]
    refine (norm_intCast_mul_coe_le (q₁ : ℤ) _).trans ?_
    have hq₁0' : (0 : ℝ) ≤ q₁ := Nat.cast_nonneg q₁
    simp only [Int.cast_natCast, abs_of_nonneg hq₁0']
    calc (q₁ : ℝ) * ‖((Q * a₂ : ℝ) : UnitAddCircle)‖
        ≤ (5 * D) * (10 ^ 9 * ε * D ^ 10 / M ^ 2) :=
          mul_le_mul hq₁5 hQa (norm_nonneg _) (by positivity)
      _ = (5 * 10 ^ 9 * ε * D ^ 11) / M ^ 2 := by ring
      _ ≤ 10 ^ 12 * ε * D ^ 12 / M ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          have : D ^ 11 ≤ D ^ 12 := pow_le_pow_right₀ hD (by norm_num)
          linarith only [mul_le_mul_of_nonneg_left this hε0,
            mul_nonneg hε0 (pow_nonneg hD0.le 11)]
  · have e : ((q₁ * Q : ℕ) : ℝ) * a₁ = (q₁ : ℝ) * (Q * a₁) := by
      push_cast
      ring
    rw [e]
    refine hα₁.trans ?_
    calc 40 * (5 * 10 ^ 9 * ε * D ^ 10) * D ^ 2 / M
        = (2 * 10 ^ 11 * ε * D ^ 12) / M := by ring
      _ ≤ 10 ^ 12 * ε * D ^ 12 / M := by
          apply div_le_div_of_nonneg_right _ hM0.le
          linarith only [mul_nonneg hε0 (pow_nonneg hD0.le 12)]
  · have e : ((q₁ * Q : ℕ) : ℝ) * a₀ = (q₁ : ℝ) * (Q * a₀) := by
      push_cast
      ring
    rw [e]
    refine hβ₁.trans ?_
    have e2 : 5 * D * (5 * 10 ^ 9 * ε * D ^ 10)
        + 2 * M * (40 * (5 * 10 ^ 9 * ε * D ^ 10) * D ^ 2 / M)
        = 25 * 10 ^ 9 * ε * D ^ 11 + 4 * 10 ^ 11 * ε * D ^ 12 := by
      field_simp
      ring
    rw [e2]
    have : D ^ 11 ≤ D ^ 12 := pow_le_pow_right₀ hD (by norm_num)
    linarith only [mul_le_mul_of_nonneg_left this hε0,
      mul_nonneg hε0 (pow_nonneg hD0.le 11)]

end PrimeCarleson.Proof.Fplus31

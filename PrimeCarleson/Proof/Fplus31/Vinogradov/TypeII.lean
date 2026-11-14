module

public import PrimeCarleson.Proof.Fplus31.Vinogradov.TwoVariable
public import PrimeCarleson.Proof.Fplus31.Vinogradov.OneVariable

/-!
# The many-dilates Vinogradov lemma for pairs (type II), degree at most two

Vinogradov-type estimate used by the extrapolation step of the iteration of `C2/CMain.lean` (proof
of [F+] Proposition 3.1). For the type II step the dilation parameters are pairs `(ℓ, ℓ')` in a
dense subset `Γ ⊆ (L/2, L]²` and the relevant polynomial is
`P(x, y) = c₀₀ + c₁₀ x + c₀₁ y + c₂₀ x² + c₁₁ x y + c₀₂ y²` (a polynomial `u(x) + v(y)`, the
separate-variable form of the character computation, is the case `c₁₁ = 0`).

* `vinogradov_two_var_explicit`: explicit constants;
* `vinogradov_two_var`: one absolute `C`, in the form of the one-variable
  `vinogradov_poly_deg_le_two`: if `‖P(ℓ, ℓ')‖_{ℝ/ℤ} ≤ ε` on `Γ`, `δ L² ≤ |Γ|`, `L ≥ C δ^{-C}`,
  `ε ≤ δ^C / C`, then a single `q ≤ C δ^{-C}` has `‖q c_{ij}‖ ≤ C δ^{-C} ε / L^{i+j}` for all
  six coefficients;
* `vinogradov_two_var_separate`: the corollary for `P(ℓ, ℓ') = u(ℓ) + v(ℓ')`, `u, v` real
  polynomials of degree at most `2`, constant term `u₀ + v₀`.

The proof is the pigeonhole on `Q_{ℓ'}`: `two_variable_rows` (the quadratic lemma in each dense row,
then `Q_{ℓ'} = Q_*` on a dense set of rows) and `two_variable_columns` (the linear lemma for
`c₁₁, c₁₀` and the quadratic lemma for `c₀₂, c₀₁, c₀₀` on that set of rows).
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- **Many-dilates Vinogradov lemma for pairs, explicit constants.**  Let
`P(x, y) = c₀₀ + c₁₀ x + c₀₁ y + c₂₀ x² + c₁₁ x y + c₀₂ y²`, `L` a natural number with
`δ⁴² L ≥ 2·10³⁸`, and `Γ ⊆ (L/2, L]²` a set of pairs of integers with `|Γ| ≥ δ L²`.  If
`‖P(x, y)‖_{ℝ/ℤ} ≤ ε` on `Γ`, where `10⁸⁸ ε ≤ δ⁹⁶`, there is a positive integer
`q ≤ 10⁴⁹ δ⁻⁵⁵` with `‖q c_{ij}‖ ≤ 10⁹⁵ ε δ⁻¹⁰³ / L^{i+j}`. -/
theorem vinogradov_two_var_explicit {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 10 ^ 88 * ε ≤ δ ^ 96) (c₀₀ c₁₀ c₀₁ c₂₀ c₁₁ c₀₂ : ℝ) (L : ℕ)
    (hL : 2 * 10 ^ 38 ≤ δ ^ 42 * L) (Γ : Finset (ℕ × ℕ))
    (hΓ : ∀ p ∈ Γ, (L : ℝ) / 2 < p.1 ∧ (p.1 : ℝ) ≤ L ∧ (L : ℝ) / 2 < p.2 ∧ (p.2 : ℝ) ≤ L)
    (hcard : δ * (L : ℝ) ^ 2 ≤ Γ.card)
    (h : ∀ p ∈ Γ, ‖((c₀₀ + c₁₀ * (p.1 : ℝ) + c₀₁ * (p.2 : ℝ) + c₂₀ * (p.1 : ℝ) ^ 2
        + c₁₁ * (p.1 : ℝ) * (p.2 : ℝ) + c₀₂ * (p.2 : ℝ) ^ 2 : ℝ) : UnitAddCircle)‖ ≤ ε) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ 10 ^ 49 / δ ^ 55 ∧
      ‖(((q : ℝ) * c₂₀ : ℝ) : UnitAddCircle)‖ ≤ 10 ^ 95 * ε / (δ ^ 103 * (L : ℝ) ^ 2) ∧
      ‖(((q : ℝ) * c₁₁ : ℝ) : UnitAddCircle)‖ ≤ 10 ^ 95 * ε / (δ ^ 103 * (L : ℝ) ^ 2) ∧
      ‖(((q : ℝ) * c₀₂ : ℝ) : UnitAddCircle)‖ ≤ 10 ^ 95 * ε / (δ ^ 103 * (L : ℝ) ^ 2) ∧
      ‖(((q : ℝ) * c₁₀ : ℝ) : UnitAddCircle)‖ ≤ 10 ^ 95 * ε / (δ ^ 103 * (L : ℝ)) ∧
      ‖(((q : ℝ) * c₀₁ : ℝ) : UnitAddCircle)‖ ≤ 10 ^ 95 * ε / (δ ^ 103 * (L : ℝ)) ∧
      ‖(((q : ℝ) * c₀₀ : ℝ) : UnitAddCircle)‖ ≤ 10 ^ 95 * ε / δ ^ 103 := by
  have hu : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  set u : ℝ := δ⁻¹ with hu_def
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
  have hδ42 : δ ^ 42 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hδ42pos : 0 < δ ^ 42 := by positivity
  have hL0 : (0 : ℝ) < L := by
    by_contra hcon
    have : (L : ℝ) = 0 := le_antisymm (not_lt.mp hcon) (Nat.cast_nonneg L)
    rw [this] at hL
    norm_num at hL
  have hLbig : 2 * 10 ^ 38 ≤ (L : ℝ) := hL.trans (mul_le_of_le_one_left hL0.le hδ42)
  have hΓne : Γ.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < Γ.card := lt_of_lt_of_le (by positivity) hcard
    exact_mod_cast this
  have hε0 : 0 ≤ ε := by
    obtain ⟨p, hp⟩ := hΓne
    exact (norm_nonneg _).trans (h p hp)
  set M : ℝ := (L : ℝ) / 2 with hM
  have hM1 : 1 ≤ M := by rw [hM]; linarith
  -- the hypotheses of the two stages
  have hεu : 10 ^ 88 * ε * u ^ 96 ≤ 1 := by
    have e : 10 ^ 88 * ε * u ^ 96 = 10 ^ 88 * ε / δ ^ 96 := by
      rw [hu_def, inv_pow]; ring
    rw [e, div_le_one (by positivity)]
    exact hε
  have hεu' : ∀ j : ℕ, j ≤ 96 → ε * u ^ j ≤ 1 / 10 ^ 88 := by
    intro j hj
    have h1 : u ^ j ≤ u ^ 96 := pow_le_pow_right₀ hu hj
    have h2 : ε * u ^ j ≤ ε * u ^ 96 := mul_le_mul_of_nonneg_left h1 hε0
    have h3 : ε * u ^ 96 ≤ 1 / 10 ^ 88 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    linarith
  have hε1 : 10 ^ 12 * ε * u ^ 12 ≤ 1 := by
    have := hεu' 12 (by norm_num)
    have h2 : (10 : ℝ) ^ 12 * (ε * u ^ 12) ≤ 10 ^ 12 * (1 / 10 ^ 88) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    have h3 : (10 : ℝ) ^ 12 * (1 / 10 ^ 88) ≤ 1 := by norm_num
    exact (mul_assoc _ _ _).trans_le (h2.trans h3)
  have hMu : 10 ^ 38 * u ^ 42 ≤ M := by
    have e : 10 ^ 38 * u ^ 42 = 10 ^ 38 / δ ^ 42 := by
      rw [hu_def, inv_pow]; ring
    rw [e, div_le_iff₀ hδ42pos, hM]
    linarith
  have hu6 : 10 ^ 6 * u ^ 6 ≤ M := by
    have : u ^ 6 ≤ u ^ 42 := pow_le_pow_right₀ hu (by norm_num)
    calc 10 ^ 6 * u ^ 6 ≤ 10 ^ 6 * u ^ 42 := mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ 10 ^ 38 * u ^ 42 := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ M := hMu
  have hD₂ : 1 ≤ 2 * 10 ^ 5 * u ^ 7 :=
    (one_le_pow₀ (n := 7) hu).trans (le_mul_of_one_le_left (by positivity) (by norm_num))
  have hη0 : 0 ≤ 10 ^ 12 * ε * u ^ 12 := by positivity
  have hη : 10 ^ 12 * (10 ^ 12 * ε * u ^ 12) * (2 * 10 ^ 5 * u ^ 7) ^ 12 ≤ 1 := by
    have e : 10 ^ 12 * (10 ^ 12 * ε * u ^ 12) * (2 * 10 ^ 5 * u ^ 7) ^ 12
        = (10 ^ 24 * (2 * 10 ^ 5) ^ 12) * (ε * u ^ 96) := by ring
    rw [e]
    have h1 := hεu' 96 le_rfl
    have h2 : (10 : ℝ) ^ 24 * (2 * 10 ^ 5) ^ 12 * (ε * u ^ 96)
        ≤ 10 ^ 24 * (2 * 10 ^ 5) ^ 12 * (1 / 10 ^ 88) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (10 : ℝ) ^ 24 * (2 * 10 ^ 5) ^ 12 * (1 / 10 ^ 88) ≤ 1 := by norm_num
    linarith
  have hMD₂ : 10 ^ 6 * (2 * 10 ^ 5 * u ^ 7) ^ 6 ≤ M := by
    have e : 10 ^ 6 * (2 * 10 ^ 5 * u ^ 7) ^ 6 = (10 ^ 6 * (2 * 10 ^ 5) ^ 6) * u ^ 42 := by ring
    rw [e]
    have h3 : (10 : ℝ) ^ 6 * (2 * 10 ^ 5) ^ 6 ≤ 10 ^ 38 := by norm_num
    have h4 : (10 ^ 6 * (2 * 10 ^ 5) ^ 6 : ℝ) * u ^ 42 ≤ 10 ^ 38 * u ^ 42 :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    linarith
  -- the set of pairs, as integer pairs
  set Γ' : Finset (ℤ × ℤ) := Γ.image (fun p : ℕ × ℕ => ((p.1 : ℤ), (p.2 : ℤ))) with hΓ'
  have hΓ'card : Γ'.card = Γ.card := by
    apply Finset.card_image_of_injective
    intro p q hpq
    simp only [Prod.mk.injEq, Nat.cast_inj] at hpq
    exact Prod.ext hpq.1 hpq.2
  have hΓ'mem : ∀ z ∈ Γ', ∃ p ∈ Γ, (p.1 : ℤ) = z.1 ∧ (p.2 : ℤ) = z.2 := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨p, hp, rfl, rfl⟩
  have hΓ'bd : ∀ z ∈ Γ', M ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ M + M ∧ M ≤ (z.2 : ℝ) ∧
      (z.2 : ℝ) ≤ M + M := by
    intro z hz
    obtain ⟨p, hp, h1, h2⟩ := hΓ'mem z hz
    obtain ⟨a1, a2, a3, a4⟩ := hΓ p hp
    have e1 : (z.1 : ℝ) = (p.1 : ℝ) := by rw [← h1]; simp
    have e2 : (z.2 : ℝ) = (p.2 : ℝ) := by rw [← h2]; simp
    rw [e1, e2, hM]
    exact ⟨a1.le, a2.trans_eq (add_halves _).symm, a3.le, a4.trans_eq (add_halves _).symm⟩
  have hΓ'poly : ∀ z ∈ Γ', ‖((c₀₀ + c₁₀ * (z.1 : ℝ) + c₀₁ * (z.2 : ℝ) + c₂₀ * (z.1 : ℝ) ^ 2
        + c₁₁ * (z.1 : ℝ) * (z.2 : ℝ) + c₀₂ * (z.2 : ℝ) ^ 2 : ℝ) : UnitAddCircle)‖ ≤ ε := by
    intro z hz
    obtain ⟨p, hp, h1, h2⟩ := hΓ'mem z hz
    have e1 : (z.1 : ℝ) = (p.1 : ℝ) := by rw [← h1]; simp
    have e2 : (z.2 : ℝ) = (p.2 : ℝ) := by rw [← h2]; simp
    rw [e1, e2]
    exact h p hp
  -- stage 0: dense rows
  obtain ⟨R, hR, hRcard, hrows⟩ := exists_dense_rows (D := u) (a := M) (M := M) hu0 hM1 Γ'
    hΓ'bd (by
      rw [hΓ'card]
      have e : 4 * M ^ 2 / u = δ * (L : ℝ) ^ 2 := by
        rw [hM, hu_def]
        field_simp
        ring
      rw [e]
      exact hcard)
  -- stage 1: pigeonhole on `q_y`
  obtain ⟨Q, R', hQ0, hQ, hR', hR'card, hQ₂₀, hQ₁, hQ₀⟩ := two_variable_rows (D := u) (ε := ε)
    (a := M) (M := M) (c₂₀ := c₂₀) (c₁₁ := c₁₁) (c₁₀ := c₁₀) (c₀₂ := c₀₂) (c₀₁ := c₀₁)
    (c₀₀ := c₀₀) hu hε0 hε1 hu6 (by positivity) le_rfl Γ'
    (fun z hz => ⟨(hΓ'bd z hz).1, (hΓ'bd z hz).2.1⟩) R hR hRcard hrows hΓ'poly
  -- stage 2: the columns
  obtain ⟨q, hq0, hq, b₁₁, b₁₀, b₀₂, b₀₁, b₀₀⟩ := two_variable_columns
    (D := 2 * 10 ^ 5 * u ^ 7) (η := 10 ^ 12 * ε * u ^ 12) (a := M) (M := M) (Q := (Q : ℝ))
    (c₁₁ := c₁₁) (c₁₀ := c₁₀) (c₀₂ := c₀₂) (c₀₁ := c₀₁) (c₀₀ := c₀₀) hD₂ hη0 hη hMD₂
    (by positivity) le_rfl R' hR' hR'card hQ₁ hQ₀
  -- conversion of the constants
  have conv : ∀ k : ℕ, k ≤ 2 →
      10 ^ 13 * (10 ^ 12 * ε * u ^ 12) * (2 * 10 ^ 5 * u ^ 7) ^ 13 / M ^ k
        ≤ 10 ^ 95 * ε / (δ ^ 103 * (L : ℝ) ^ k) := by
    intro k hk
    have e : 10 ^ 13 * (10 ^ 12 * ε * u ^ 12) * (2 * 10 ^ 5 * u ^ 7) ^ 13 / M ^ k
        = (10 ^ 25 * (2 * 10 ^ 5) ^ 13 * 2 ^ k) * ε / (δ ^ 103 * (L : ℝ) ^ k) := by
      rw [hM, hu_def, div_pow]
      field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hK : (10 : ℝ) ^ 25 * (2 * 10 ^ 5) ^ 13 * 2 ^ k ≤ 10 ^ 95 := by
      interval_cases k <;> norm_num
    exact mul_le_mul_of_nonneg_right hK hε0
  have hqpos : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hD₂13 : 10 ^ 6 * (2 * 10 ^ 5 * u ^ 7) ^ 7 ≤ 10 ^ 13 * (2 * 10 ^ 5 * u ^ 7) ^ 13 := by
    have : (2 * 10 ^ 5 * u ^ 7) ^ 7 ≤ (2 * 10 ^ 5 * u ^ 7) ^ 13 :=
      pow_le_pow_right₀ hD₂ (by norm_num)
    calc 10 ^ 6 * (2 * 10 ^ 5 * u ^ 7) ^ 7 ≤ 10 ^ 13 * (2 * 10 ^ 5 * u ^ 7) ^ 7 :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ 10 ^ 13 * (2 * 10 ^ 5 * u ^ 7) ^ 13 := mul_le_mul_of_nonneg_left this (by positivity)
  refine ⟨Q * q, by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · push_cast
    have h1 : (Q : ℝ) * q ≤ (2 * 10 ^ 5 * u ^ 6) * (10 ^ 6 * (2 * 10 ^ 5 * u ^ 7) ^ 7) :=
      mul_le_mul hQ hq hqpos (by positivity)
    have e : (2 * 10 ^ 5 * u ^ 6) * (10 ^ 6 * (2 * 10 ^ 5 * u ^ 7) ^ 7)
        = (2 * 10 ^ 11 * (2 * 10 ^ 5) ^ 7) * u ^ 55 := by ring
    have e2 : 10 ^ 49 / δ ^ 55 = 10 ^ 49 * u ^ 55 := by
      rw [hu_def, inv_pow]; ring
    rw [e2]
    have h3 : (2 * 10 ^ 11 * (2 * 10 ^ 5) ^ 7 : ℝ) * u ^ 55 ≤ 10 ^ 49 * u ^ 55 :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    linarith
  · -- `c₂₀`
    have e : ((Q * q : ℕ) : ℝ) * c₂₀ = (q : ℝ) * ((Q : ℝ) * c₂₀) := by push_cast; ring
    rw [e]
    refine (norm_natCast_mul_coe_le q _).trans ?_
    refine le_trans ?_ (conv 2 le_rfl)
    calc (q : ℝ) * ‖(((Q : ℝ) * c₂₀ : ℝ) : UnitAddCircle)‖
        ≤ (10 ^ 6 * (2 * 10 ^ 5 * u ^ 7) ^ 7) * (10 ^ 12 * ε * u ^ 12 / M ^ 2) :=
          mul_le_mul (by simpa using hq) hQ₂₀ (norm_nonneg _) (by positivity)
      _ = (10 ^ 6 * (2 * 10 ^ 5 * u ^ 7) ^ 7) * (10 ^ 12 * ε * u ^ 12) / M ^ 2 := by ring
      _ ≤ (10 ^ 13 * (2 * 10 ^ 5 * u ^ 7) ^ 13) * (10 ^ 12 * ε * u ^ 12) / M ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hD₂13 hη0
      _ = 10 ^ 13 * (10 ^ 12 * ε * u ^ 12) * (2 * 10 ^ 5 * u ^ 7) ^ 13 / M ^ 2 := by ring
  · -- `c₁₁`
    have e : ((Q * q : ℕ) : ℝ) * c₁₁ = (q : ℝ) * ((Q : ℝ) * c₁₁) := by push_cast; ring
    rw [e]
    refine b₁₁.trans ?_
    have := conv 2 le_rfl
    calc _ = 10 ^ 13 * (10 ^ 12 * ε * u ^ 12) * (2 * 10 ^ 5 * u ^ 7) ^ 13 / M ^ 2 := by ring
      _ ≤ _ := this
  · -- `c₀₂`
    have e : ((Q * q : ℕ) : ℝ) * c₀₂ = (q : ℝ) * ((Q : ℝ) * c₀₂) := by push_cast; ring
    rw [e]
    refine b₀₂.trans ?_
    have := conv 2 le_rfl
    calc _ = 10 ^ 13 * (10 ^ 12 * ε * u ^ 12) * (2 * 10 ^ 5 * u ^ 7) ^ 13 / M ^ 2 := by ring
      _ ≤ _ := this
  · -- `c₁₀`
    have e : ((Q * q : ℕ) : ℝ) * c₁₀ = (q : ℝ) * ((Q : ℝ) * c₁₀) := by push_cast; ring
    rw [e]
    refine b₁₀.trans ?_
    have := conv 1 (by norm_num)
    simp only [pow_one] at this
    exact this
  · -- `c₀₁`
    have e : ((Q * q : ℕ) : ℝ) * c₀₁ = (q : ℝ) * ((Q : ℝ) * c₀₁) := by push_cast; ring
    rw [e]
    refine b₀₁.trans ?_
    have := conv 1 (by norm_num)
    simp only [pow_one] at this
    exact this
  · -- `c₀₀`
    have e : ((Q * q : ℕ) : ℝ) * c₀₀ = (q : ℝ) * ((Q : ℝ) * c₀₀) := by push_cast; ring
    rw [e]
    refine b₀₀.trans ?_
    have := conv 0 (by norm_num)
    simp only [pow_zero, mul_one, div_one] at this
    calc _ = 10 ^ 13 * (10 ^ 12 * ε * u ^ 12) * (2 * 10 ^ 5 * u ^ 7) ^ 13 := by ring
      _ ≤ _ := this

/-- **Many-dilates Vinogradov lemma for pairs (type II), degree at most two** (two variables; the
pigeonhole on `Q_{ℓ'}`).

There is an absolute constant `C` (one may take `C = 10¹⁰⁰`) such that: if `0 < δ ≤ 1`,
`ε ≤ δ^C / C`, `L ≥ C δ^{-C}` is a natural number, `Γ ⊆ (L/2, L]²` is a set of pairs of integers
with `|Γ| ≥ δ L²`, and `P(x, y) = c₀₀ + c₁₀ x + c₀₁ y + c₂₀ x² + c₁₁ x y + c₀₂ y²` satisfies
`‖P(ℓ, ℓ')‖_{ℝ/ℤ} ≤ ε` on `Γ`, then there is a positive integer `q ≤ C δ^{-C}` with
`‖q c_{ij}‖ ≤ C δ^{-C} ε / L^{i+j}` for all six coefficients. -/
theorem vinogradov_two_var :
    ∃ C : ℕ, ∀ (δ ε : ℝ), 0 < δ → δ ≤ 1 → ε ≤ δ ^ C / C →
      ∀ (c₀₀ c₁₀ c₀₁ c₂₀ c₁₁ c₀₂ : ℝ) (L : ℕ), (C : ℝ) * (δ ^ C)⁻¹ ≤ L →
        ∀ Γ : Finset (ℕ × ℕ),
          (∀ p ∈ Γ, (L : ℝ) / 2 < p.1 ∧ (p.1 : ℝ) ≤ L ∧ (L : ℝ) / 2 < p.2 ∧ (p.2 : ℝ) ≤ L) →
          δ * (L : ℝ) ^ 2 ≤ Γ.card →
          (∀ p ∈ Γ, ‖((c₀₀ + c₁₀ * (p.1 : ℝ) + c₀₁ * (p.2 : ℝ) + c₂₀ * (p.1 : ℝ) ^ 2
              + c₁₁ * (p.1 : ℝ) * (p.2 : ℝ) + c₀₂ * (p.2 : ℝ) ^ 2 : ℝ) : UnitAddCircle)‖ ≤ ε) →
          ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ C * (δ ^ C)⁻¹ ∧
            ‖(((q : ℝ) * c₂₀ : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / (L : ℝ) ^ 2 ∧
            ‖(((q : ℝ) * c₁₁ : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / (L : ℝ) ^ 2 ∧
            ‖(((q : ℝ) * c₀₂ : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / (L : ℝ) ^ 2 ∧
            ‖(((q : ℝ) * c₁₀ : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / (L : ℝ) ∧
            ‖(((q : ℝ) * c₀₁ : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / (L : ℝ) ∧
            ‖(((q : ℝ) * c₀₀ : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε := by
  refine ⟨10 ^ 100, ?_⟩
  intro δ ε hδ hδ1 hε c₀₀ c₁₀ c₀₁ c₂₀ c₁₁ c₀₂ L hL Γ hΓ hcard h
  have hCr : (((10 ^ 100 : ℕ)) : ℝ) = 10 ^ 100 := by push_cast; ring
  rw [hCr] at hε hL ⊢
  set C : ℕ := 10 ^ 100 with hC
  have hδC : δ ^ C ≤ δ ^ 96 := pow_le_pow_of_le_one hδ.le hδ1 (by norm_num [hC])
  have hδC42 : δ ^ C ≤ δ ^ 42 := pow_le_pow_of_le_one hδ.le hδ1 (by norm_num [hC])
  have hδCpos : 0 < δ ^ C := by positivity
  have hL0 : (0 : ℝ) < L := by
    refine lt_of_lt_of_le ?_ hL
    positivity
  have hΓne : Γ.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < Γ.card := lt_of_lt_of_le (by positivity) hcard
    exact_mod_cast this
  have hε0 : 0 ≤ ε := by
    obtain ⟨p, hp⟩ := hΓne
    exact (norm_nonneg _).trans (h p hp)
  have hε' : 10 ^ 88 * ε ≤ δ ^ 96 := by
    have h1 : ε * 10 ^ 100 ≤ δ ^ C := by
      rwa [le_div_iff₀ (by positivity)] at hε
    linarith only [h1, hδC, pow_nonneg hδ.le 96]
  have hL' : 2 * 10 ^ 38 ≤ δ ^ 42 * L := by
    have h1 : 10 ^ 100 ≤ δ ^ C * L := by
      have h2 := mul_le_mul_of_nonneg_left hL hδCpos.le
      have h3 : δ ^ C * (10 ^ 100 * (δ ^ C)⁻¹) = 10 ^ 100 := by field_simp
      rw [h3] at h2
      exact h2
    exact (by norm_num : (2 : ℝ) * 10 ^ 38 ≤ 10 ^ 100).trans
      (h1.trans (mul_le_mul_of_nonneg_right hδC42 hL0.le))
  obtain ⟨q, hq0, hq, b₂₀, b₁₁, b₀₂, b₁₀, b₀₁, b₀₀⟩ :=
    vinogradov_two_var_explicit hδ hδ1 hε' c₀₀ c₁₀ c₀₁ c₂₀ c₁₁ c₀₂ L hL' Γ hΓ hcard h
  refine ⟨q, hq0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine hq.trans ?_
    have := div_pow_mul_le (c := 10 ^ 49) (C := 10 ^ 100) (ε := 1) hδ hδ1 zero_le_one
      (by norm_num) (by norm_num) (m := 55) (n := C) (by norm_num [hC]) (X := 1) one_pos
    simpa using this
  · exact b₂₀.trans (div_pow_mul_le hδ hδ1 hε0 (by norm_num) (by norm_num)
      (m := 103) (n := C) (by norm_num [hC]) (pow_pos hL0 2))
  · exact b₁₁.trans (div_pow_mul_le hδ hδ1 hε0 (by norm_num) (by norm_num)
      (m := 103) (n := C) (by norm_num [hC]) (pow_pos hL0 2))
  · exact b₀₂.trans (div_pow_mul_le hδ hδ1 hε0 (by norm_num) (by norm_num)
      (m := 103) (n := C) (by norm_num [hC]) (pow_pos hL0 2))
  · refine b₁₀.trans ?_
    exact div_pow_mul_le hδ hδ1 hε0 (by norm_num) (by norm_num)
      (m := 103) (n := C) (by norm_num [hC]) hL0
  · refine b₀₁.trans ?_
    exact div_pow_mul_le hδ hδ1 hε0 (by norm_num) (by norm_num)
      (m := 103) (n := C) (by norm_num [hC]) hL0
  · refine b₀₀.trans ?_
    have := div_pow_mul_le (c := 10 ^ 95) (C := 10 ^ 100) hδ hδ1 hε0 (by norm_num) (by norm_num)
      (m := 103) (n := C) (by norm_num [hC]) (X := 1) one_pos
    simpa using this

/-- **The type II lemma in the separate-variable form** `P(ℓ, ℓ') = u(ℓ) + v(ℓ')` with real
polynomials `u, v` of degree at most `2` (the shape of the character computation, which has no mixed
term): the same conclusion for the coefficients of `u` and `v` and the constant term `u₀ + v₀`. -/
theorem vinogradov_two_var_separate :
    ∃ C : ℕ, ∀ (δ ε : ℝ), 0 < δ → δ ≤ 1 → ε ≤ δ ^ C / C →
      ∀ u v : Polynomial ℝ, u.natDegree ≤ 2 → v.natDegree ≤ 2 →
        ∀ L : ℕ, (C : ℝ) * (δ ^ C)⁻¹ ≤ L →
          ∀ Γ : Finset (ℕ × ℕ),
            (∀ p ∈ Γ, (L : ℝ) / 2 < p.1 ∧ (p.1 : ℝ) ≤ L ∧ (L : ℝ) / 2 < p.2 ∧ (p.2 : ℝ) ≤ L) →
            δ * (L : ℝ) ^ 2 ≤ Γ.card →
            (∀ p ∈ Γ, ‖((u.eval (p.1 : ℝ) + v.eval (p.2 : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε) →
            ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ C * (δ ^ C)⁻¹ ∧
              ‖(((q : ℝ) * u.coeff 2 : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / (L : ℝ) ^ 2 ∧
              ‖(((q : ℝ) * v.coeff 2 : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / (L : ℝ) ^ 2 ∧
              ‖(((q : ℝ) * u.coeff 1 : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / (L : ℝ) ∧
              ‖(((q : ℝ) * v.coeff 1 : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / (L : ℝ) ∧
              ‖(((q : ℝ) * (u.coeff 0 + v.coeff 0) : ℝ) : UnitAddCircle)‖
                ≤ C * (δ ^ C)⁻¹ * ε := by
  obtain ⟨C, hC⟩ := vinogradov_two_var
  refine ⟨C, fun δ ε hδ hδ1 hε u v hu hv L hL Γ hΓ hcard h => ?_⟩
  obtain ⟨q, hq0, hq, b₂₀, -, b₀₂, b₁₀, b₀₁, b₀₀⟩ := hC δ ε hδ hδ1 hε (u.coeff 0 + v.coeff 0)
    (u.coeff 1) (v.coeff 1) (u.coeff 2) 0 (v.coeff 2) L hL Γ hΓ hcard (by
      intro p hp
      have := h p hp
      rw [eval_eq_of_natDegree_le_two u hu, eval_eq_of_natDegree_le_two v hv] at this
      have e : u.coeff 0 + v.coeff 0 + u.coeff 1 * (p.1 : ℝ) + v.coeff 1 * (p.2 : ℝ)
          + u.coeff 2 * (p.1 : ℝ) ^ 2 + 0 * (p.1 : ℝ) * (p.2 : ℝ) + v.coeff 2 * (p.2 : ℝ) ^ 2
          = u.coeff 2 * (p.1 : ℝ) ^ 2 + u.coeff 1 * (p.1 : ℝ) + u.coeff 0
            + (v.coeff 2 * (p.2 : ℝ) ^ 2 + v.coeff 1 * (p.2 : ℝ) + v.coeff 0) := by ring
      rw [e]
      exact this)
  exact ⟨q, hq0, hq, b₂₀, b₀₂, b₁₀, b₀₁, b₀₀⟩

end PrimeCarleson.Proof.Fplus31

module

public import PrimeCarleson.Proof.Fplus31.Vinogradov.Quadratic
public import PrimeCarleson.Proof.Fplus31.Vinogradov.Rows

/-!
# The Vinogradov lemma in two variables, degree at most two

Vinogradov-type estimate used by the extrapolation step of the iteration of `C2/CMain.lean` (proof
of [F+] Proposition 3.1), two variables (type II, via Fubini; a pigeonhole on `Q_{ℓ'}` is needed).
The polynomial `P(x, y) = c₀₀ + c₁₀ x + c₀₁ y + c₂₀ x² + c₁₁ x y + c₀₂ y²` is small on a dense set
`Γ` of pairs.

1. `two_variable_rows`: for each `y` in a dense set `R` of rows, `x ↦ P(x, y)` is a quadratic
   polynomial in `x` that is small on the dense row `{x : (x, y) ∈ Γ}`; the quadratic lemma gives
   `q_y`; pigeonhole `q_y = Q` on a dense `R' ⊆ R`.  Then `‖Q c₂₀‖` is small and, for `y ∈ R'`,
   `Q (c₁₀ + c₁₁ y)` and `Q (c₀₀ + c₀₁ y + c₀₂ y²)` are small;
2. `two_variable_columns`: the linear lemma (for `c₁₁, c₁₀`) and the quadratic lemma (for
   `c₀₂, c₀₁, c₀₀`) in the variable `y ∈ R'`, with a multiplier `q`.

`Q q` is the final multiplier.  Constants are explicit polynomials in `D = κ⁻¹`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- Rows: the pigeonhole on the multiplier `q_y` (the first half of the two-variable lemma). -/
theorem two_variable_rows {D ε a M c₂₀ c₁₁ c₁₀ c₀₂ c₀₁ c₀₀ : ℝ} (hD : 1 ≤ D) (hε0 : 0 ≤ ε)
    (hε : 10 ^ 12 * ε * D ^ 12 ≤ 1) (hM : 10 ^ 6 * D ^ 6 ≤ M) (ha0 : 0 ≤ a) (haM : a ≤ M)
    (Γ : Finset (ℤ × ℤ)) (hΓ : ∀ p ∈ Γ, a ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ a + M)
    (R : Finset ℤ) (hR : ∀ y ∈ R, a ≤ (y : ℝ) ∧ (y : ℝ) ≤ a + M) (hRcard : M / D ≤ R.card)
    (hrows : ∀ y ∈ R, M / D ≤ (pairRow Γ y).card)
    (h : ∀ p ∈ Γ, ‖((c₀₀ + c₁₀ * (p.1 : ℝ) + c₀₁ * (p.2 : ℝ) + c₂₀ * (p.1 : ℝ) ^ 2
        + c₁₁ * (p.1 : ℝ) * (p.2 : ℝ) + c₀₂ * (p.2 : ℝ) ^ 2 : ℝ) : UnitAddCircle)‖ ≤ ε) :
    ∃ (Q : ℕ) (R' : Finset ℤ), 0 < Q ∧ (Q : ℝ) ≤ 2 * 10 ^ 5 * D ^ 6 ∧
      (∀ y ∈ R', a ≤ (y : ℝ) ∧ (y : ℝ) ≤ a + M) ∧ M / (2 * 10 ^ 5 * D ^ 7) ≤ R'.card ∧
      ‖(((Q : ℝ) * c₂₀ : ℝ) : UnitAddCircle)‖ ≤ 10 ^ 12 * ε * D ^ 12 / M ^ 2 ∧
      (∀ y ∈ R', ‖((((Q : ℝ) * c₁₁ * (y : ℝ) + Q * c₁₀ : ℝ)) : UnitAddCircle)‖
        ≤ 10 ^ 12 * ε * D ^ 12 / M) ∧
      (∀ y ∈ R', ‖((((Q : ℝ) * c₀₂ * (y : ℝ) ^ 2 + Q * c₀₁ * (y : ℝ) + Q * c₀₀ : ℝ))
        : UnitAddCircle)‖ ≤ 10 ^ 12 * ε * D ^ 12) := by
  have hD0 : 0 < D := by linarith
  have hD6 : 1 ≤ D ^ 6 := one_le_pow₀ hD
  have hM1 : 1 ≤ M := by linarith only [hM, hD6]
  have hM0 : 0 < M := by linarith
  -- the quadratic lemma in each row
  have hq : ∀ y ∈ R, ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ 2 * 10 ^ 5 * D ^ 6 ∧
      ‖(((q : ℝ) * c₂₀ : ℝ) : UnitAddCircle)‖ ≤ 10 ^ 12 * ε * D ^ 12 / M ^ 2 ∧
      ‖(((q : ℝ) * (c₁₀ + c₁₁ * (y : ℝ)) : ℝ) : UnitAddCircle)‖ ≤ 10 ^ 12 * ε * D ^ 12 / M ∧
      ‖(((q : ℝ) * (c₀₀ + c₀₁ * (y : ℝ) + c₀₂ * (y : ℝ) ^ 2) : ℝ) : UnitAddCircle)‖
        ≤ 10 ^ 12 * ε * D ^ 12 := by
    intro y hy
    obtain ⟨q, hq0, hq, hq2, hq1, hq0'⟩ := quadratic_vinogradov hD hε0 hε hM ha0 haM
      (pairRow Γ y) (fun x hx => hΓ (x, y) (mem_pairRow.mp hx)) (hrows y hy)
      (a₂ := c₂₀) (a₁ := c₁₀ + c₁₁ * (y : ℝ)) (a₀ := c₀₀ + c₀₁ * (y : ℝ) + c₀₂ * (y : ℝ) ^ 2)
      (fun x hx => by
        have := h (x, y) (mem_pairRow.mp hx)
        have e : c₂₀ * (x : ℝ) ^ 2 + (c₁₀ + c₁₁ * (y : ℝ)) * x
            + (c₀₀ + c₀₁ * (y : ℝ) + c₀₂ * (y : ℝ) ^ 2)
            = c₀₀ + c₁₀ * (x : ℝ) + c₀₁ * (y : ℝ) + c₂₀ * (x : ℝ) ^ 2
              + c₁₁ * (x : ℝ) * (y : ℝ) + c₀₂ * (y : ℝ) ^ 2 := by ring
        rw [e]
        exact this)
    exact ⟨q, hq0, hq, hq2, hq1, hq0'⟩
  choose! qf hqf using hq
  -- pigeonhole on the value of `q_y`
  set N : ℕ := ⌊2 * 10 ^ 5 * D ^ 6⌋₊ with hN
  have hN30 : (N : ℝ) ≤ 2 * 10 ^ 5 * D ^ 6 := Nat.floor_le (by positivity)
  have hN1 : 1 ≤ N := by
    apply Nat.le_floor
    push_cast
    linarith only [hD6]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hmaps : ∀ y ∈ R, qf y ∈ Finset.Icc 1 N := by
    intro y hy
    obtain ⟨h1, h2, -⟩ := hqf y hy
    rw [Finset.mem_Icc]
    exact ⟨h1, Nat.le_floor h2⟩
  have hRne : R.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < R.card := lt_of_lt_of_le (by positivity) hRcard
    exact_mod_cast this
  obtain ⟨Q, hQ, hQ'⟩ := exists_fiber_ge R (Finset.Icc 1 N) qf hmaps
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN1⟩⟩
  set R' := R.filter (fun y => qf y = Q) with hR'
  have hQN : (Q : ℝ) ≤ 2 * 10 ^ 5 * D ^ 6 := by
    have : Q ≤ N := (Finset.mem_Icc.mp hQ).2
    exact (by exact_mod_cast this : (Q : ℝ) ≤ N).trans hN30
  have hQ1 : 0 < Q := (Finset.mem_Icc.mp hQ).1
  have hR'card : M / (2 * 10 ^ 5 * D ^ 7) ≤ R'.card := by
    have h1 : ((Finset.Icc 1 N).card : ℝ) = N := by simp
    rw [h1] at hQ'
    refine le_trans ?_ hQ'
    calc M / (2 * 10 ^ 5 * D ^ 7) = (M / D) / (2 * 10 ^ 5 * D ^ 6) := by field_simp
      _ ≤ (R.card : ℝ) / (2 * 10 ^ 5 * D ^ 6) :=
          div_le_div_of_nonneg_right hRcard (by positivity)
      _ ≤ (R.card : ℝ) / N := div_le_div_of_nonneg_left (by positivity) hNpos hN30
  have hR'ne : R'.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < R'.card := lt_of_lt_of_le (by positivity) hR'card
    exact_mod_cast this
  have hR'mem : ∀ y ∈ R', y ∈ R ∧ qf y = Q := fun y hy => Finset.mem_filter.mp hy
  refine ⟨Q, R', hQ1, hQN, fun y hy => hR y (hR'mem y hy).1, hR'card, ?_, ?_, ?_⟩
  · obtain ⟨y₀, hy₀⟩ := hR'ne
    obtain ⟨h1, h2⟩ := hR'mem y₀ hy₀
    have := (hqf y₀ h1).2.2.1
    rwa [h2] at this
  · intro y hy
    obtain ⟨h1, h2⟩ := hR'mem y hy
    have := (hqf y h1).2.2.2.1
    rw [h2] at this
    have e : (Q : ℝ) * c₁₁ * (y : ℝ) + Q * c₁₀ = (Q : ℝ) * (c₁₀ + c₁₁ * (y : ℝ)) := by ring
    rw [e]
    exact this
  · intro y hy
    obtain ⟨h1, h2⟩ := hR'mem y hy
    have := (hqf y h1).2.2.2.2
    rw [h2] at this
    have e : (Q : ℝ) * c₀₂ * (y : ℝ) ^ 2 + Q * c₀₁ * (y : ℝ) + Q * c₀₀
        = (Q : ℝ) * (c₀₀ + c₀₁ * (y : ℝ) + c₀₂ * (y : ℝ) ^ 2) := by ring
    rw [e]
    exact this

/-- Columns: the linear lemma for `c₁₁, c₁₀` and the quadratic lemma for `c₀₂, c₀₁, c₀₀` in the
variable `y` on the dense set `R`, for the polynomials `Q c₁₁ y + Q c₁₀` and
`Q c₀₂ y² + Q c₀₁ y + Q c₀₀`, which are small (the second of size `η`, the first of size
`η / M`). -/
theorem two_variable_columns {D η a M Q c₁₁ c₁₀ c₀₂ c₀₁ c₀₀ : ℝ} (hD : 1 ≤ D) (hη0 : 0 ≤ η)
    (hη : 10 ^ 12 * η * D ^ 12 ≤ 1) (hM : 10 ^ 6 * D ^ 6 ≤ M) (ha0 : 0 ≤ a) (haM : a ≤ M)
    (R : Finset ℤ) (hR : ∀ y ∈ R, a ≤ (y : ℝ) ∧ (y : ℝ) ≤ a + M) (hcard : M / D ≤ R.card)
    (h1 : ∀ y ∈ R, ‖(((Q * c₁₁ * (y : ℝ) + Q * c₁₀ : ℝ)) : UnitAddCircle)‖ ≤ η / M)
    (h2 : ∀ y ∈ R, ‖(((Q * c₀₂ * (y : ℝ) ^ 2 + Q * c₀₁ * (y : ℝ) + Q * c₀₀ : ℝ))
      : UnitAddCircle)‖ ≤ η) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ 10 ^ 6 * D ^ 7 ∧
      ‖(((q : ℝ) * (Q * c₁₁) : ℝ) : UnitAddCircle)‖ ≤ 10 ^ 13 * η * D ^ 13 / M ^ 2 ∧
      ‖(((q : ℝ) * (Q * c₁₀) : ℝ) : UnitAddCircle)‖ ≤ 10 ^ 13 * η * D ^ 13 / M ∧
      ‖(((q : ℝ) * (Q * c₀₂) : ℝ) : UnitAddCircle)‖ ≤ 10 ^ 13 * η * D ^ 13 / M ^ 2 ∧
      ‖(((q : ℝ) * (Q * c₀₁) : ℝ) : UnitAddCircle)‖ ≤ 10 ^ 13 * η * D ^ 13 / M ∧
      ‖(((q : ℝ) * (Q * c₀₀) : ℝ) : UnitAddCircle)‖ ≤ 10 ^ 13 * η * D ^ 13 := by
  have hD0 : 0 < D := by linarith
  have hD6 : 1 ≤ D ^ 6 := one_le_pow₀ hD
  have hM1 : 1 ≤ M := by linarith only [hM, hD6]
  have hM0 : 0 < M := by linarith
  have hDM : ∀ j : ℕ, j ≤ 12 → η * D ^ j ≤ 1 / 10 ^ 12 := by
    intro j hj
    have h1 : D ^ j ≤ D ^ 12 := pow_le_pow_right₀ hD hj
    have h2 : η * D ^ j ≤ η * D ^ 12 := mul_le_mul_of_nonneg_left h1 hη0
    have h3 : η * D ^ 12 ≤ 1 / 10 ^ 12 := by
      rw [le_div_iff₀ (by positivity)]
      linarith only [hη]
    linarith only [h2, h3]
  have hD2 : 80 * D ^ 2 ≤ M := by
    have : D ^ 2 ≤ D ^ 6 := pow_le_pow_right₀ hD (by norm_num)
    linarith only [this, hM, sq_nonneg D]
  -- the linear lemma
  obtain ⟨q₂, hq₂0, hq₂5, hα, hβ⟩ := linear_vinogradov_inv (D := D) (ε := η / M) (a := a)
    (M := M) (R := 2 * M) (α := Q * c₁₁) (β := Q * c₁₀) hD (by positivity)
    (by
      have h1 : η * D ≤ 1 / 10 ^ 12 := by simpa using hDM 1 (by norm_num)
      have e : 16 * (η / M) * D = 16 * (η * D) / M := by ring
      rw [e, div_le_one hM0]
      linarith only [h1, hM1])
    hD2 R hR hcard
    (fun y hy => by
      obtain ⟨hy1, hy2⟩ := hR y hy
      rw [abs_of_nonneg (by linarith only [ha0, hy1])]
      linarith only [haM, hy2])
    (fun y hy => h1 y hy)
  -- the quadratic lemma
  obtain ⟨q₃, hq₃0, hq₃, hγ₂, hγ₁, hγ₀⟩ := quadratic_vinogradov hD hη0 hη hM ha0 haM R hR hcard
    (a₂ := Q * c₀₂) (a₁ := Q * c₀₁) (a₀ := Q * c₀₀) h2
  have hq₂0' : (0 : ℝ) ≤ q₂ := Nat.cast_nonneg q₂
  have hq₃0' : (0 : ℝ) ≤ q₃ := Nat.cast_nonneg q₃
  have hηM : 0 ≤ η / M := by positivity
  have hD8 : D ^ 8 ≤ D ^ 13 := pow_le_pow_right₀ hD (by norm_num)
  have hD13 : D ^ 13 = D * D ^ 12 := by ring
  have hηD8 : 0 ≤ η * D ^ 8 := by positivity
  have hηD13 : 0 ≤ η * D ^ 13 := by positivity
  refine ⟨q₂ * q₃, by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · push_cast
    have := mul_le_mul hq₂5 hq₃ hq₃0' (by positivity)
    linarith only [this]
  · -- `c₁₁`
    have e : ((q₂ * q₃ : ℕ) : ℝ) * (Q * c₁₁) = (q₃ : ℝ) * ((q₂ : ℝ) * (Q * c₁₁)) := by
      push_cast
      ring
    rw [e]
    refine (norm_natCast_mul_coe_le q₃ _).trans ?_
    calc (q₃ : ℝ) * ‖(((q₂ : ℝ) * (Q * c₁₁) : ℝ) : UnitAddCircle)‖
        ≤ (2 * 10 ^ 5 * D ^ 6) * (40 * (η / M) * D ^ 2 / M) :=
          mul_le_mul hq₃ hα (norm_nonneg _) (by positivity)
      _ = 8 * 10 ^ 6 * (η * D ^ 8) / M ^ 2 := by
        field_simp
        ring
      _ ≤ 10 ^ 13 * η * D ^ 13 / M ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith only [mul_le_mul_of_nonneg_left hD8 hη0, hηD13]
  · -- `c₁₀`
    have e : ((q₂ * q₃ : ℕ) : ℝ) * (Q * c₁₀) = (q₃ : ℝ) * ((q₂ : ℝ) * (Q * c₁₀)) := by
      push_cast
      ring
    rw [e]
    refine (norm_natCast_mul_coe_le q₃ _).trans ?_
    have hb : 5 * D * (η / M) + 2 * M * (40 * (η / M) * D ^ 2 / M)
        = (5 * D + 80 * D ^ 2) * η / M := by
      field_simp
      ring
    rw [hb] at hβ
    calc (q₃ : ℝ) * ‖(((q₂ : ℝ) * (Q * c₁₀) : ℝ) : UnitAddCircle)‖
        ≤ (2 * 10 ^ 5 * D ^ 6) * ((5 * D + 80 * D ^ 2) * η / M) :=
          mul_le_mul hq₃ hβ (norm_nonneg _) (by positivity)
      _ = (2 * 10 ^ 5 * D ^ 6 * (5 * D + 80 * D ^ 2) * η) / M := by ring
      _ ≤ 10 ^ 13 * η * D ^ 13 / M := by
          apply div_le_div_of_nonneg_right _ hM0.le
          have h1 : D ^ 7 ≤ D ^ 8 := pow_le_pow_right₀ hD (by norm_num)
          have h2 : D ^ 6 * (5 * D + 80 * D ^ 2) ≤ 85 * D ^ 8 := by linarith only [h1]
          linarith only [mul_le_mul_of_nonneg_left h2 hη0, mul_le_mul_of_nonneg_left hD8 hη0,
            hηD13]
  · -- `c₀₂`
    have e : ((q₂ * q₃ : ℕ) : ℝ) * (Q * c₀₂) = (q₂ : ℝ) * ((q₃ : ℝ) * (Q * c₀₂)) := by
      push_cast
      ring
    rw [e]
    refine (norm_natCast_mul_coe_le q₂ _).trans ?_
    calc (q₂ : ℝ) * ‖(((q₃ : ℝ) * (Q * c₀₂) : ℝ) : UnitAddCircle)‖
        ≤ (5 * D) * (10 ^ 12 * η * D ^ 12 / M ^ 2) :=
          mul_le_mul hq₂5 hγ₂ (norm_nonneg _) (by positivity)
      _ = 5 * 10 ^ 12 * (η * D ^ 13) / M ^ 2 := by field_simp
      _ ≤ 10 ^ 13 * η * D ^ 13 / M ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith only [hηD13]
  · -- `c₀₁`
    have e : ((q₂ * q₃ : ℕ) : ℝ) * (Q * c₀₁) = (q₂ : ℝ) * ((q₃ : ℝ) * (Q * c₀₁)) := by
      push_cast
      ring
    rw [e]
    refine (norm_natCast_mul_coe_le q₂ _).trans ?_
    calc (q₂ : ℝ) * ‖(((q₃ : ℝ) * (Q * c₀₁) : ℝ) : UnitAddCircle)‖
        ≤ (5 * D) * (10 ^ 12 * η * D ^ 12 / M) :=
          mul_le_mul hq₂5 hγ₁ (norm_nonneg _) (by positivity)
      _ = 5 * 10 ^ 12 * (η * D ^ 13) / M := by field_simp
      _ ≤ 10 ^ 13 * η * D ^ 13 / M := by
          apply div_le_div_of_nonneg_right _ hM0.le
          linarith only [hηD13]
  · -- `c₀₀`
    have e : ((q₂ * q₃ : ℕ) : ℝ) * (Q * c₀₀) = (q₂ : ℝ) * ((q₃ : ℝ) * (Q * c₀₀)) := by
      push_cast
      ring
    rw [e]
    refine (norm_natCast_mul_coe_le q₂ _).trans ?_
    calc (q₂ : ℝ) * ‖(((q₃ : ℝ) * (Q * c₀₀) : ℝ) : UnitAddCircle)‖
        ≤ (5 * D) * (10 ^ 12 * η * D ^ 12) :=
          mul_le_mul hq₂5 hγ₀ (norm_nonneg _) (by positivity)
      _ = 5 * 10 ^ 12 * (η * D ^ 13) := by ring
      _ ≤ 10 ^ 13 * η * D ^ 13 := by linarith only [hηD13]

end PrimeCarleson.Proof.Fplus31

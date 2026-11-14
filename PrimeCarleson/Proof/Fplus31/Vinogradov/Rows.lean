module

public import PrimeCarleson.Proof.Fplus31.Vinogradov.Differencing

/-!
# Dense rows of a dense set of pairs

Vinogradov-type estimate used by the extrapolation step of the iteration of `C2/CMain.lean` (proof
of [F+] Proposition 3.1), two variables (for each `ℓ'` in a dense set apply the one-variable lemma
in `ℓ`).

`exists_dense_rows`: a set `Γ` of pairs of integers in `[a, a + M]²` with `|Γ| ≥ 4 M² / D` has a
set `R` of at least `M / D` values `y` of the second coordinate whose row
`{x : (x, y) ∈ Γ}` has at least `M / D` elements.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- The row `{x : (x, y) ∈ Γ}` of a set of pairs. -/
def pairRow (Γ : Finset (ℤ × ℤ)) (y : ℤ) : Finset ℤ :=
  (Γ.filter (fun p => p.2 = y)).image Prod.fst

theorem mem_pairRow {Γ : Finset (ℤ × ℤ)} {x y : ℤ} : x ∈ pairRow Γ y ↔ (x, y) ∈ Γ := by
  simp only [pairRow, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨x', y'⟩, ⟨h1, h2⟩, h3⟩
    have h2' : y' = y := h2
    have h3' : x' = x := h3
    rw [h2', h3'] at h1
    exact h1
  · intro h
    exact ⟨(x, y), ⟨h, rfl⟩, rfl⟩

theorem card_pairRow (Γ : Finset (ℤ × ℤ)) (y : ℤ) :
    (pairRow Γ y).card = (Γ.filter (fun p => p.2 = y)).card := by
  apply Finset.card_image_of_injOn
  intro p hp q hq hpq
  have hp' := (Finset.mem_filter.mp hp).2
  have hq' := (Finset.mem_filter.mp hq).2
  ext
  · exact hpq
  · exact hp'.trans hq'.symm

/-- **Dense rows.**  A set `Γ` of pairs in `[a, a + M]²`, `M ≥ 1`, with `|Γ| ≥ 4 M² / D` has a
set `R` of at least `M / D` second coordinates `y ∈ [a, a + M]` with rows of size at least
`M / D`. -/
theorem exists_dense_rows {D a M : ℝ} (hD : 0 < D) (hM : 1 ≤ M) (Γ : Finset (ℤ × ℤ))
    (hΓ : ∀ p ∈ Γ, a ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ a + M ∧ a ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ a + M)
    (hcard : 4 * M ^ 2 / D ≤ Γ.card) :
    ∃ R : Finset ℤ, (∀ y ∈ R, a ≤ (y : ℝ) ∧ (y : ℝ) ≤ a + M) ∧ M / D ≤ R.card ∧
      ∀ y ∈ R, M / D ≤ (pairRow Γ y).card := by
  classical
  set Y : Finset ℤ := Γ.image Prod.snd with hY
  have hYI : Y ⊆ Finset.Icc ⌈a⌉ ⌊a + M⌋ := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨-, -, h3, h4⟩ := hΓ p hp
    rw [Finset.mem_Icc]
    exact ⟨Int.ceil_le.mpr h3, Int.le_floor.mpr h4⟩
  have hIcard : ((Finset.Icc ⌈a⌉ ⌊a + M⌋).card : ℝ) ≤ 2 * M := by
    have := card_Icc_int_le a (a + M) (by linarith)
    linarith
  have hYcard : (Y.card : ℝ) ≤ 2 * M :=
    (by exact_mod_cast Finset.card_le_card hYI : (Y.card : ℝ) ≤ _).trans hIcard
  have hrow : ∀ y, ((pairRow Γ y).card : ℝ) ≤ 2 * M := by
    intro y
    have hsub : pairRow Γ y ⊆ Finset.Icc ⌈a⌉ ⌊a + M⌋ := by
      intro x hx
      have := hΓ (x, y) (mem_pairRow.mp hx)
      rw [Finset.mem_Icc]
      exact ⟨Int.ceil_le.mpr this.1, Int.le_floor.mpr this.2.1⟩
    exact (by exact_mod_cast Finset.card_le_card hsub : ((pairRow Γ y).card : ℝ) ≤ _).trans hIcard
  have hsum : ∑ y ∈ Y, ((pairRow Γ y).card : ℝ) = Γ.card := by
    have h1 := Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (s := Γ) (t := Y)
      (fun p hp => Finset.mem_image_of_mem _ hp)
    have h2 : ∀ y, (pairRow Γ y).card = (Γ.filter (fun p => p.2 = y)).card := card_pairRow Γ
    simp_rw [h2]
    exact_mod_cast h1.symm
  set R : Finset ℤ := Y.filter (fun y => M / D ≤ (pairRow Γ y).card) with hR
  have hRsum : ∑ y ∈ R, ((pairRow Γ y).card : ℝ) ≤ R.card * (2 * M) := by
    calc _ ≤ ∑ _y ∈ R, 2 * M := Finset.sum_le_sum (fun y _ => hrow y)
      _ = R.card * (2 * M) := by simp
  have hbad : ∑ y ∈ Y.filter (fun y => ¬ M / D ≤ ((pairRow Γ y).card : ℝ)),
      ((pairRow Γ y).card : ℝ) ≤ 2 * M ^ 2 / D := by
    calc _ ≤ ∑ _y ∈ Y.filter (fun y => ¬ M / D ≤ ((pairRow Γ y).card : ℝ)), M / D :=
          Finset.sum_le_sum (fun y hy => (not_le.mp (Finset.mem_filter.mp hy).2).le)
      _ = (Y.filter (fun y => ¬ M / D ≤ ((pairRow Γ y).card : ℝ))).card * (M / D) := by simp
      _ ≤ (2 * M) * (M / D) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact (by exact_mod_cast Finset.card_filter_le _ _ : (_ : ℝ) ≤ Y.card).trans hYcard
      _ = 2 * M ^ 2 / D := by ring
  have hsplit := Finset.sum_filter_add_sum_filter_not Y (fun y => M / D ≤ ((pairRow Γ y).card : ℝ))
    (fun y => ((pairRow Γ y).card : ℝ))
  rw [hsum] at hsplit
  refine ⟨R, ?_, ?_, fun y hy => (Finset.mem_filter.mp hy).2⟩
  · intro y hy
    have := hYI (Finset.mem_filter.mp hy).1
    rw [Finset.mem_Icc] at this
    have h1 : (⌈a⌉ : ℝ) ≤ y := by exact_mod_cast this.1
    have h2 : (y : ℝ) ≤ ⌊a + M⌋ := by exact_mod_cast this.2
    exact ⟨(Int.le_ceil a).trans h1, h2.trans (Int.floor_le _)⟩
  · have h3 : 4 * M ^ 2 / D ≤ R.card * (2 * M) + 2 * M ^ 2 / D := by linarith
    have h4 : 2 * M ^ 2 / D ≤ R.card * (2 * M) := by
      have : 4 * M ^ 2 / D = 2 * M ^ 2 / D + 2 * M ^ 2 / D := by ring
      linarith
    have h5 : M / D * (2 * M) ≤ R.card * (2 * M) := by
      calc M / D * (2 * M) = 2 * M ^ 2 / D := by ring
        _ ≤ _ := h4
    exact le_of_mul_le_mul_right h5 (by positivity)

end PrimeCarleson.Proof.Fplus31

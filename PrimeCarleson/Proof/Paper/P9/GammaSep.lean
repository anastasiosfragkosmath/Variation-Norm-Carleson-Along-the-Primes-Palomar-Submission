module

public import PrimeCarleson.Proof.Paper.Defs.Weights

/-!
# `Γ_Q` is `Q^{-2}`-separated

Source: main paper `p:global-shell-var`, L2044–L2045.
Distinct reduced fractions `a/q, a'/q'` in `[0, 1)` with denominators `≤ Q` satisfy
`|a/q - a'/q' - v| ≥ 1/(q q') ≥ Q^{-2}` for every integer `v` (`‖a/q - a'/q'‖_𝕋 ≥ Q^{-2}`).
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

/-- **The separation of `Γ_Q`** (Source: main paper `p:global-shell-var`, L2044–L2045): for distinct
`r, r' ∈ Γ_Q` and every integer `v`, `1/Q² ≤ |r - r' - v|`. -/
theorem gammaQ_sep {Q : ℕ} {r r' : ℚ} (hr : r ∈ gammaQ Q) (hr' : r' ∈ gammaQ Q) (hne : r ≠ r')
    (v : ℤ) : 1 / ((Q : ℝ) * Q) ≤ |(r : ℝ) - r' - v| := by
  rw [mem_gammaQ_real] at hr hr'
  have hq : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hq' : (0 : ℝ) < r'.den := by exact_mod_cast r'.den_pos
  set N : ℤ := r.num * r'.den - r'.num * r.den - v * r.den * r'.den with hNdef
  have hN : ((r : ℝ) - r' - v) * ((r.den : ℝ) * r'.den) = N := by
    rw [Rat.cast_def r, Rat.cast_def r', hNdef]
    push_cast
    field_simp
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0] at hN
    have hx : (r : ℝ) - r' - v = 0 := by
      have : ((r.den : ℝ) * r'.den) ≠ 0 := by positivity
      simpa [this] using hN
    have hv : (r : ℝ) - r' = v := by linarith
    have hr1 : (r : ℝ) < 1 := by exact_mod_cast hr.2.1
    have hr1' : (r' : ℝ) < 1 := by exact_mod_cast hr'.2.1
    have hr0 : (0 : ℝ) ≤ r := by exact_mod_cast hr.1
    have hr0' : (0 : ℝ) ≤ r' := by exact_mod_cast hr'.1
    have h1 : (v : ℝ) < 1 := by rw [← hv]; linarith
    have h2 : (-1 : ℝ) < v := by rw [← hv]; linarith
    have h1' : v < 1 := by exact_mod_cast h1
    have h2' : -1 < v := by exact_mod_cast h2
    have hv0 : v = 0 := by omega
    rw [hv0] at hv
    apply hne
    have : (r : ℝ) = r' := by
      have h := hv
      simp only [Int.cast_zero] at h
      linarith
    exact_mod_cast this
  have hN1 : (1 : ℝ) ≤ |(N : ℝ)| := by exact_mod_cast Int.one_le_abs hN0
  have hD : (r.den : ℝ) * r'.den ≤ Q * Q := mul_le_mul hr.2.2.2 hr'.2.2.2 hq'.le
    (by linarith [hr.2.2.2, hq])
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le hq hr.2.2.2
  have hQ : (0 : ℝ) < Q * Q := by positivity
  rw [div_le_iff₀ hQ]
  calc (1 : ℝ) ≤ |(N : ℝ)| := hN1
    _ = |(r : ℝ) - r' - v| * ((r.den : ℝ) * r'.den) := by
        rw [← hN, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (r.den : ℝ) * r'.den)]
    _ ≤ |(r : ℝ) - r' - v| * (Q * Q) := mul_le_mul_of_nonneg_left hD (abs_nonneg _)

end PrimeCarleson.Proof.Paper

module

public import PrimeCarleson.Proof.Lepingle.Path.StoppingTimes

/-!
# The comparable-jump claim of Lépingle's inequality

Source: Zorin-Kranich's notes `lem:comparable-jump` (02-Lepingle.tex, L43–L58): the Claim of
02-Lepingle.tex (L43-L92), pathwise. A jump of the path of size
`d ∈ (2, 4] · 2^{-m} M_t` between two times `t' < t` is dominated, up to the factor `8`, by one
increment of the path along the level-`m` stopping times `τ^{(m)}_j` (`stopTime`) inside `(t', t]`.

The statement is for an arbitrary path `f : ℕ → E` (no constancy after a time, no horizon). It is
written with products instead of the ratio `d / (2^{-m} M_t)` of the printed text; the hypotheses
force `M_t > 0`, so the two forms are equivalent. The level `m ≥ 1` suffices (the notes ask
`m ≥ 2`).
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Lepingle

variable {E : Type*} [PseudoMetricSpace E]

/-- **Comparable jump** (Claim of Zorin-Kranich's notes, L43-L92). Let `t' < t`, `m ≥ 1` and
`2 · 2^{-m} M_t < dist (f t') (f t) ≤ 4 · 2^{-m} M_t`. Then there are `j` and times
`τ_j = a`, `τ_{j+1} = b` of the level-`m` partition with `t' < b ≤ t` and
`dist (f t') (f t) ≤ 8 dist (f a) (f b)`. -/
theorem exists_stopTime_comparable_jump {f : ℕ → E} {m : ℕ} (hm : 1 ≤ m) {t' t : ℕ}
    (htt : t' < t) (h1 : 2 * ((2⁻¹ : ℝ) ^ m * runningOsc f t) < dist (f t') (f t))
    (h2 : dist (f t') (f t) ≤ 4 * ((2⁻¹ : ℝ) ^ m * runningOsc f t)) :
    ∃ j a b : ℕ, stopTime f m j = a ∧ stopTime f m (j + 1) = b ∧ t' < b ∧ b ≤ t ∧
      dist (f t') (f t) ≤ 8 * dist (f a) (f b) := by
  set c : ℝ := (2⁻¹ : ℝ) ^ m with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 2⁻¹ :=
    calc c = (2⁻¹ : ℝ) ^ m := rfl
      _ ≤ (2⁻¹ : ℝ) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      _ = 2⁻¹ := pow_one _
  set d := dist (f t') (f t) with hd
  have hdM : d ≤ runningOsc f t := dist_le_runningOsc f htt.le le_rfl
  have hMt : 0 < runningOsc f t := by
    rcases (runningOsc_nonneg f t).eq_or_lt with h0 | hpos
    · rw [← h0] at h1 hdM
      linarith
    · exact hpos
  -- the largest `j` with `τ_j ≤ t`
  obtain ⟨j, hj1, hj2⟩ := exists_stopTime_le_lt f m t
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top t) hj1)
  have haj : stopTime f m j = a := ha.symm
  have hat : a ≤ t := by exact_mod_cast ha ▸ hj1
  -- `τ' = a > t'`: otherwise the rule fails at both `t'` and `t`
  have hta : t' < a := by
    by_contra hcon
    have hcon' : a ≤ t' := not_lt.1 hcon
    have hr1 : ¬ StopRule f m a t' :=
      not_stopRule_of_lt_stopTime_succ haj (lt_trans (by exact_mod_cast htt) hj2)
    have hr2 : ¬ StopRule f m a t := not_stopRule_of_lt_stopTime_succ haj hj2
    have e1 := dist_le_of_not_stopRule hcon' hr1
    have e2 := dist_le_of_not_stopRule hat hr2
    rw [← hc] at e1 e2
    have e4 := mul_le_mul_of_nonneg_left (runningOsc_mono f htt.le) hc0.le
    have e5 : d ≤ dist (f t') (f a) + dist (f t) (f a) := by
      rw [hd, dist_comm (f t) (f a)]
      exact dist_triangle _ _ _
    linarith
  -- `j ≥ 1`: write `j = j' + 1`
  cases j with
  | zero =>
    rw [stopTime_zero] at haj
    have h0 : a = 0 := by exact_mod_cast haj.symm
    omega
  | succ j =>
    obtain ⟨p, hp, hrule⟩ := exists_stopRule_of_stopTime_succ_eq haj
    -- `M_{τ'} ≥ M_t / 2`
    have hMa : runningOsc f t ≤ 2 * runningOsc f a := by
      by_contra hlt
      have hlt' : 2 * runningOsc f a < runningOsc f t := not_le.1 hlt
      obtain ⟨x, y, hx, hy, hxy⟩ := exists_dist_eq_runningOsc f t
      have htri : runningOsc f t ≤ dist (f x) (f a) + dist (f a) (f y) := by
        rw [← hxy]
        exact dist_triangle _ _ _
      have hz : ∃ z : ℕ, z ≤ t ∧ runningOsc f t / 2 ≤ dist (f z) (f a) := by
        by_cases hx' : runningOsc f t / 2 ≤ dist (f x) (f a)
        · exact ⟨x, hx, hx'⟩
        · refine ⟨y, hy, ?_⟩
          rw [dist_comm (f y) (f a)]
          linarith
      obtain ⟨z, hzt, hz⟩ := hz
      have hza : a < z := by
        by_contra hcon
        have := dist_le_runningOsc f (not_lt.1 hcon) (le_refl a)
        linarith
      have hMz : dist (f z) (f a) ≤ runningOsc f z := dist_le_runningOsc f le_rfl hza.le
      have hrz : StopRule f m a z := by
        refine ⟨hza.le, by linarith, ?_⟩
        change c * runningOsc f z ≤ _
        have e3 := mul_le_mul_of_nonneg_left (runningOsc_mono f hzt) hc0.le
        have e4 := mul_le_mul_of_nonneg_right hc1 (runningOsc_nonneg f t)
        linarith
      have := (stopTime_succ_le haj hrz).trans (by exact_mod_cast hzt : (z : ℕ∞) ≤ t)
      exact absurd hj2 (not_lt.2 this)
    refine ⟨j, p, a, hp, haj, hta, hat, ?_⟩
    have e1 := mul_le_mul_of_nonneg_left hMa hc0.le
    have e2 := hrule.2.2
    rw [← hc] at e2
    rw [dist_comm (f p) (f a)]
    linarith

end PrimeCarleson.Proof.Lepingle

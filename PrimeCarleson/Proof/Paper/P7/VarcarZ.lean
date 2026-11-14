module

public import PrimeCarleson.Proof.Paper.P7.Sums

/-!
# `l:varcarZ`: the variation of maximally modulated bounded-variation multipliers on `ℤ`

Source: main paper `l:varcarZ`, L1771–L1776 and L1807–L1817, with its steps: the application of the
transference (L1813–L1816), the covering by intervals (L1808–L1811), the density argument and the
reduction from countable to finite sets of `λ` (L1812). Throughout, `k̂ : ℝ → ℂ` is measurable,
vanishes off an interval `[u, u + 1/10]` and has total variation `≤ c₀`; the kernel is
`k(n) = ∫ k̂(ξ) e(nξ) dξ`; `f` is finitely supported (the convention of the footnote L288);
`dilSum k̂ 1 f x λ = ∑_n f(x - n) e(λ n) k(n)`.

* `varcarZ_of_oplus` (`l:varcarZ`, conditional on `hO : OplusVariationBound`): for all
  `T ⊆ [0, 1)` (finite or not), `‖V^r(∑_n f(x-n) e(λ n) k(n) : λ ∈ T)‖_{ℓ²(ℤ)} ≤ C_r c₀ ‖f‖_{ℓ²}`,
  `r > 2`. This is the transference of the multipliers `m_λ(β) = k̂(β - λ)`: the chart is
  `(u - 1/2, u + 1/2]` and the multiplier is folded onto it (`dilSum_one_eq_chartMult`,
  `h = k̂ + k̂(· + 1)`, then `chart_variation`), so that the covering of `𝕋` by the ten intervals
  of length `1/10` of the paper is not needed, and neither is the density or the countable
  reduction: the set `T` is arbitrary, since `V^r` over `T` is the supremum over finite subsets
  (`halfLine_variation`, `eLpNorm_count_iSup_le`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.MswTransference
  PrimeCarleson.Proof.Goal0

/-- `dilSum k̂ 1 f x λ` is the sum `∑_n f(x - n) e(λ n) k(n)` of `l:varcarZ`. -/
theorem dilSum_one_apply (khat : ℝ → ℂ) (f : ℤ →₀ ℂ) (x : ℤ) (lam : ℝ) :
    dilSum khat 1 f x lam =
      ∑' n : ℤ, f (x - n) * e (lam * (n : ℝ)) * ∫ ξ, khat ξ * e ((n : ℝ) * ξ) := by
  simp [dilSum]

/-- A multiplier with `‖k̂‖` bounded and vanishing off `[u, u + 1/10]` is integrable and
vanishes off the chart of centre `u`. -/
theorem integrable_of_window {khat : ℝ → ℂ} (hk : Measurable khat) {u : ℝ} {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hsupp : ∀ ξ, khat ξ ≠ 0 → ξ ∈ Set.Icc u (u + 1 / 10))
    (hvar : eVariationOn khat Set.univ ≤ ENNReal.ofReal c₀) : Integrable khat := by
  have hs : ∀ s, s ∉ Set.Icc u (u + 1 / 10) → khat s = 0 := fun s hs => by
    by_contra h
    exact hs (hsupp s h)
  exact integrable_of_bound_support hk (norm_le_of_eVariationOn hs hc₀ hvar) hs

/-- The `ℓ²` norm as a `tsum`, for the exponent `2` of `l:varcarZ`. -/
theorem eLpNorm_two_eq_tsum_sq (F : ℤ → ℝ≥0∞) :
    eLpNorm F (ENNReal.ofReal 2) Measure.count = (∑' x : ℤ, F x ^ 2) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_count_eq_tsum_enn F two_pos]
  simp_rw [ENNReal.rpow_two]

/-- The `ℓ²` norm of a finitely supported sequence as a `tsum`. -/
theorem eLpNorm_two_eq_tsum_sq' (f : ℤ →₀ ℂ) :
    eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count = (∑' x : ℤ, ‖f x‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_count_eq_tsum _ two_pos]
  simp_rw [ENNReal.rpow_two]

/-- For `s > 2`, the conjugate exponent `s/(s-1)` is `< 2`. -/
theorem two_gt_conj {s : ℝ} (hs : 2 < s) : s / (s - 1) < 2 := by
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-- If the variation of `k̂` is `≤ c₀ < 0` then `k̂ = 0`, and the modulated sums vanish. -/
theorem zero_case_of_variation {r : ℝ} (hr : 2 < r) {khat : ℝ → ℂ} {u c₀ : ℝ}
    (hsupp : ∀ ξ, khat ξ ≠ 0 → ξ ∈ Set.Icc u (u + 1 / 10))
    (hvar : eVariationOn khat Set.univ ≤ ENNReal.ofReal c₀) (hc : c₀ < 0) (f : ℤ →₀ ℂ)
    (T : Set ℝ) :
    (∑' x : ℤ, rVariationOn r T (fun lam => dilSum khat 1 f x lam) ^ 2) ^ (1 / 2 : ℝ) = 0 := by
  have hc0 : ENNReal.ofReal c₀ = 0 := ENNReal.ofReal_of_nonpos hc.le
  rw [hc0] at hvar
  have hzero : ∀ s, khat s = 0 := fun s => by
    have h1 := eVariationOn.edist_le khat (Set.mem_univ s) (Set.mem_univ (u - 1))
    have h2 : khat (u - 1) = 0 := by
      by_contra h
      have := (hsupp _ h).1
      linarith
    have h3 : edist (khat s) (khat (u - 1)) = 0 := le_antisymm (h1.trans hvar) zero_le
    rw [h2, edist_zero_right] at h3
    exact enorm_eq_zero.1 h3
  have hsum : ∀ x : ℤ, (fun lam => dilSum khat 1 f x lam) = (0 : ℝ → ℂ) := fun x => by
    funext lam
    simp [dilSum, hzero]
  simp_rw [hsum, rVariationOn_zero (by linarith : 0 < r)]
  simp

/-- **`l:varcarZ`** (conditional on `hO : OplusVariationBound`; L1771-L1776): for `r > 2` there is
`C ≥ 0` such that for every measurable `k̂` vanishing off an interval `[u, u + 1/10]` with total
variation `≤ c₀`, every finitely supported `f` and every `T ⊆ [0, 1)` (finite or not),
`‖V^r(∑_n f(x - n) e(λ n) k(n) : λ ∈ T)‖_{ℓ²} ≤ C c₀ ‖f‖_{ℓ²}`, `k(n) = ∫ k̂(ξ) e(nξ) dξ`.
The constant depends on `r` only.

Source: main paper `l:varcarZ`, L1771–L1776. -/
theorem varcarZ_of_oplus (hO : OplusVariationBound) {r : ℝ} (hr : 2 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (khat : ℝ → ℂ) (c₀ u : ℝ), Measurable khat →
      (∀ ξ, khat ξ ≠ 0 → ξ ∈ Set.Icc u (u + 1 / 10)) →
      eVariationOn khat Set.univ ≤ ENNReal.ofReal c₀ →
      ∀ (f : ℤ →₀ ℂ) (T : Set ℝ), T ⊆ Set.Ico 0 1 →
        (∑' x : ℤ, rVariationOn r T (fun lam => dilSum khat 1 f x lam) ^ 2) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (C * c₀) * (∑' x : ℤ, ‖f x‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := chart_variation hO hr (two_gt_conj hr)
  refine ⟨2 * C, by positivity, fun khat c₀ u hk hsupp hvar f T hT => ?_⟩
  by_cases hc₀ : 0 ≤ c₀
  · have hint := integrable_of_window hk hc₀ hsupp hvar
    have hs : ∀ s, s ∉ Set.Icc u (u + 1 / 10) → khat s = 0 := fun s hs => by
      by_contra h
      exact hs (hsupp s h)
    -- the folded multiplier `h = k̂ + k̂(· + 1)`
    have hsh : ∀ s, s ∉ Set.Icc (u - 1) (u + 1 / 10) →
        (fun s => khat s + khat (s + 1)) s = 0 := fun s hs' => by
      have h1 : khat s = 0 := hs s fun hmem => hs' ⟨by linarith [hmem.1], hmem.2⟩
      have h2 : khat (s + 1) = 0 := hs (s + 1) fun hmem =>
        hs' ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
      simp [h1, h2]
    have hvar2 : eVariationOn (fun s => khat s + khat (s + 1)) Set.univ ≤
        ENNReal.ofReal (2 * c₀) := by
      refine (eVariationOn_add_shift_le khat).trans ?_
      rw [ENNReal.ofReal_mul zero_le_two]
      gcongr
      simp
    have h := hC u (fun s => khat s + khat (s + 1)) (u - 1) (u + 1 / 10) hsh (2 * c₀)
      (by positivity) hvar2 f T
    have hchart : ∀ s, khat s ≠ 0 → s ∈ chartSet u := fun s hne => by
      have := hsupp s hne
      simp only [chartSet, Set.mem_Ioc]
      constructor <;> linarith [this.1, this.2]
    have hcongr : ∀ x : ℤ, rVariationOn r T (fun lam => dilSum khat 1 f x lam) =
        rVariationOn r T (chartMult u (fun s => khat s + khat (s + 1)) f x) := fun x =>
      rVariationOn_congr fun lam hlam =>
        dilSum_one_eq_chartMult hint hchart f x (hT hlam).1 (hT hlam).2.le
    have hfun : (fun x : ℤ => rVariationOn r T (fun lam => dilSum khat 1 f x lam)) =
        fun x => rVariationOn r T (chartMult u (fun s => khat s + khat (s + 1)) f x) :=
      funext hcongr
    rw [← eLpNorm_two_eq_tsum_sq, hfun, ← eLpNorm_two_eq_tsum_sq']
    refine h.trans (le_of_eq ?_)
    rw [show 2 * C * c₀ = C * (2 * c₀) by ring]
  · exact (zero_case_of_variation hr hsupp hvar (not_le.1 hc₀) f T).le.trans zero_le

end PrimeCarleson.Proof.Paper

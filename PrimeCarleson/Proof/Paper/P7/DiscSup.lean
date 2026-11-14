module

public import PrimeCarleson.Proof.Paper.P7.Disc
public import PrimeCarleson.Proof.Paper.Defs.Basic

/-!
# The single-frequency and maximal bounds for the modulated sums

The paper never supplies an `ℓ^s` bound for the modulated sum at one fixed frequency `λ`, although
the application of `c:disc` in `l:red-var-l2` (L1694–L1706), the crude bound for `C^Q` (L1729–L1731)
and the endpoint terms of the `λ`-range splitting of `p:disc` (L2964) need it (`c:disc` bounds only
the variation).

**Resolution, from the variation bound itself.** For a bounded-variation multiplier supported in the
chart the folded multiplier `h = K̂ + K̂(· + 1)` vanishes on the chart after the shift by `λ₀ = 3`:
the chart multiplier output at `λ₀ = 3` is `0`. Hence for `λ ∈ S ⊆ [0, 1)` the two-point chain
`(λ, 3)` gives `|∑_n f(x - n) e(λ n) K(n)| = |a_λ - a_3| ≤ V^r(a : S ∪ {3})`, and the variation
bound of `chart_variation` for the set `S ∪ {3}` gives

`‖ sup_{λ ∈ S} |∑_n f(x - Qn) e(λ n) K(n)| ‖_{ℓ^p} ≤ C_{p,r} c₀ ‖f‖_{ℓ^p}`

(`sup_modulated_of_oplus`), uniformly in `Q`; in particular, for `S = {λ}`, the `ℓ^p` boundedness of
each single modulated convolution `f ↦ ∑_n f(x - Qn) e(λ n) K(n)`. No input beyond
`OplusVariationBound` is needed (conditional theorems).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.MswTransference
  PrimeCarleson.Proof.Goal0

/-- The chart multiplier output at the frequency `3` vanishes for the folded multiplier
`h = K̂ + K̂(· + 1)`, which vanishes off `[-3/2, 1/2]`. -/
theorem chartMult_three {h : ℝ → ℂ} (hh : ∀ s, s ∉ Set.Icc (-3 / 2 : ℝ) (1 / 2) → h s = 0)
    (f : ℤ →₀ ℂ) (x : ℤ) : chartMult 0 h f x 3 = 0 := by
  unfold chartMult mulInt
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun β => ?_)
  by_cases hβ : β ∈ chartSet 0
  · have hβ' : β - 3 ∉ Set.Icc (-3 / 2 : ℝ) (1 / 2) := by
      intro hmem
      have := hβ
      simp only [chartSet, Set.mem_Ioc] at this
      linarith [hmem.1, this.1]
    simp [hh _ hβ']
  · simp [chartDensity, Set.indicator_of_notMem hβ]

/-- **The maximal bound for the modulated sums** (`Q = 1`; conditional on `hO`): for `r > 2`,
`r' < p < ∞` there is `C ≥ 0` such that for every measurable `K̂` supported in `(-1/2, 1/2]` of
variation `≤ c₀`, every finitely supported `f` and every `S ⊆ [0, 1)`,
`‖sup_{λ ∈ S} |∑_n f(x - n) e(λ n) K(n)|‖_{ℓ^p} ≤ C c₀ ‖f‖_{ℓ^p}`. -/
theorem sup_modulated_one (hO : OplusVariationBound) {r p : ℝ} (hr : 2 < r)
    (hp : r / (r - 1) < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (khat : ℝ → ℂ) (c₀ : ℝ), 0 ≤ c₀ → Measurable khat →
      (∀ ξ, khat ξ ≠ 0 → ξ ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2)) →
      eVariationOn khat Set.univ ≤ ENNReal.ofReal c₀ →
      ∀ (f : ℤ →₀ ℂ) (S : Set ℝ), S ⊆ Set.Ico 0 1 →
        eLpNorm (fun x : ℤ => ⨆ lam ∈ S, ‖dilSum khat 1 f x lam‖ₑ)
            (ENNReal.ofReal p) Measure.count ≤
          ENNReal.ofReal (C * c₀) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨C, hC0, hC⟩ := chart_variation hO hr hp
  refine ⟨2 * C, by positivity, fun khat c₀ hc₀ hk hsupp hvar f S hS => ?_⟩
  have hs : ∀ s, s ∉ Set.Icc (-1 / 2 : ℝ) (1 / 2) → khat s = 0 := fun s hs => by
    by_contra h
    exact hs (Set.Ioc_subset_Icc_self (hsupp s h))
  have hint : Integrable khat :=
    integrable_of_bound_support hk (norm_le_of_eVariationOn hs hc₀ hvar) hs
  have hsh : ∀ s, s ∉ Set.Icc (-3 / 2 : ℝ) (1 / 2) →
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
  have hp0 : 0 < p := by linarith [one_le_of_gt_conj hr hp]
  have h := hC 0 (fun s => khat s + khat (s + 1)) (-3 / 2) (1 / 2) hsh (2 * c₀) (by positivity)
    hvar2 f (S ∪ {3})
  have hpt : ∀ x : ℤ, (⨆ lam ∈ S, ‖dilSum khat 1 f x lam‖ₑ) ≤
      rVariationOn r (S ∪ {3}) (chartMult 0 (fun s => khat s + khat (s + 1)) f x) := by
    intro x
    refine iSup₂_le fun lam hlam => ?_
    have h1 : dilSum khat 1 f x lam = chartMult 0 (fun s => khat s + khat (s + 1)) f x lam :=
      dilSum_one_eq_chartMult hint (subset_chartSet_zero hsupp) f x (hS hlam).1 (hS hlam).2.le
    have h3 := chartMult_three hsh f x
    have := enorm_sub_le_rVariationOn (by linarith : 0 < r)
      (a := chartMult 0 (fun s => khat s + khat (s + 1)) f x) (S := S ∪ {3})
      (Or.inl hlam) (Or.inr rfl)
    rw [h3, sub_zero, ← h1] at this
    exact this
  calc eLpNorm (fun x : ℤ => ⨆ lam ∈ S, ‖dilSum khat 1 f x lam‖ₑ) (ENNReal.ofReal p)
        Measure.count
      ≤ eLpNorm (fun x : ℤ => rVariationOn r (S ∪ {3})
          (chartMult 0 (fun s => khat s + khat (s + 1)) f x)) (ENNReal.ofReal p)
          Measure.count := eLpNorm_count_mono_enn hpt _
    _ ≤ _ := h
    _ = _ := by rw [show C * (2 * c₀) = 2 * C * c₀ by ring]

/-- **The maximal bound for the dilated modulated sums** (conditional on `hO`): the same with the
constant independent of `Q ≥ 1`. -/
theorem sup_modulated_of_oplus (hO : OplusVariationBound) {r p : ℝ} (hr : 2 < r)
    (hp : r / (r - 1) < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (khat : ℝ → ℂ) (c₀ : ℝ), 0 ≤ c₀ → Measurable khat →
      (∀ ξ, khat ξ ≠ 0 → ξ ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2)) →
      eVariationOn khat Set.univ ≤ ENNReal.ofReal c₀ →
      ∀ (Q : ℕ), 1 ≤ Q → ∀ (f : ℤ →₀ ℂ) (S : Set ℝ), S ⊆ Set.Ico 0 1 →
        eLpNorm (fun x : ℤ => ⨆ lam ∈ S, ‖dilSum khat (Q : ℤ) f x lam‖ₑ)
            (ENNReal.ofReal p) Measure.count ≤
          ENNReal.ofReal (C * c₀) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨C, hC0, hC⟩ := sup_modulated_one hO hr hp
  have hp0 : 0 < p := by linarith [one_le_of_gt_conj hr hp]
  refine ⟨C, hC0, fun khat c₀ hc₀ hk hsupp hvar Q hQ f S hS => ?_⟩
  refine eLpNorm_count_dilation hp0 hQ _ f _
    (fun a y => ⨆ lam ∈ S, ‖dilSum khat 1 (residueSeq Q hQ (a : ℕ) f) y lam‖ₑ)
    (fun a y => ?_) (fun a => hC khat c₀ hc₀ hk hsupp hvar _ S hS)
  refine iSup_congr fun lam => iSup_congr fun _ => ?_
  rw [dilSum_residue hQ khat f (a : ℕ) y lam]

end PrimeCarleson.Proof.Paper

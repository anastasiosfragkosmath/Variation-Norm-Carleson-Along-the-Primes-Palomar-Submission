module

public import Carleson.ToMathlib.HardyLittlewood

/-!
# The Hardy–Littlewood maximal function on `ℝ`

The uncentered Hardy–Littlewood maximal function of [O+] (L2396, L2420, L2477, L2546, L2654; the
paper writes `M[f](x)` for the supremum over the intervals containing `x` of the average of `|f|`
and defines it nowhere), and its weak type `(1, 1)` and strong type `(p, p)` bounds on `ℝ` with
Lebesgue measure, a standard result.  [O+] uses the weak type `(1, 1)` bound for `1_F` (L2654),
the weak type `(1, 1)` bound in the proof of `tileslargemaxprop` (L2546) and the `L²` bound in the
proof of `treeestimatelargeintervals` (L2420).  The dyadic maximal function `M_D` is used only
through `M_D[1_F] ≤ M[1_F]` (L2664, in the use of `tilessmallmaxprop`): `maximalDyadicR` defines
it, and `laverage_le_maximalHLR` bounds the average over any interval, in particular over any
dyadic interval, by `M`, which gives the pointwise comparison.

The proof specializes the Hardy–Littlewood theorem on doubling metric measure spaces of the
vendored Lean Carleson project (`hasWeakType_maximalFunction_one`,
`hasStrongType_maximalFunction_one`, `Carleson.ToMathlib.HardyLittlewood`) to `ℝ`: the balls of `ℝ`
are the open bounded intervals, the vendored maximal function `globalMaximalFunction volume 1` is
the supremum over the open intervals containing `x`, and it agrees with the supremum over the
closed intervals containing `x` (`maximalHLR_eq_globalMaximalFunction`), so no constant is lost.

* `maximalHLR f x = ⨆ a < b, x ∈ [a, b], ⨍_{[a, b]} ‖f‖ₑ`;
* `laverage_le_maximalHLR`: the average over any interval `I` (open, closed or half-open, e.g. a
  dyadic interval) containing `x` is at most `maximalHLR f x`;
* `measurable_maximalHLR`, `maximalHLR_eq_globalMaximalFunction`;
* `mul_volume_maximalHLR_le`: weak type `(1, 1)`, `t · |{M f > t}| ≤ 4 ‖f‖_{L¹}` for all `t`
  (`volume_maximalHLR_gt_le`, `wnorm_maximalHLR_le`, and for `1_F`:
  `volume_maximalHLR_indicator_gt_le`, `volume_maximalHLR_indicator_gt_sixteen_le`, the set `G` of
  L2654 with `C'' = 16`);
* `eLpNorm_maximalHLR_le`: `‖M f‖_{L^p} ≤ C_p ‖f‖_{L^p}` for `1 < p ≤ ∞`, with
  `C_p = maximalHLRConst p` (`= 1` for `p = ∞`, `= 2 (4 p / (p - 1))^{1/p}` for `p < ∞`,
  `maximalHLRConst_of_ne_top`).

The bounds hold for every `f : ℝ → E` (for `f` that is not `L^p` the right-hand side is `∞`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped NNReal ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Common

/-- The uncentered Hardy–Littlewood maximal function on `ℝ`: the supremum, over all closed
intervals `[a, b]` (`a < b`) containing `x`, of the average `|[a, b]|⁻¹ ∫_{[a, b]} ‖f‖ₑ`. -/
def maximalHLR {E : Type*} [ENorm E] (f : ℝ → E) (x : ℝ) : ℝ≥0∞ :=
  ⨆ (a : ℝ) (b : ℝ) (_ : a < b) (_ : x ∈ Icc a b), ⨍⁻ y in Icc a b, ‖f y‖ₑ ∂volume

/-- Lebesgue measure on `ℝ` is doubling with constant `2`. -/
theorem isDoubling_volume_real : (volume : Measure ℝ).IsDoubling 2 where
  measure_ball_two_le_same x r := by
    rw [Real.volume_ball, Real.volume_ball]
    rcases le_or_gt r 0 with hr | hr
    · rw [ENNReal.ofReal_of_nonpos (by linarith : 2 * (2 * r) ≤ 0)]
      exact zero_le
    · rw [show 2 * (2 * r) = 2 * (2 * r) from rfl, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      simp

/-- The balls of `ℝ` are the open intervals: `ball z r = Ioo (z - r) (z + r)`; the average over an
open interval is the average over the corresponding closed one. -/
theorem laverage_Ioo_eq_laverage_Icc {a b : ℝ} (g : ℝ → ℝ≥0∞) :
    ⨍⁻ y in Ioo a b, g y ∂volume = ⨍⁻ y in Icc a b, g y ∂volume :=
  setLAverage_congr Ioo_ae_eq_Icc

/-- The closed-interval maximal function is the vendored ball maximal function
`globalMaximalFunction volume 1`: the balls of `ℝ` are the open intervals, and an average over the
closed interval `[a, b] ∋ x` is a limit of averages over the open intervals `(a - ε, b + ε) ∋ x`. -/
theorem maximalHLR_eq_globalMaximalFunction {E : Type*} [ENorm E] (f : ℝ → E) :
    maximalHLR f = globalMaximalFunction (volume : Measure ℝ) 1 (fun y => ‖f y‖ₑ) := by
  funext x
  refine le_antisymm ?_ ?_
  · -- closed intervals: approximate by open intervals `(a - ε, b + ε)`
    refine iSup₂_le fun a b => iSup_le fun hab => iSup_le fun hx => ?_
    set g : ℝ → ℝ≥0∞ := fun y => ‖f y‖ₑ with hg
    set G := globalMaximalFunction (volume : Measure ℝ) 1 g x with hG
    set L := b - a with hL
    have hL0 : 0 < L := sub_pos.2 hab
    have hxab := hx
    rw [setLAverage_eq, Real.volume_Icc, ← hL]
    -- for every `ε > 0` the open interval `(a - ε, b + ε)` is a ball containing `x`
    have key : ∀ ε : ℝ, 0 < ε →
        (∫⁻ y in Icc a b, g y) / ENNReal.ofReal (L + 2 * ε) ≤ G := by
      intro ε hε
      set z := (a + b) / 2 with hz
      set r := L / 2 + ε with hr
      have hball : ball z r = Ioo (a - ε) (b + ε) := by
        rw [Real.ball_eq_Ioo]
        congr 1 <;> (rw [hz, hr, hL]; ring)
      have hdist : dist x z < r := by
        rw [Real.dist_eq, abs_lt, hz, hr, hL]
        constructor <;> linarith [hxab.1, hxab.2]
      have h1 : ⨍⁻ y in ball z r, ‖g y‖ₑ ∂(volume : Measure ℝ) ≤ G :=
        laverage_le_globalMaximalFunction hdist
      refine le_trans ?_ h1
      rw [setLAverage_eq, hball, Real.volume_Ioo]
      have : b + ε - (a - ε) = L + 2 * ε := by rw [hL]; ring
      rw [this]
      have hint : ∫⁻ y in Icc a b, g y ∂volume ≤ ∫⁻ y in Ioo (a - ε) (b + ε), ‖g y‖ₑ ∂volume := by
        simp only [enorm_eq_self]
        exact lintegral_mono_set (Icc_subset_Ioo (by linarith) (by linarith))
      exact ENNReal.div_le_div_right hint _
    -- let `ε → 0`
    have hlim : Tendsto (fun ε : ℝ => (∫⁻ y in Icc a b, g y) *
        (ENNReal.ofReal (L + 2 * ε))⁻¹) (𝓝[>] 0)
        (𝓝 ((∫⁻ y in Icc a b, g y) * (ENNReal.ofReal L)⁻¹)) := by
      refine ENNReal.Tendsto.const_mul ?_ (Or.inl ?_)
      · have hc : Continuous fun ε : ℝ => ENNReal.ofReal (L + 2 * ε) :=
          ENNReal.continuous_ofReal.comp (by fun_prop)
        have hc' : Tendsto (fun ε : ℝ => ENNReal.ofReal (L + 2 * ε)) (𝓝[>] 0)
            (𝓝 (ENNReal.ofReal L)) := by
          simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
        exact tendsto_inv_iff.2 hc'
      · simp
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        (∫⁻ y in Icc a b, g y) * (ENNReal.ofReal (L + 2 * ε))⁻¹ ≤ G := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [← div_eq_mul_inv]
      exact key ε hε
    have := le_of_tendsto hlim hev
    rwa [← div_eq_mul_inv] at this
  · -- balls are intervals
    refine iSup₂_le fun i _ => ?_
    by_cases hx : x ∈ ball i.1 i.2
    · rw [indicator_of_mem hx]
      simp only [ENNReal.rpow_one, inv_one]
      rw [Real.ball_eq_Ioo] at hx ⊢
      rw [laverage_Ioo_eq_laverage_Icc]
      refine le_iSup₂_of_le (i.1 - i.2) (i.1 + i.2) <| le_iSup₂_of_le ?_ ?_ le_rfl
      · linarith [hx.1, hx.2]
      · exact Ioo_subset_Icc_self hx
    · rw [indicator_of_notMem hx]
      exact zero_le

/-- The average over any interval `I` with `(a, b) ⊆ I ⊆ [a, b]`, `a < b`, containing `x` is at
most `maximalHLR f x`: this covers open, closed and half-open (e.g. dyadic) intervals. -/
theorem laverage_le_maximalHLR {E : Type*} [ENorm E] (f : ℝ → E) {a b x : ℝ} {I : Set ℝ}
    (hab : a < b) (h1 : Ioo a b ⊆ I) (h2 : I ⊆ Icc a b) (hx : x ∈ I) :
    ⨍⁻ y in I, ‖f y‖ₑ ∂volume ≤ maximalHLR f x := by
  have hI : I =ᵐ[(volume : Measure ℝ)] Icc a b := by
    have h3 := ae_eq_set.1 (Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := a) (b := b))
    rw [ae_eq_set]
    refine ⟨?_, measure_mono_null (sdiff_subset_sdiff_right h1) h3.2⟩
    rw [sdiff_eq_empty.2 h2]
    simp
  rw [setLAverage_congr hI]
  exact le_iSup₂_of_le a b <| le_iSup₂_of_le hab (h2 hx) le_rfl

/-- The maximal function is lower semicontinuous. -/
theorem lowerSemicontinuous_maximalHLR {E : Type*} [ENorm E] (f : ℝ → E) :
    LowerSemicontinuous (maximalHLR f) := by
  rw [maximalHLR_eq_globalMaximalFunction]
  exact lowerSemiContinuous_maximalFunction

/-- The maximal function is measurable. -/
theorem measurable_maximalHLR {E : Type*} [ENorm E] (f : ℝ → E) : Measurable (maximalHLR f) :=
  (lowerSemicontinuous_maximalHLR f).measurable

/-- **Weak type `(1, 1)` of the Hardy–Littlewood maximal function on `ℝ`**:
`‖M f‖_{L^{1,∞}} ≤ 4 ‖f‖_{L¹}`
(the vendored weak type `(1, 1)` bound has constant `A² = 4` for the doubling constant `A = 2`). -/
theorem wnorm_maximalHLR_le {E : Type*} [TopologicalSpace E] [ContinuousENorm E] (f : ℝ → E) :
    wnorm (maximalHLR f) 1 volume ≤ 4 * eLpNorm f 1 volume := by
  have := isDoubling_volume_real
  by_cases hfp : MemLp f 1 volume
  · have hu : MemLp (fun y => ‖f y‖ₑ) 1 volume := by
      rw [MemLp, eLpNorm_enorm f hfp.aestronglyMeasurable]
      exact hfp
    have key := (hasWeakType_maximalFunction_one (μ := (volume : Measure ℝ)) (A := 2)
      (𝓑 := univ) (c := Prod.fst) (r := Prod.snd) (ε := ℝ≥0∞) _ hu).2
    rw [eLpNorm_enorm f hfp.aestronglyMeasurable] at key
    rw [maximalHLR_eq_globalMaximalFunction]
    refine key.trans (le_of_eq ?_)
    norm_num
  · rw [not_lt_top_iff.1 hfp, ENNReal.mul_top (by norm_num)]
    exact le_top

/-- **Weak type `(1, 1)` of the Hardy–Littlewood maximal function on `ℝ`**, distribution form:
`t · |{x : M f (x) > t}| ≤ 4 ‖f‖_{L¹}` for every `t` (the paper uses `|{M[1_F] > C'' |F|}| ≤ 1/4`
(L2654) and `|Ω_λ| ≲ |F| / λ` for `Ω_λ = {M[1_F] > λ}` (L2546)). -/
theorem mul_volume_maximalHLR_le {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    (f : ℝ → E) (t : ℝ≥0∞) :
    t * volume {x | t < maximalHLR f x} ≤ 4 * eLpNorm f 1 volume := by
  rcases eq_or_ne t ⊤ with rfl | ht
  · simp
  lift t to ℝ≥0 using ht
  refine le_trans ?_ (wnorm_maximalHLR_le f)
  rw [wnorm_one (measurable_maximalHLR f).aestronglyMeasurable]
  exact le_iSup (fun s : ℝ≥0 => (s : ℝ≥0∞) * distribution (maximalHLR f) s volume) t

/-- Weak type `(1, 1)`, measure form: `|{M f > t}| ≤ 4 ‖f‖_{L¹} / t` for `0 < t`. -/
theorem volume_maximalHLR_gt_le {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    (f : ℝ → E) {t : ℝ≥0∞} (ht : t ≠ 0) :
    volume {x | t < maximalHLR f x} ≤ 4 * eLpNorm f 1 volume / t := by
  rcases eq_or_ne t ⊤ with rfl | htt
  · simp
  rw [ENNReal.le_div_iff_mul_le (Or.inl ht) (Or.inl htt), mul_comm]
  exact mul_volume_maximalHLR_le f t

/-- The maximal dyadic average operator `M_D` of the paper (L2458, L2664; the paper does not define
it): `M_D f(x) = sup_{I ∋ x} |I|⁻¹ ∫_I ‖f‖ₑ` over the dyadic intervals `I = [k 2^j, (k + 1) 2^j)`,
`j, k ∈ ℤ`, containing `x`. -/
def maximalDyadicR {E : Type*} [ENorm E] (f : ℝ → E) (x : ℝ) : ℝ≥0∞ :=
  ⨆ (j : ℤ) (k : ℤ) (_ : x ∈ Ico ((k : ℝ) * 2 ^ j) (((k : ℝ) + 1) * 2 ^ j)),
    ⨍⁻ y in Ico ((k : ℝ) * 2 ^ j) (((k : ℝ) + 1) * 2 ^ j), ‖f y‖ₑ ∂volume

/-- Weak type `(1, 1)` for the indicator of a measurable set `F` (the form used at L2546 and
L2654 of `osttw0710.tex`): `|{M[1_F] > t}| ≤ 4 |F| / t` for `0 < t`. -/
theorem volume_maximalHLR_indicator_gt_le {F : Set ℝ} (hF : MeasurableSet F) {t : ℝ≥0∞}
    (ht : t ≠ 0) :
    volume {x | t < maximalHLR (F.indicator (fun _ => (1 : ℝ))) x} ≤ 4 * volume F / t := by
  have h1 : eLpNorm (F.indicator (fun _ => (1 : ℝ))) 1 volume = volume F := by
    rw [eLpNorm_indicator_const hF.nullMeasurableSet one_ne_zero ENNReal.one_ne_top]
    simp
  have := volume_maximalHLR_gt_le (F.indicator (fun _ => (1 : ℝ))) ht
  rwa [h1] at this

/-- **The set `G` of L2654 of `osttw0710.tex`**: for a measurable `F` of finite positive measure,
`|{x : M[1_F](x) > 16 |F|}| ≤ 1/4`, so `C'' = 16` is an absolute constant with `|G| ≤ 1/4`. -/
theorem volume_maximalHLR_indicator_gt_sixteen_le {F : Set ℝ} (hF : MeasurableSet F)
    (hF0 : volume F ≠ 0) (hFt : volume F ≠ ⊤) :
    volume {x | 16 * volume F < maximalHLR (F.indicator (fun _ => (1 : ℝ))) x} ≤ 1 / 4 := by
  have h16 : (16 : ℝ≥0∞) * volume F ≠ 0 := mul_ne_zero (by norm_num) hF0
  refine (volume_maximalHLR_indicator_gt_le hF h16).trans ?_
  have h4 : (4 : ℝ≥0∞)⁻¹ * 16 = 4 := by
    rw [show (16 : ℝ≥0∞) = 4 * 4 by norm_num, ← mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  rw [ENNReal.div_le_iff h16 (by finiteness), one_div, ← mul_assoc, h4]

/-- The constant of the Hardy–Littlewood maximal theorem on `L^p(ℝ)`: `1` for `p = ∞` and
`CMB 2 p` (the constant of the vendored theorem for doubling constant `2`) for `p < ∞`. -/
def maximalHLRConst (p : ℝ≥0∞) : ℝ≥0 :=
  if p = ⊤ then 1 else CMB 2 p.toNNReal

/-- For `1 < p < ∞` the constant is `2 (4 p / (p - 1))^{1/p}`. -/
theorem maximalHLRConst_of_ne_top {p : ℝ≥0∞} (hp : 1 < p) (hpt : p ≠ ⊤) :
    maximalHLRConst p = 2 * (p.toNNReal / (p.toNNReal - 1) * 2 ^ 2) ^ (p.toNNReal : ℝ)⁻¹ := by
  have hp' : 1 < p.toNNReal := by
    have := ENNReal.toNNReal_lt_toNNReal ENNReal.one_ne_top hpt |>.2 hp
    simpa using this
  simp only [maximalHLRConst, hpt, ↓reduceIte]
  exact CMB_eq_of_one_lt_q hp'

/-- The constant `maximalHLRConst p` is positive for `1 < p`. -/
theorem maximalHLRConst_pos {p : ℝ≥0∞} (hp : 1 < p) : 0 < maximalHLRConst p := by
  rcases eq_or_ne p ⊤ with rfl | hpt
  · simp [maximalHLRConst]
  · rw [maximalHLRConst_of_ne_top hp hpt]
    have hp' : 1 < p.toNNReal := by
      have := ENNReal.toNNReal_lt_toNNReal ENNReal.one_ne_top hpt |>.2 hp
      simpa using this
    exact mul_pos two_pos (NNReal.rpow_pos (mul_pos (div_pos (zero_lt_one.trans hp')
      (tsub_pos_of_lt hp')) (by norm_num)))

/-- **Hardy–Littlewood maximal theorem on `ℝ`** (the paper uses `p = 2`, L2420): for `1 < p ≤ ∞` and
every `f : ℝ → E`, `‖M f‖_{L^p} ≤ C_p ‖f‖_{L^p}` with `C_p = maximalHLRConst p`. -/
theorem eLpNorm_maximalHLR_le {E : Type*} [TopologicalSpace E] [ContinuousENorm E] {p : ℝ≥0∞}
    (hp : 1 < p) (f : ℝ → E) :
    eLpNorm (maximalHLR f) p volume ≤ maximalHLRConst p * eLpNorm f p volume := by
  by_cases hfp : MemLp f p volume
  · have hu : MemLp (fun y => ‖f y‖ₑ) p volume := by
      rw [MemLp, eLpNorm_enorm f hfp.aestronglyMeasurable]
      exact hfp
    have hmeas : AEStronglyMeasurable (maximalHLR f) volume :=
      (measurable_maximalHLR f).aestronglyMeasurable
    rcases eq_or_ne p ⊤ with rfl | hpt
    · simp only [maximalHLRConst, ↓reduceIte, ENNReal.coe_one, one_mul]
      rw [eLpNorm_exponent_top hmeas, eLpNorm_exponent_top hfp.aestronglyMeasurable]
      refine essSup_le_of_ae_le _ (Filter.Eventually.of_forall fun x => ?_)
      change ‖maximalHLR f x‖ₑ ≤ eLpNormEssSup f volume
      rw [enorm_eq_self, maximalHLR_eq_globalMaximalFunction]
      exact maximalFunction_one_le_eLpNormEssSup (μ := (volume : Measure ℝ))
        (𝓑 := (univ : Set (ℝ × ℝ))) (c := Prod.fst) (r := Prod.snd)
        (u := fun y => ‖f y‖ₑ) (x := x)
    · lift p to ℝ≥0 using hpt
      have hp' : 1 < p := by exact_mod_cast hp
      have := isDoubling_volume_real
      have key := (hasStrongType_maximalFunction_one (μ := (volume : Measure ℝ)) (A := 2)
        (𝓑 := univ) (c := Prod.fst) (r := Prod.snd) (ε' := ℝ≥0∞) hp' _ hu).2
      rw [eLpNorm_enorm f hfp.aestronglyMeasurable] at key
      rw [maximalHLR_eq_globalMaximalFunction]
      have hC : maximalHLRConst (p : ℝ≥0∞) = CMB 2 p := by simp [maximalHLRConst]
      rw [hC]
      exact key
  · rw [not_lt_top_iff.1 hfp, ENNReal.mul_top (by simpa using (maximalHLRConst_pos hp).ne')]
    exact le_top

end PrimeCarleson.Proof.Common

module

public import PrimeCarleson.Proof.Oplus.Theorem.Cutoff
public import PrimeCarleson.Proof.Oplus.Theorem.Basic

/-!
# The Fourier cutoff of [O+] `linearizedtheorem` (L921-L926)

For a finite set `Ξ ⊆ ℝ` and `ε > 0` let `χ_ε = θ(ε ·) - ∑_{ξ ∈ Ξ} θ((· - ξ)/ε)` (`cutMult`), with
`θ` the bump of `Bump.lean`. For `ε` small (`CutSmall`: the bumps `θ((· - ξ)/ε)` have disjoint
supports inside `{θ(ε ·) = 1}`) `χ_ε` vanishes near every `ξ ∈ Ξ`, has compact support, and
`χ_ε → 1` off `Ξ` as `ε → 0`. For a Schwartz function `f`, `f_ε = cutOp χ_ε f = f ⋆ 𝓕⁻χ_ε` is
Schwartz with `𝓕 f_ε = 𝓕 f · χ_ε`, hence with Fourier transform compactly supported in `ℝ ∖ Ξ`.

`exists_fourier_cutoff_seq`: there is a sequence of Schwartz functions `g_n` (`g_n = f_{ε_n}`) with
Fourier transform compactly supported in `ℝ ∖ Ξ`, `‖f̂ - ĝ_n‖_{L¹} → 0` (dominated convergence) and
`‖g_n - f‖_{L^p} → 0` for every `p > 1`. The `L^p` convergence: `‖g_n - f‖_{L^∞} ≤ ‖f̂ - ĝ_n‖_{L¹}
→ 0` by Fourier inversion, `‖g_n - f‖_{L¹} ≤ ‖f‖_{L¹}(1 + (1 + |Ξ|)‖𝓕⁻θ‖_{L¹})` stays bounded (the
`L¹` norm of the kernel `𝓕⁻χ_ε` is independent of `ε`, `Bump.lean`), and
`‖g‖_p^p ≤ ‖g‖_∞^{p-1}‖g‖_1`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap ENNReal
open FourierTransform

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

/-- The Fourier multiplier `χ_ε = θ(ε ·) - ∑_{ξ∈Ξ} θ((· - ξ)/ε)`. -/
def cutMult (Ξ : Finset ℝ) (ε : ℝ) : 𝓢(ℝ, ℂ) := bumpS 0 (1 / ε) - ∑ ξ ∈ Ξ, bumpS ξ ε

/-- The multiplier as a combination of bumps. -/
theorem cutMult_apply (Ξ : Finset ℝ) {ε : ℝ} (hε : 0 < ε) (η : ℝ) :
    cutMult Ξ ε η = bumpFn 0 (1 / ε) η - ∑ ξ ∈ Ξ, bumpFn ξ ε η := by
  simp only [cutMult, sub_apply, sum_apply, bumpS_apply _ (one_div_pos.2 hε),
    bumpS_apply _ hε]

/-- The multiplier `χ_ε` has compact support. -/
theorem hasCompactSupport_cutMult (Ξ : Finset ℝ) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (⇑(cutMult Ξ ε)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ)
    (2 * (1 / ε) + ∑ ξ ∈ Ξ, (|ξ| + 2 * ε))) fun η hη => ?_
  have hη' : 2 * (1 / ε) + ∑ ξ ∈ Ξ, (|ξ| + 2 * ε) < |η| := by
    simpa [Metric.mem_closedBall, Real.dist_eq] using hη
  have hsum : 0 ≤ ∑ ξ ∈ Ξ, (|ξ| + 2 * ε) :=
    Finset.sum_nonneg fun ξ _ => by positivity
  rw [cutMult_apply Ξ hε, bumpFn_eq_zero (one_div_pos.2 hε) (by rw [sub_zero]; linarith), zero_sub,
    neg_eq_zero]
  refine Finset.sum_eq_zero fun ξ hξ => bumpFn_eq_zero hε ?_
  have h1 : |ξ| + 2 * ε ≤ ∑ ξ ∈ Ξ, (|ξ| + 2 * ε) :=
    Finset.single_le_sum (f := fun ξ => |ξ| + 2 * ε) (fun ξ _ => by positivity) hξ
  have h2 : |η| ≤ |η - ξ| + |ξ| := by
    have := abs_sub_abs_le_abs_sub η ξ
    have := abs_add_le (η - ξ) ξ
    simpa using this
  have h3 : 0 ≤ 2 * (1 / ε) := by positivity
  linarith


/-- A continuous function vanishing at `0` tends to `0` as `ε → 0+`. -/
theorem tendsto_nhdsGT_zero_of_continuous {f : ℝ → ℝ} (hf : Continuous f) (h0 : f 0 = 0) :
    Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  (hf.tendsto' 0 0 h0).mono_left nhdsWithin_le_nhds

/-- `ε` is small compared with the finite set `Ξ`: the bumps `θ((· - ξ)/ε)` have disjoint
supports inside `{θ(ε ·) = 1}`. -/
def CutSmall (Ξ : Finset ℝ) (ε : ℝ) : Prop :=
  0 < ε ∧ (∀ ζ ∈ Ξ, ε * (|ζ| + ε) ≤ 1) ∧ ∀ ζ ∈ Ξ, ∀ ξ ∈ Ξ, ζ ≠ ξ → 3 * ε ≤ |ζ - ξ|

/-- The multiplier vanishes near each point of `Ξ` when `ε` is small. -/
theorem cutMult_eq_zero_of_small {Ξ : Finset ℝ} {ε : ℝ} (hε : CutSmall Ξ ε) {ζ : ℝ} (hζ : ζ ∈ Ξ)
    {η : ℝ} (hη : |η - ζ| < ε) : cutMult Ξ ε η = 0 := by
  obtain ⟨hε0, h1, h2⟩ := hε
  rw [cutMult_apply Ξ hε0]
  have hb0 : bumpFn 0 (1 / ε) η = 1 := by
    refine bumpFn_eq_one (one_div_pos.2 hε0) ?_
    rw [sub_zero]
    have h3 : |η| ≤ |ζ| + ε := by
      have := abs_add_le (η - ζ) ζ
      simp only [sub_add_cancel] at this
      linarith
    have h4 : ε * (|ζ| + ε) ≤ 1 := h1 ζ hζ
    rw [le_div_iff₀ hε0]
    nlinarith
  rw [hb0, Finset.sum_eq_single ζ]
  · rw [bumpFn_eq_one hε0 hη.le]; ring
  · intro ξ hξ hne
    refine bumpFn_eq_zero hε0 ?_
    have h5 := h2 ζ hζ ξ hξ (Ne.symm hne)
    have h6 : |ζ - ξ| ≤ |η - ξ| + |η - ζ| := by
      have := abs_sub_le ζ η ξ
      rw [abs_sub_comm ζ η] at this
      linarith
    linarith
  · intro h; exact absurd hζ h

/-- For `η ∉ Ξ` the multiplier is eventually `1` as `ε → 0+`. -/
theorem eventually_cutMult_eq_one (Ξ : Finset ℝ) {η : ℝ} (hη : η ∉ Ξ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), cutMult Ξ ε η = 1 := by
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), |η| ≤ ε⁻¹ :=
    tendsto_inv_nhdsGT_zero.eventually (eventually_ge_atTop |η|)
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ξ ∈ Ξ, 2 * ε ≤ |η - ξ| := by
    refine (Filter.eventually_all_finset Ξ).2 fun ξ hξ => ?_
    have hpos : 0 < |η - ξ| := abs_pos.2 (sub_ne_zero.2 fun h => hη (h ▸ hξ))
    have : Tendsto (fun ε : ℝ => 2 * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsGT_zero_of_continuous (by fun_prop) (by simp)
    exact (this.eventually (gt_mem_nhds hpos)).mono fun ε h => h.le
  filter_upwards [h1, h2, self_mem_nhdsWithin] with ε hε1 hε2 hε0
  have hε0' : 0 < ε := hε0
  rw [cutMult_apply Ξ hε0', bumpFn_eq_one (one_div_pos.2 hε0')]
  · rw [Finset.sum_eq_zero fun ξ hξ => bumpFn_eq_zero hε0' (hε2 ξ hξ)]; ring
  · rw [sub_zero, one_div]; exact hε1

/-- The set of small parameters `ε` is a neighbourhood of `0+`. -/
theorem eventually_cutSmall (Ξ : Finset ℝ) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), CutSmall Ξ ε := by
  have hlim : ∀ c : ℝ, Tendsto (fun ε : ℝ => c * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := fun c =>
    tendsto_nhdsGT_zero_of_continuous (by fun_prop) (by simp)
  have h0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  refine h0.and (Filter.Eventually.and ?_ ?_)
  · refine (Filter.eventually_all_finset Ξ).2 fun ζ _ => ?_
    have : Tendsto (fun ε : ℝ => ε * (|ζ| + ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsGT_zero_of_continuous (by fun_prop) (by simp)
    exact (this.eventually (gt_mem_nhds one_pos)).mono fun ε h => h.le
  · refine (Filter.eventually_all_finset Ξ).2 fun ζ _ => ?_
    refine (Filter.eventually_all_finset Ξ).2 fun ξ _ => ?_
    by_cases hne : ζ = ξ
    · exact Eventually.of_forall fun ε h => absurd hne h
    · have hpos : 0 < |ζ - ξ| := abs_pos.2 (sub_ne_zero.2 hne)
      exact ((hlim 3).eventually (gt_mem_nhds hpos)).mono fun ε h _ => h.le

/-- `|1 - χ_ε| ≤ 2 + |Ξ|`. -/
theorem norm_one_sub_cutMult_le (Ξ : Finset ℝ) {ε : ℝ} (hε : 0 < ε) (η : ℝ) :
    ‖1 - cutMult Ξ ε η‖ ≤ 2 + Ξ.card := by
  rw [cutMult_apply Ξ hε]
  have : (1 : ℂ) - (bumpFn 0 (1 / ε) η - ∑ ξ ∈ Ξ, bumpFn ξ ε η) =
      (1 - bumpFn 0 (1 / ε) η) + ∑ ξ ∈ Ξ, bumpFn ξ ε η := by ring
  rw [this]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sub_le _ _).trans ?_
    have := norm_bumpFn_le_one 0 (1 / ε) η
    simp only [norm_one]
    linarith
  · refine (norm_sum_le _ _).trans ?_
    calc ∑ ξ ∈ Ξ, ‖bumpFn ξ ε η‖ ≤ ∑ _ξ ∈ Ξ, (1 : ℝ) :=
          Finset.sum_le_sum fun ξ _ => norm_bumpFn_le_one ξ ε η
      _ = Ξ.card := by simp


/-- The `L¹` norm of the kernel `𝓕⁻(bumpS 0 1)` (the same for every position and scale). -/
def bumpKernelNorm : ℝ≥0∞ := ∫⁻ y, ‖(𝓕⁻ (bumpS 0 1) : 𝓢(ℝ, ℂ)) y‖ₑ

/-- The kernel `𝓕⁻θ` is integrable. -/
theorem bumpKernelNorm_lt_top : bumpKernelNorm < ⊤ :=
  (𝓕⁻ (bumpS 0 1) : 𝓢(ℝ, ℂ)).integrable.hasFiniteIntegral

/-- The `L¹` norm of the kernel of a bump is `bumpKernelNorm`. -/
theorem lintegral_enorm_fourierInv_bumpS (a : ℝ) {s : ℝ} (hs : 0 < s) :
    ∫⁻ y, ‖(𝓕⁻ (bumpS a s) : 𝓢(ℝ, ℂ)) y‖ₑ = bumpKernelNorm := by
  have h1 := ofReal_integral_norm_eq_lintegral_enorm
    (𝓕⁻ (bumpS a s) : 𝓢(ℝ, ℂ)).integrable (μ := volume)
  have h2 := ofReal_integral_norm_eq_lintegral_enorm
    (𝓕⁻ (bumpS 0 1) : 𝓢(ℝ, ℂ)).integrable (μ := volume)
  rw [← h1, bumpKernelNorm, ← h2]
  simp only [SchwartzMap.fourierInv_coe]
  rw [integral_norm_fourierInv_bumpS a hs]

/-- **Uniform `L¹` bound for the kernel of the cutoff**: `‖𝓕⁻χ_ε‖_{L¹} ≤ (1 + |Ξ|) ‖𝓕⁻θ‖_{L¹}`
for every `ε > 0`. -/
theorem lintegral_enorm_fourierInv_cutMult_le (Ξ : Finset ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ y, ‖(𝓕⁻ (cutMult Ξ ε) : 𝓢(ℝ, ℂ)) y‖ₑ ≤ (1 + Ξ.card) * bumpKernelNorm := by
  have hK : (𝓕⁻ (cutMult Ξ ε) : 𝓢(ℝ, ℂ)) =
      𝓕⁻ (bumpS 0 (1 / ε)) - ∑ ξ ∈ Ξ, 𝓕⁻ (bumpS ξ ε) := by
    rw [cutMult, sub_eq_add_neg, fourierInv_add, fourierInv_neg, fourierInv_sum, ← sub_eq_add_neg]
  have hpt : ∀ y, ‖(𝓕⁻ (cutMult Ξ ε) : 𝓢(ℝ, ℂ)) y‖ₑ ≤ ‖(𝓕⁻ (bumpS 0 (1 / ε)) : 𝓢(ℝ, ℂ)) y‖ₑ +
      ∑ ξ ∈ Ξ, ‖(𝓕⁻ (bumpS ξ ε) : 𝓢(ℝ, ℂ)) y‖ₑ := by
    intro y
    rw [hK]
    simp only [sub_apply, sum_apply]
    refine enorm_sub_le.trans (add_le_add le_rfl ?_)
    exact enorm_sum_le _ _
  have hm : ∀ a s : ℝ, Measurable fun y => ‖(𝓕⁻ (bumpS a s) : 𝓢(ℝ, ℂ)) y‖ₑ := fun a s =>
    (𝓕⁻ (bumpS a s) : 𝓢(ℝ, ℂ)).continuous.enorm.measurable
  calc ∫⁻ y, ‖(𝓕⁻ (cutMult Ξ ε) : 𝓢(ℝ, ℂ)) y‖ₑ
      ≤ ∫⁻ y, (‖(𝓕⁻ (bumpS 0 (1 / ε)) : 𝓢(ℝ, ℂ)) y‖ₑ +
          ∑ ξ ∈ Ξ, ‖(𝓕⁻ (bumpS ξ ε) : 𝓢(ℝ, ℂ)) y‖ₑ) := lintegral_mono hpt
    _ = (∫⁻ y, ‖(𝓕⁻ (bumpS 0 (1 / ε)) : 𝓢(ℝ, ℂ)) y‖ₑ) +
          ∑ ξ ∈ Ξ, ∫⁻ y, ‖(𝓕⁻ (bumpS ξ ε) : 𝓢(ℝ, ℂ)) y‖ₑ := by
        rw [lintegral_add_left (hm _ _), lintegral_finsetSum _ fun ξ _ => hm _ _]
    _ = bumpKernelNorm + ∑ _ξ ∈ Ξ, bumpKernelNorm := by
        rw [lintegral_enorm_fourierInv_bumpS _ (one_div_pos.2 hε)]
        simp_rw [lintegral_enorm_fourierInv_bumpS _ hε]
    _ = (1 + Ξ.card) * bumpKernelNorm := by
        rw [Finset.sum_const, nsmul_eq_mul, add_mul, one_mul]

/-- The Fourier transform of a difference of Schwartz functions. -/
theorem fourier_coe_sub (A B : 𝓢(ℝ, ℂ)) : 𝓕 ⇑(A - B) = 𝓕 ⇑A - 𝓕 ⇑B := by
  have : (𝓕 (A - B) : 𝓢(ℝ, ℂ)) = 𝓕 A - 𝓕 B := by
    simpa using (SchwartzMap.fourierTransformCLM (V := ℝ) (E := ℂ) ℂ).map_sub A B
  rw [← SchwartzMap.fourier_coe, this]
  simp [SchwartzMap.fourier_coe]


/-- **The Fourier cutoff** ([O+] L921-L926): for a
Schwartz function `f` and a finite set `Ξ` there are Schwartz functions `g_n` with `ĝ_n` compactly
supported in `ℝ ∖ Ξ` such that `‖f̂ - ĝ_n‖_{L¹} → 0` and `g_n → f` in `L^p` for every `p > 1`. -/
theorem exists_fourier_cutoff_seq (Ξ : Finset ℝ) (f : 𝓢(ℝ, ℂ)) :
    ∃ g : ℕ → 𝓢(ℝ, ℂ), (∀ n, HasCompactSupport (𝓕 ⇑(g n))) ∧
      (∀ n, ∀ ζ ∈ Ξ, ζ ∉ tsupport (𝓕 ⇑(g n))) ∧
      Tendsto (fun n => ∫ η, ‖𝓕 ⇑f η - 𝓕 ⇑(g n) η‖) atTop (𝓝 0) ∧
      ∀ p : ℝ, 1 < p →
        Tendsto (fun n => eLpNorm (⇑(g n) - ⇑f) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => ?_⟩
    simp only [Set.mem_Ioi]
    positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hseq.eventually (eventually_cutSmall Ξ))
  set ε : ℕ → ℝ := fun n => 1 / (((n + N : ℕ) : ℝ) + 1) with hε
  have hεsmall : ∀ n, CutSmall Ξ (ε n) := fun n => hN (n + N) (Nat.le_add_left _ _)
  have hεpos : ∀ n, 0 < ε n := fun n => (hεsmall n).1
  have hεlim : Tendsto ε atTop (𝓝[>] (0 : ℝ)) := hseq.comp (tendsto_add_atTop_nat N)
  set g : ℕ → 𝓢(ℝ, ℂ) := fun n => cutOp (cutMult Ξ (ε n)) f with hg
  have hFg : ∀ n η, 𝓕 ⇑(g n) η = 𝓕 ⇑f η * cutMult Ξ (ε n) η := fun n η => fourier_cutOp _ _ η
  have hFgfun : ∀ n, 𝓕 ⇑(g n) = fun η => 𝓕 ⇑f η * cutMult Ξ (ε n) η := fun n => funext (hFg n)
  have hnorm : ∀ n η, ‖𝓕 ⇑f η - 𝓕 ⇑(g n) η‖ = ‖𝓕 ⇑f η‖ * ‖1 - cutMult Ξ (ε n) η‖ := by
    intro n η
    rw [hFg, ← norm_mul]
    congr 1
    ring
  have h3 : Tendsto (fun n => ∫ η, ‖𝓕 ⇑f η - 𝓕 ⇑(g n) η‖) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence
      (μ := (volume : Measure ℝ)) (F := fun n η => ‖𝓕 ⇑f η - 𝓕 ⇑(g n) η‖) (f := fun _ => (0 : ℝ))
      (fun η => (2 + Ξ.card : ℝ) * ‖𝓕 ⇑f η‖)
      (fun n => ((integrable_fourier_schwartz f).sub (integrable_fourier_schwartz (g n))).norm
        |>.aestronglyMeasurable)
      ((integrable_fourier_schwartz f).norm.const_mul _)
      (fun n => Eventually.of_forall fun η => by
        rw [norm_norm, hnorm, mul_comm]
        exact mul_le_mul_of_nonneg_right (norm_one_sub_cutMult_le Ξ (hεpos n) η) (norm_nonneg _))
      (by
        have hne : ∀ᵐ η ∂(volume : Measure ℝ), η ∉ (Ξ : Set ℝ) :=
          (Finset.countable_toSet Ξ).ae_notMem _
        filter_upwards [hne] with η hη
        have hη' : η ∉ Ξ := hη
        have hev : ∀ᶠ n in atTop, cutMult Ξ (ε n) η = 1 :=
          hεlim.eventually (eventually_cutMult_eq_one Ξ hη')
        refine tendsto_const_nhds.congr' (hev.mono fun n hn => ?_)
        change (0 : ℝ) = ‖𝓕 ⇑f η - 𝓕 ⇑(g n) η‖
        rw [hnorm, hn]
        simp)
    simpa using this
  refine ⟨g, ?_, ?_, h3, ?_⟩
  · intro n
    rw [hFgfun n]
    exact (hasCompactSupport_cutMult Ξ (hεpos n)).mul_left
  · intro n ζ hζ
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [Metric.ball_mem_nhds ζ (hεpos n)] with η hη
    rw [hFg, cutMult_eq_zero_of_small (hεsmall n) hζ (by simpa [Real.dist_eq] using hη)]
    simp
  · intro p hp
    set c₁ : ℝ≥0∞ := ∫⁻ y, ‖f y‖ₑ with hc₁
    set M : ℝ≥0∞ := c₁ * ((1 + Ξ.card) * bumpKernelNorm) + c₁ with hM
    have hc₁_top : c₁ ≠ ⊤ := (f.integrable (μ := volume)).hasFiniteIntegral.ne
    have hM_top : M ≠ ⊤ := by
      refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hc₁_top (ENNReal.mul_ne_top ?_
        bumpKernelNorm_lt_top.ne), hc₁_top⟩
      exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.natCast_ne_top _⟩
    have hL1 : ∀ n, ∫⁻ x, ‖(⇑(g n) - ⇑f) x‖ₑ ≤ M := by
      intro n
      calc ∫⁻ x, ‖(⇑(g n) - ⇑f) x‖ₑ ≤ ∫⁻ x, (‖g n x‖ₑ + ‖f x‖ₑ) :=
            lintegral_mono fun x => enorm_sub_le
        _ = (∫⁻ x, ‖g n x‖ₑ) + ∫⁻ x, ‖f x‖ₑ :=
            lintegral_add_left (g n).continuous.enorm.measurable _
        _ ≤ c₁ * ((1 + Ξ.card) * bumpKernelNorm) + c₁ := by
            gcongr
            exact (lintegral_enorm_cutOp_le (cutMult Ξ (ε n)) f).trans (by
              rw [mul_comm c₁ _]
              rw [mul_comm]
              gcongr
              exact lintegral_enorm_fourierInv_cutMult_le Ξ (hεpos n))
    have hsup : ∀ n x, ‖(⇑(g n) - ⇑f) x‖ₑ ≤ ENNReal.ofReal (∫ η, ‖𝓕 ⇑f η - 𝓕 ⇑(g n) η‖) := by
      intro n x
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      have := norm_le_integral_norm_fourier (g n - f) x
      simp only [sub_apply, fourier_coe_sub] at this ⊢
      refine this.trans (le_of_eq (integral_congr_ae (Eventually.of_forall fun η => ?_)))
      simp only [Pi.sub_apply]
      exact norm_sub_rev _ _
    have hbd : ∀ n, eLpNorm (⇑(g n) - ⇑f) (ENNReal.ofReal p) volume ≤
        (ENNReal.ofReal (∫ η, ‖𝓕 ⇑f η - 𝓕 ⇑(g n) η‖) ^ (p - 1) * M) ^ (1 / p) := fun n =>
      eLpNorm_le_of_enorm_le_of_lintegral_le hp
        ((g n - f).continuous.aestronglyMeasurable) ENNReal.ofReal_ne_top (hsup n) (hL1 n)
    have hδ : Tendsto (fun n => ENNReal.ofReal (∫ η, ‖𝓕 ⇑f η - 𝓕 ⇑(g n) η‖)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal h3
    have hpow : Tendsto (fun n => (ENNReal.ofReal (∫ η, ‖𝓕 ⇑f η - 𝓕 ⇑(g n) η‖) ^ (p - 1) * M) ^
        (1 / p)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => ENNReal.ofReal (∫ η, ‖𝓕 ⇑f η - 𝓕 ⇑(g n) η‖) ^ (p - 1))
          atTop (𝓝 0) := by
        have := ((ENNReal.continuous_rpow_const (y := p - 1)).tendsto 0).comp hδ
        rw [ENNReal.zero_rpow_of_pos (sub_pos.2 hp)] at this
        exact this
      have h2 : Tendsto (fun n => ENNReal.ofReal (∫ η, ‖𝓕 ⇑f η - 𝓕 ⇑(g n) η‖) ^ (p - 1) * M)
          atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hM_top)
      have := ((ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0).comp h2
      rw [ENNReal.zero_rpow_of_pos (one_div_pos.2 (by linarith : (0 : ℝ) < p))] at this
      exact this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpow (fun n => zero_le) hbd

end PrimeCarleson.Proof.Oplus

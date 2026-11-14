module

public import PrimeCarleson.Proof.Lepingle.Prob.Stopping

/-!
# Lépingle's inequality for martingales

Source: Zorin-Kranich's notes `thm:lepingle` (02-Lepingle.tex, L16–L25), L153–L158 and L32:
Theorem 2.1 (02-Lepingle.tex L16-L168): for a martingale `f` on a filtered probability space
(here: finite measure space),
`1 ≤ p < ∞` and `r > 2`,
`‖V^r f‖_p ≤ C_p · r/(r-2) · ‖Mf‖_p`.

* `lintegral_root_tsum_le`: Minkowski's inequality in `L^p` for countable sums of nonnegative
  functions (tacit in L153-L154);
* `lp_sum_over_m`:
  `‖V^r(f; 0..N)‖_p ≤ 8 ∑_{m ≥ 2} 2^{-(m-2)(r-2)/2} ‖S_{(m)}‖_p` from the pathwise bound
  `seqVariationOn_le_tsum_sqFun` of `Lepingle/Path`;
* `lepingle_horizon`: with the BDG inequality for the sampled martingales (`bdg_stopped`) and the
  geometric series (`tsum_ofReal_lepingleWeight_le`),
  `‖V^r(f; 0..N)‖_p ≤ 672 p r/(r-2) ‖sup_{k ≤ N} |f_k|‖_p`.

This is Theorem 2.1 on a finite horizon `N`; the dyadic martingale on `ℝ` (`lepingle_dyadic` of
`Lepingle/Prob/Dyadic.lean`) uses it directly.

The constant is `C_p = 12 · 56 p = 672 p`, i.e. better than the `12 C'_p` with `C'_p = 112 p`
of the notes' argument, because BDG (`bdg_sqFn_le`) needs no `f_0 = 0`.  No integrability hypothesis
beyond `f` being a martingale on a finite measure space: all quantities are `ℝ≥0∞`-valued
(if `‖Mf‖_p = ∞` the inequality is trivial).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Finset
open scoped ENNReal NNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Lepingle

section Minkowski

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Minkowski's inequality in `L^p` for finite sums of nonnegative measurable functions. -/
theorem lintegral_root_finsetSum_le {ι : Type*} (s : Finset ι) {g : ι → Ω → ℝ≥0∞}
    (hg : ∀ i, Measurable (g i)) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ ω, (∑ i ∈ s, g i ω) ^ p ∂μ) ^ (1 / p) ≤ ∑ i ∈ s, (∫⁻ ω, g i ω ^ p ∂μ) ^ (1 / p) := by
  classical
  have hp0 : 0 < p := by linarith
  induction s using Finset.induction_on with
  | empty =>
    simp [ENNReal.zero_rpow_of_pos hp0, hp0]
  | insert a s ha ih =>
    have hS : Measurable fun ω => ∑ i ∈ s, g i ω := Finset.measurable_sum _ fun i _ => hg i
    simp_rw [Finset.sum_insert ha]
    refine le_trans ?_ (add_le_add le_rfl ih)
    exact ENNReal.lintegral_Lp_add_le (f := g a) (g := fun ω => ∑ i ∈ s, g i ω)
      (hg a).aemeasurable hS.aemeasurable hp

/-- Minkowski's inequality in `L^p` for countable sums of nonnegative measurable functions
(as used at Zorin-Kranich's notes, L153-L154: monotone convergence of the partial sums). -/
theorem lintegral_root_tsum_le {g : ℕ → Ω → ℝ≥0∞} (hg : ∀ k, Measurable (g k)) {p : ℝ}
    (hp : 1 ≤ p) :
    (∫⁻ ω, (∑' k, g k ω) ^ p ∂μ) ^ (1 / p) ≤ ∑' k, (∫⁻ ω, g k ω ^ p ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  set t : ℕ → ℝ≥0∞ := fun k => (∫⁻ ω, g k ω ^ p ∂μ) ^ (1 / p) with ht
  have hGm : ∀ n, Measurable fun ω => ∑ k ∈ Finset.range n, g k ω := fun n =>
    Finset.measurable_sum _ fun k _ => hg k
  have hsup : ∫⁻ ω, (∑' k, g k ω) ^ p ∂μ =
      ⨆ n, ∫⁻ ω, (∑ k ∈ Finset.range n, g k ω) ^ p ∂μ := by
    rw [← lintegral_iSup]
    · refine lintegral_congr fun ω => ?_
      calc (∑' k, g k ω) ^ p = (⨆ n, ∑ k ∈ Finset.range n, g k ω) ^ p := by
            rw [ENNReal.tsum_eq_iSup_nat]
        _ = ⨆ n, (∑ k ∈ Finset.range n, g k ω) ^ p :=
            Monotone.map_iSup_of_continuousAt (f := fun x : ℝ≥0∞ => x ^ p)
              (g := fun n : ℕ => ∑ k ∈ Finset.range n, g k ω)
              ENNReal.continuous_rpow_const.continuousAt
              (fun a b hab => ENNReal.rpow_le_rpow hab hp0.le) (ENNReal.zero_rpow_of_pos hp0)
    · exact fun n => (hGm n).pow_const _
    · intro n m hnm ω
      exact ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset (Finset.range_mono hnm)) hp0.le
  have hle : ∫⁻ ω, (∑' k, g k ω) ^ p ∂μ ≤ (∑' k, t k) ^ p := by
    rw [hsup]
    refine iSup_le fun n => ?_
    have h1 := lintegral_root_finsetSum_le (μ := μ) (Finset.range n) hg hp
    have h2 : (∑ k ∈ Finset.range n, t k) ≤ ∑' k, t k := ENNReal.sum_le_tsum _
    have h3 := ENNReal.rpow_le_rpow (h1.trans h2) hp0.le
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one] at h3
  calc (∫⁻ ω, (∑' k, g k ω) ^ p ∂μ) ^ (1 / p) ≤ ((∑' k, t k) ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hle (by positivity)
    _ = ∑' k, t k := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

/-- Monotone convergence for `L^p` norms in `ℝ≥0∞`: if `g_N ≥ 0` are measurable and increasing in
`N` with `‖g_N‖_p ≤ K` for all `N`, then `‖sup_N g_N‖_p ≤ K` (used in the reduction to martingales
that are eventually constant). -/
theorem lintegral_root_iSup_le {g : ℕ → Ω → ℝ≥0∞} (hg : ∀ N, Measurable (g N))
    (hmono : ∀ ω, Monotone fun N => g N ω) {p : ℝ} (hp : 0 < p) {K : ℝ≥0∞}
    (hK : ∀ N, (∫⁻ ω, g N ω ^ p ∂μ) ^ (1 / p) ≤ K) :
    (∫⁻ ω, (⨆ N, g N ω) ^ p ∂μ) ^ (1 / p) ≤ K := by
  have hsup : ∫⁻ ω, (⨆ N, g N ω) ^ p ∂μ = ⨆ N, ∫⁻ ω, g N ω ^ p ∂μ := by
    rw [← lintegral_iSup]
    · refine lintegral_congr fun ω => ?_
      exact Monotone.map_iSup_of_continuousAt (f := fun x : ℝ≥0∞ => x ^ p)
        (g := fun N : ℕ => g N ω) ENNReal.continuous_rpow_const.continuousAt
        (fun a b hab => ENNReal.rpow_le_rpow hab hp.le) (ENNReal.zero_rpow_of_pos hp)
    · exact fun N => (hg N).pow_const _
    · intro N M hNM ω
      exact ENNReal.rpow_le_rpow (hmono ω hNM) hp.le
  have hle : ∫⁻ ω, (⨆ N, g N ω) ^ p ∂μ ≤ K ^ p := by
    rw [hsup]
    refine iSup_le fun N => ?_
    have h3 := ENNReal.rpow_le_rpow (hK N) hp.le
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one] at h3
  calc (∫⁻ ω, (⨆ N, g N ω) ^ p ∂μ) ^ (1 / p) ≤ (K ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hle (by positivity)
    _ = K := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]

end Minkowski

section Measurability

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {𝕜 : Type*} [RCLike 𝕜] {f : ℕ → Ω → 𝕜}

end Measurability

section Lepingle

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
  {𝕜 : Type*} [RCLike 𝕜] {f : ℕ → Ω → 𝕜}

theorem measurable_sqFun_path [IsFiniteMeasure μ] (hf : Martingale f ℱ μ) (N m : ℕ) :
    Measurable fun ω => sqFun (fun n => f n ω) N m := by
  have hg := martingale_sampled hf N m
  have hm : ∀ j, Measurable (sampled f N m j) := fun j =>
    (hg.stronglyMeasurable j).measurable.mono ((partFiltration hf.stronglyAdapted N m).le j) le_rfl
  have : (fun ω => sqFun (fun n => f n ω) N m) = sqUpTo (sampled f N m) N := by
    funext ω
    exact sqFun_eq_sqUpTo_sampled f N m ω
  rw [this]
  exact measurable_sqUpTo fun k _ => hm k

/-- **Minkowski over the levels** (Zorin-Kranich's notes, L153-L158): for a martingale `f`,
`1 ≤ p < ∞`, `r > 2`, `‖V^r(f; 0..N)‖_p ≤ 8 ∑_{m ≥ 2} 2^{-(m-2)(r-2)/2} ‖S_{(m)}‖_p`
(the sum over `k = m - 2`). -/
theorem lp_sum_over_m [IsFiniteMeasure μ] (hf : Martingale f ℱ μ) {p : ℝ} (hp : 1 ≤ p)
    {r : ℝ} (hr : 2 < r) (N : ℕ) :
    (∫⁻ ω, seqVariationOn r (fun n => f n ω) N ^ p ∂μ) ^ (1 / p) ≤
      8 * ∑' k : ℕ, ENNReal.ofReal (lepingleWeight r k) *
        (∫⁻ ω, sqFun (fun n => f n ω) N (k + 2) ^ p ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  set S : ℕ → Ω → ℝ≥0∞ := fun k ω => sqFun (fun n => f n ω) N (k + 2) with hS
  have hSm : ∀ k, Measurable (S k) := fun k => measurable_sqFun_path hf N (k + 2)
  have hcm : ∀ k, Measurable fun ω => ENNReal.ofReal (lepingleWeight r k) * S k ω := fun k =>
    (hSm k).const_mul _
  calc (∫⁻ ω, seqVariationOn r (fun n => f n ω) N ^ p ∂μ) ^ (1 / p)
      ≤ (∫⁻ ω, (8 * ∑' k, ENNReal.ofReal (lepingleWeight r k) * S k ω) ^ p ∂μ) ^ (1 / p) := by
        refine ENNReal.rpow_le_rpow (lintegral_mono fun ω => ?_) (by positivity)
        exact ENNReal.rpow_le_rpow (seqVariationOn_le_tsum_sqFun hr _ N) hp0.le
    _ ≤ 8 * (∫⁻ ω, (∑' k, ENNReal.ofReal (lepingleWeight r k) * S k ω) ^ p ∂μ) ^ (1 / p) :=
        root_lintegral_le_const_mul (by norm_num) hp0 fun ω => le_rfl
    _ ≤ 8 * ∑' k, (∫⁻ ω, (ENNReal.ofReal (lepingleWeight r k) * S k ω) ^ p ∂μ) ^ (1 / p) := by
        gcongr
        exact lintegral_root_tsum_le hcm hp
    _ ≤ 8 * ∑' k, ENNReal.ofReal (lepingleWeight r k) * (∫⁻ ω, S k ω ^ p ∂μ) ^ (1 / p) := by
        gcongr with k
        exact root_lintegral_le_const_mul ENNReal.ofReal_ne_top hp0 fun ω => le_rfl

/-- **Lépingle's inequality on the horizon `[0, N]`** (Zorin-Kranich's notes, Theorem 2.1,
L139-L168): for a martingale `f` on a finite measure space, `1 ≤ p < ∞`, `r > 2` and every `N`,
`‖V^r(f; 0..N)‖_p ≤ 672 p · r/(r-2) · ‖sup_{k ≤ N} |f_k|‖_p`. -/
theorem lepingle_horizon [IsFiniteMeasure μ] (hf : Martingale f ℱ μ) {p : ℝ} (hp : 1 ≤ p)
    {r : ℝ} (hr : 2 < r) (N : ℕ) :
    (∫⁻ ω, seqVariationOn r (fun n => f n ω) N ^ p ∂μ) ^ (1 / p) ≤
      ENNReal.ofReal (672 * p * (r / (r - 2))) * (∫⁻ ω, maxUpTo f N ω ^ p ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  set X := (∫⁻ ω, maxUpTo f N ω ^ p ∂μ) ^ (1 / p) with hX
  refine (lp_sum_over_m hf hp hr N).trans ?_
  calc 8 * ∑' k : ℕ, ENNReal.ofReal (lepingleWeight r k) *
        (∫⁻ ω, sqFun (fun n => f n ω) N (k + 2) ^ p ∂μ) ^ (1 / p)
      ≤ 8 * ∑' k : ℕ, ENNReal.ofReal (lepingleWeight r k) * (ENNReal.ofReal (56 * p) * X) := by
        gcongr with k
        exact bdg_stopped hf hp N (k + 2)
    _ = 8 * ((∑' k : ℕ, ENNReal.ofReal (lepingleWeight r k)) * (ENNReal.ofReal (56 * p) * X)) := by
        rw [ENNReal.tsum_mul_right]
    _ ≤ 8 * (ENNReal.ofReal (3 / 2 * (r / (r - 2))) * (ENNReal.ofReal (56 * p) * X)) := by
        gcongr
        exact tsum_ofReal_lepingleWeight_le hr
    _ = ENNReal.ofReal (672 * p * (r / (r - 2))) * X := by
        have hr2 : 0 < r / (r - 2) := div_pos (by linarith) (by linarith)
        have h8 : (8 : ℝ≥0∞) = ENNReal.ofReal 8 := by simp
        rw [h8, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

end Lepingle

section Final

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℂ}

end Final

end PrimeCarleson.Proof.Lepingle

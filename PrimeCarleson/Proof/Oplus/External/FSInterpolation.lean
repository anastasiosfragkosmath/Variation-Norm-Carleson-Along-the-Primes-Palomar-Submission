module

public import PrimeCarleson.Proof.Oplus.External.FSLayerCake
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Interpolation between `L¹` and dyadic BMO

[O+] L2603-L2609 ("we may interpolate the `L¹` and the BMO
bound ... a standard technique involving the sharp maximal function from §5 in [fs-hardy]"), with
an own dyadic stopping-time proof:

`dyadic_interpolation`: for every `q ∈ [1, ∞)` there is `C_q` such that for every `g ≥ 0` in `L¹`
which is locally constant at almost every point (e.g. a finite sum of indicators of bounded
intervals; `dyadic_interpolation_indicators`, `dyadic_interpolation_dilates`) and every `b ≥ 0` with
`dyadicBMO g ≤ b` (the dyadic BMO norm of `EnergyIncrement/BmoGeometry.lean`),
`‖g‖_q ≤ C_q ‖g‖_1^{1/q} b^{1 - 1/q}` (in `ℝ≥0∞`, `‖·‖` the `eLpNorm`); one may take `C_1 = 1` and
`C_q^q = q (4^{q-1}/(q-1) + 4^q Γ(q)/(log 2)^q)` (`layerCakeConst`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-! ### The BMO norm and the mean oscillation bound -/

/-- `dyadicBMO g ≤ b` gives the mean oscillation bound `∫_I |g - g_I| ≤ b |I|`. -/
theorem meanOscLe_of_dyadicBMO_le {g : ℝ → ℝ} (hgi : Integrable g) {b : ℝ} (hb : 0 ≤ b)
    (h : dyadicBMO g ≤ ENNReal.ofReal b) : MeanOscLe g b := by
  intro I
  have hfin : volume I.toSet ≠ ∞ := by rw [Dyadic.volume_toSet]; exact ENNReal.ofReal_ne_top
  have hI0 : volume I.toSet ≠ 0 := by
    rw [Dyadic.volume_toSet]; exact (ENNReal.ofReal_pos.2 I.length_pos).ne'
  have h1 : ⨍⁻ y in I.toSet, ‖g y - (⨍ z in I.toSet, g z ∂volume)‖ₑ ∂volume ≤ ENNReal.ofReal b :=
    le_trans (le_iSup (fun J : Dyadic =>
      ⨍⁻ y in J.toSet, ‖g y - (⨍ z in J.toSet, g z ∂volume)‖ₑ ∂volume) I) h
  rw [laverage_eq, Measure.restrict_apply_univ, ENNReal.div_le_iff hI0 hfin] at h1
  have hint : IntegrableOn (fun y => |g y - dyadicMean g I|) I.toSet :=
    (hgi.integrableOn.sub (integrableOn_const hfin)).abs
  have h2 : ENNReal.ofReal (∫ y in I.toSet, |g y - dyadicMean g I|) ≤
      ENNReal.ofReal (b * I.length) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun y => abs_nonneg _),
      ENNReal.ofReal_mul hb, ← Dyadic.volume_toSet]
    refine le_trans (le_of_eq ?_) h1
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal_abs]
    rfl
  exact (ENNReal.ofReal_le_ofReal_iff (by have := I.length_pos; positivity)).1 h2

/-! ### Dyadic differentiation at points of local constancy -/

/-- A function that is locally constant at almost every point satisfies `g ≤ M_D g` a.e.:
the dyadic interval of scale `k → -∞` containing `x` has average `g(x)`. -/
theorem dyadicDominated_of_locallyConstant {g : ℝ → ℝ}
    (h : ∀ᵐ x : ℝ, ∀ᶠ y in 𝓝 x, g y = g x) : DyadicDominated g := by
  filter_upwards [h] with x hx t ht
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hx
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  set I := Dyadic.ofPoint (-(n : ℤ)) x with hI
  have hxI : x ∈ I.toSet := Dyadic.mem_toSet_ofPoint _ x
  have hlen : I.length < δ := by
    have : I.length = (1 / 2 : ℝ) ^ n := by
      simp [I, Dyadic.length, Dyadic.ofPoint, zpow_neg, one_div, inv_pow]
    rwa [this]
  have hconst : ∀ y ∈ I.toSet, g y = g x := by
    intro y hy
    apply hδ'
    rw [Real.dist_eq]
    have h1 := hy
    have h2 := hxI
    have := I.right_eq
    rw [abs_lt]
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  have havg : dyadicMean g I = g x := by
    have hfin : volume I.toSet ≠ ∞ := by rw [Dyadic.volume_toSet]; exact ENNReal.ofReal_ne_top
    have hI0 : volume I.toSet ≠ 0 := by
      rw [Dyadic.volume_toSet]; exact (ENNReal.ofReal_pos.2 I.length_pos).ne'
    rw [dyadicMean, setAverage_congr_fun I.measurableSet_toSet
      (Eventually.of_forall hconst), setAverage_const hI0 hfin]
  exact ⟨I, hxI, by rw [havg]; exact ht⟩

/-! ### The `L^q` norm of a nonnegative function -/

/-- `‖g‖_q = (∫ g^q)^{1/q}` for `g ≥ 0`. -/
theorem eLpNorm_eq_lintegral_ofReal_rpow {g : ℝ → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hg : AEStronglyMeasurable g volume) {q : ℝ} (hq : 0 < q) :
    eLpNorm g (ENNReal.ofReal q) volume = (∫⁻ x, ENNReal.ofReal (g x ^ q)) ^ (1 / q) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq).ne' ENNReal.ofReal_ne_top
    hg, ENNReal.toReal_ofReal hq.le]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_of_nonneg (hg0 x), ENNReal.ofReal_rpow_of_nonneg (hg0 x) hq.le]

/-- `‖g‖_1 = ∫ g` for `g ≥ 0` integrable. -/
theorem eLpNorm_one_eq_ofReal_integral {g : ℝ → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g) :
    eLpNorm g 1 volume = ENNReal.ofReal (∫ y, g y) := by
  rw [eLpNorm_one_eq_lintegral_enorm hgi.aestronglyMeasurable,
    ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall hg0)]
  exact lintegral_congr fun x => Real.enorm_of_nonneg (hg0 x)

/-! ### The interpolation inequality -/

/-- **`L^q ≤ L¹^{1/q} BMO^{1-1/q}` for `q > 1`**, with the constant `K_q^{1/q}`. -/
theorem eLpNorm_le_of_dyadicBMO_le {q : ℝ} (hq : 1 < q) {g : ℝ → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hgi : Integrable g) (hdom : DyadicDominated g) {b : ℝ} (hb : 0 ≤ b)
    (hBMO : dyadicBMO g ≤ ENNReal.ofReal b) :
    eLpNorm g (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (layerCakeConst q ^ (1 / q)) * eLpNorm g 1 volume ^ (1 / q) *
        ENNReal.ofReal b ^ (1 - 1 / q) := by
  set A := ∫ y, g y with hA
  have hA0 : 0 ≤ A := integral_nonneg hg0
  have hq0 : 0 < q := by linarith
  have hK0 : 0 ≤ layerCakeConst q := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    unfold layerCakeConst
    have : 0 < Real.log 2 ^ q := Real.rpow_pos_of_pos hlog q
    have hG := Real.Gamma_pos_of_pos hq0
    have h1 : 0 ≤ (4 : ℝ) ^ (q - 1) / (q - 1) :=
      div_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith)
    have h2 : 0 ≤ (4 : ℝ) ^ q * Real.Gamma q / Real.log 2 ^ q := by positivity
    positivity
  have hexp : 0 < 1 - 1 / q := by
    rw [sub_pos, one_div]; exact inv_lt_one_of_one_lt₀ hq
  rcases hb.eq_or_lt with hb0 | hb0
  · -- `b = 0`: all the oscillations vanish and `g = 0`
    subst hb0
    rw [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hexp, mul_zero]
    refine le_of_eq ?_
    rw [eLpNorm_eq_lintegral_ofReal_rpow hg0 hgi.aestronglyMeasurable hq0]
    have hL : ∫⁻ x, ENNReal.ofReal (g x ^ q) = 0 := by
      refine le_antisymm ?_ bot_le
      have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (layerCakeConst q *
          (1 / ((n : ℝ) + 1)) ^ (q - 1) * A)) atTop (𝓝 0) := by
        have h0 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ (q - 1)) atTop (𝓝 0) := by
          have := (Real.continuousAt_rpow_const 0 (q - 1) (Or.inr (by linarith))).tendsto.comp
            tendsto_one_div_add_atTop_nhds_zero_nat
          rwa [Real.zero_rpow (by linarith)] at this
        have h1 := (h0.const_mul (layerCakeConst q)).mul_const A
        rw [mul_zero, zero_mul] at h1
        simpa using ENNReal.tendsto_ofReal h1
      refine ge_of_tendsto' hlim fun n => ?_
      have hbn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hBn : dyadicBMO g ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
        hBMO.trans (by simp)
      exact lintegral_ofReal_rpow_le hg0 hgi hdom
        (meanOscLe_of_dyadicBMO_le hgi hbn.le hBn) hbn hq
    rw [hL, ENNReal.zero_rpow_of_pos (by positivity)]
  · have hbm : MeanOscLe g b := meanOscLe_of_dyadicBMO_le hgi hb hBMO
    have hmain := lintegral_ofReal_rpow_le hg0 hgi hdom hbm hb0 hq
    rw [eLpNorm_eq_lintegral_ofReal_rpow hg0 hgi.aestronglyMeasurable hq0,
      eLpNorm_one_eq_ofReal_integral hg0 hgi]
    have hreal : (layerCakeConst q * b ^ (q - 1) * A) ^ (1 / q) =
        layerCakeConst q ^ (1 / q) * A ^ (1 / q) * b ^ (1 - 1 / q) := by
      rw [Real.mul_rpow (mul_nonneg hK0 (Real.rpow_nonneg hb _)) hA0,
        Real.mul_rpow hK0 (Real.rpow_nonneg hb _), ← Real.rpow_mul hb,
        show (q - 1) * (1 / q) = 1 - 1 / q by field_simp]
      ring
    refine (ENNReal.rpow_le_rpow hmain (by positivity)).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (mul_nonneg hK0 (Real.rpow_nonneg hb _)) hA0)
      (by positivity), hreal, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (Real.rpow_nonneg hK0 _),
      ENNReal.ofReal_rpow_of_nonneg hA0 (by positivity),
      ENNReal.ofReal_rpow_of_nonneg hb hexp.le]

/-- **Interpolation between `L¹` and dyadic BMO** (Source: [O+], L2603–L2609; Fefferman–Stein
interpolation between L¹ and dyadic BMO; [O+] L2603-L2609): for every `q ∈ [1, ∞)` there is
`C_q ≥ 0` such
that for every integrable `g ≥ 0` which is locally constant at almost every point (e.g. a finite
sum of indicators of bounded intervals, see `dyadic_interpolation_indicators`) and every `b ≥ 0`
with `dyadicBMO g ≤ b`: `‖g‖_{L^q} ≤ C_q ‖g‖_{L¹}^{1/q} b^{1 - 1/q}`. -/
theorem dyadic_interpolation {q : ℝ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℝ → ℝ, (∀ x, 0 ≤ g x) → Integrable g →
      (∀ᵐ x : ℝ, ∀ᶠ y in 𝓝 x, g y = g x) → ∀ b : ℝ, 0 ≤ b → dyadicBMO g ≤ ENNReal.ofReal b →
      eLpNorm g (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal C * eLpNorm g 1 volume ^ (1 / q) * ENNReal.ofReal b ^ (1 - 1 / q) := by
  rcases hq.eq_or_lt with rfl | hq1
  · refine ⟨1, zero_le_one, fun g _ _ _ b _ _ => le_of_eq ?_⟩
    simp
  · have hK0 : 0 ≤ layerCakeConst q ^ (1 / q) := by
      have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hq0 : 0 < q := by linarith
      have hG := Real.Gamma_pos_of_pos hq0
      have h1 : 0 ≤ (4 : ℝ) ^ (q - 1) / (q - 1) :=
        div_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith)
      have h2 : 0 ≤ (4 : ℝ) ^ q * Real.Gamma q / Real.log 2 ^ q := by
        have : 0 < Real.log 2 ^ q := Real.rpow_pos_of_pos hlog q
        positivity
      exact Real.rpow_nonneg (by unfold layerCakeConst; positivity) _
    exact ⟨_, hK0, fun g hg0 hgi hloc b hb hBMO =>
      eLpNorm_le_of_dyadicBMO_le hq1 hg0 hgi (dyadicDominated_of_locallyConstant hloc) hb hBMO⟩

/-! ### Finite sums of indicators of intervals -/

universe u

/-- The indicator of a half-open interval is locally constant away from its end points. -/
theorem eventually_indicator_Ico_eq {a b x : ℝ} (hxa : x ≠ a) (hxb : x ≠ b) :
    ∀ᶠ y in 𝓝 x, (Ico a b).indicator (fun _ => (1 : ℝ)) y =
      (Ico a b).indicator (fun _ => (1 : ℝ)) x := by
  rcases lt_or_gt_of_ne hxa with h1 | h1
  · filter_upwards [Iio_mem_nhds h1] with y hy
    have h2 : y ∉ Ico a b := fun h => absurd h.1 (not_le.2 hy)
    have h3 : x ∉ Ico a b := fun h => absurd h.1 (not_le.2 h1)
    rw [indicator_of_notMem h2, indicator_of_notMem h3]
  · rcases lt_or_gt_of_ne hxb with h2 | h2
    · filter_upwards [Ioo_mem_nhds h1 h2] with y hy
      rw [indicator_of_mem (show y ∈ Ico a b from ⟨hy.1.le, hy.2⟩),
        indicator_of_mem (show x ∈ Ico a b from ⟨h1.le, h2⟩)]
    · filter_upwards [Ioi_mem_nhds h2] with y hy
      have h3 : y ∉ Ico a b := fun h => absurd h.2 (not_lt.2 (le_of_lt hy))
      have h4 : x ∉ Ico a b := fun h => absurd h.2 (not_lt.2 (le_of_lt h2))
      rw [indicator_of_notMem h3, indicator_of_notMem h4]

/-- A finite sum of indicators of half-open intervals is locally constant at almost every point. -/
theorem locallyConstant_sum_indicator_Ico {ι : Type u} (S : Finset ι) (a b : ι → ℝ) :
    ∀ᵐ x : ℝ, ∀ᶠ y in 𝓝 x, (∑ i ∈ S, (Ico (a i) (b i)).indicator (fun _ => (1 : ℝ)) y) =
      ∑ i ∈ S, (Ico (a i) (b i)).indicator (fun _ => (1 : ℝ)) x := by
  classical
  have hnull : volume (((S.image a : Finset ℝ) : Set ℝ) ∪ ((S.image b : Finset ℝ) : Set ℝ)) = 0 :=
    ((Finset.finite_toSet _).union (Finset.finite_toSet _)).measure_zero _
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx
  have hxa : ∀ i ∈ S, x ≠ a i := fun i hi h =>
    hx (Or.inl (by simp only [Finset.coe_image, mem_image, Finset.mem_coe]; exact ⟨i, hi, h.symm⟩))
  have hxb : ∀ i ∈ S, x ≠ b i := fun i hi h =>
    hx (Or.inr (by simp only [Finset.coe_image, mem_image, Finset.mem_coe]; exact ⟨i, hi, h.symm⟩))
  have := (Filter.eventually_all_finset S).2 fun i hi =>
    eventually_indicator_Ico_eq (hxa i hi) (hxb i hi)
  filter_upwards [this] with y hy
  exact Finset.sum_congr rfl hy

/-- A finite sum of indicators of half-open bounded intervals is integrable. -/
theorem integrable_sum_indicator_Ico {ι : Type u} (S : Finset ι) (a b : ι → ℝ) :
    Integrable (fun x => ∑ i ∈ S, (Ico (a i) (b i)).indicator (fun _ => (1 : ℝ)) x) := by
  refine integrable_finsetSum S fun i _ => ?_
  exact (integrable_indicator_iff measurableSet_Ico).2
    (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))

/-- **Interpolation for finite sums of indicators of intervals** (the form used for the `L^q`
bound for the covering function in the large-`F` case of `L1except`, [O+] L2603-L2609): for every
`q ∈ [1, ∞)` there is `C_q ≥ 0` such that for every finite family of half-open bounded intervals
`[a_i, b_i)` and every `b ≥ 0` with the dyadic BMO norm of `g = ∑_i 1_{[a_i, b_i)}` at most `b`:
`‖g‖_q ≤ C_q ‖g‖_1^{1/q} b^{1 - 1/q}`. -/
theorem dyadic_interpolation_indicators {q : ℝ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} (S : Finset ι) (a b' : ι → ℝ) (b : ℝ), 0 ≤ b →
      dyadicBMO (fun x => ∑ i ∈ S, (Ico (a i) (b' i)).indicator (fun _ => (1 : ℝ)) x) ≤
        ENNReal.ofReal b →
      eLpNorm (fun x => ∑ i ∈ S, (Ico (a i) (b' i)).indicator (fun _ => (1 : ℝ)) x)
          (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal C *
          eLpNorm (fun x => ∑ i ∈ S, (Ico (a i) (b' i)).indicator (fun _ => (1 : ℝ)) x) 1
            volume ^ (1 / q) * ENNReal.ofReal b ^ (1 - 1 / q) := by
  obtain ⟨C, hC, h⟩ := dyadic_interpolation hq
  refine ⟨C, hC, fun {ι} S a b' b hb hBMO => h _ (fun x => ?_)
    (integrable_sum_indicator_Ico S a b') (locallyConstant_sum_indicator_Ico S a b') b hb hBMO⟩
  exact Finset.sum_nonneg fun i _ => indicator_nonneg (fun _ _ => zero_le_one) x

/-- **Interpolation for sums of dilates of dyadic intervals**: the covering functions
`∑_{T ∈ 𝒯} 1_{2^ℓ I_T}` of [O+] L2603-L2609 (`C = 2^ℓ`, `I_T = D T`). -/
theorem dyadic_interpolation_dilates {q : ℝ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} (S : Finset ι) (D : ι → Dyadic) (c : ℝ) (b : ℝ), 0 ≤ b →
      dyadicBMO (fun x => ∑ i ∈ S, ((D i).dilate c).indicator (fun _ => (1 : ℝ)) x) ≤
        ENNReal.ofReal b →
      eLpNorm (fun x => ∑ i ∈ S, ((D i).dilate c).indicator (fun _ => (1 : ℝ)) x)
          (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal C *
          eLpNorm (fun x => ∑ i ∈ S, ((D i).dilate c).indicator (fun _ => (1 : ℝ)) x) 1
            volume ^ (1 / q) * ENNReal.ofReal b ^ (1 - 1 / q) := by
  obtain ⟨C, hC, h⟩ := dyadic_interpolation_indicators.{u} hq
  exact ⟨C, hC, fun {ι} S D c b hb hBMO =>
    h S (fun i => (D i).center - c * (D i).length / 2)
      (fun i => (D i).center + c * (D i).length / 2) b hb hBMO⟩

end PrimeCarleson.Proof.Oplus

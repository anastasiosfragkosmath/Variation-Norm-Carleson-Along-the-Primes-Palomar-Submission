module

public import PrimeCarleson.Proof.Common.FourierZ
public import PrimeCarleson.Proof.Common.FourierR
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Fourier densities on `ℤ`: the band-limited carrier

Source: main paper `s:MFanalysis`, L1861–L1930 and L2002–L2019. The paper works with `f ∈ ℓ²(ℤ)`
whose Fourier transform `f̂` is supported in a compact interval `I ⊂ 𝕋` contained in one coordinate
chart of `𝕋` (L1861–L1879). Such an `f` is not finitely supported, so the finitely supported
interface does not apply. Here a sequence is given by its Fourier density on a chart `[θ, θ + 1]`:

`invFZ θ H x = ∫_θ^{θ+1} H(β) e(xβ) dβ`,   `H ∈ L²(θ, θ + 1]` (`ChartL2`).

* `hasSum_sq_invFZ` (Parseval): `∑_x |invFZ θ H x|² = ∫_θ^{θ+1} |H|²` for every `ChartL2` density
  (Mathlib's `hasSum_sq_fourierCoeffOn`), so `‖invFZ θ H‖_{ℓ²} = ‖H‖_{L²}`;
* the multiplier operator of a bounded multiplier `m` is `invFZ θ (m H)`, "`K * f`" with
  `(K * f)^ = m f̂`: no kernel `K = m^∨` is needed;
* `invFZ_fourierZ`: for a finitely supported `f`, `invFZ θ (fourierZ f) = f` on every chart;
* `invFZ_conv_fourierZ`: for a finitely supported `f` and a kernel `k = invFZ θ M`,
  `∑_n f(n) k(x - n) = invFZ θ (M f̂)`.

The multiplier `m` and the density `H` are arbitrary functions on `ℝ`; only their values on the
chart enter. "`f̂` supported in `I`" is `H β = 0` for `β ∉ I`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-- The sequence with Fourier density `H` on the chart `[θ, θ + 1]`: `x ↦ ∫_θ^{θ+1} H(β) e(xβ) dβ`
(the carrier change of the paper, Source: main paper `s:MFanalysis`, L1861–L1879; for
`H = f̂ = ∑ f(n) e(-nβ)` this is `f`). -/
def invFZ (θ : ℝ) (H : ℝ → ℂ) (x : ℤ) : ℂ := ∫ β in θ..θ + 1, H β * e ((x : ℝ) * β)

/-- The density `H` is square integrable on the chart `(θ, θ + 1]`. -/
abbrev ChartL2 (θ : ℝ) (H : ℝ → ℂ) : Prop := MemLp H 2 (volume.restrict (Set.Ioc θ (θ + 1)))

/-- The `ℓ²(ℤ)` norm `(∑_x |f(x)|²)^{1/2}` as an extended real. -/
def l2enorm (f : ℤ → ℂ) : ℝ≥0∞ := (∑' x : ℤ, ‖f x‖ₑ ^ 2) ^ (1 / 2 : ℝ)

namespace ChartL2

variable {θ : ℝ} {H H' : ℝ → ℂ}

theorem integrableOn (hH : ChartL2 θ H) : IntegrableOn H (Set.Ioc θ (θ + 1)) :=
  hH.integrable (by norm_num)

theorem sub (hH : ChartL2 θ H) (hH' : ChartL2 θ H') : ChartL2 θ (fun β => H β - H' β) :=
  MemLp.sub hH hH'

theorem const_mul (hH : ChartL2 θ H) (c : ℂ) : ChartL2 θ (fun β => c * H β) :=
  hH.const_smul c

/-- A measurable density bounded on the chart is square integrable on it. -/
theorem of_bound {M : ℝ} (hm : AEStronglyMeasurable H (volume.restrict (Set.Ioc θ (θ + 1))))
    (hM : ∀ β ∈ Set.Ioc θ (θ + 1), ‖H β‖ ≤ M) : ChartL2 θ H :=
  MemLp.of_bound hm M ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hM))

/-- A function continuous on the closed chart is square integrable on it. -/
theorem of_continuousOn (hc : ContinuousOn H (Set.Icc θ (θ + 1))) : ChartL2 θ H := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact of_bound (hc.mono Set.Ioc_subset_Icc_self |>.aestronglyMeasurable measurableSet_Ioc)
    fun β hβ => hM β (Set.Ioc_subset_Icc_self hβ)

/-- Pointwise `|m H| ≤ M |H|` (a multiplier bounded by `M` on the support of `H`) maps densities
to densities. -/
theorem mul_of_le {m : ℝ → ℂ} {M : ℝ}
    (hm : AEStronglyMeasurable m (volume.restrict (Set.Ioc θ (θ + 1))))
    (hb : ∀ β, ‖m β * H β‖ ≤ M * ‖H β‖) (hH : ChartL2 θ H) :
    ChartL2 θ (fun β => m β * H β) :=
  MemLp.of_le_mul (c := M) hH (hm.mul hH.aestronglyMeasurable) (Filter.Eventually.of_forall hb)

/-- `H(β) e(xβ)` is integrable on the chart. -/
theorem integrable_mul_e (hH : ChartL2 θ H) (x : ℤ) :
    IntervalIntegrable (fun β => H β * e ((x : ℝ) * β)) volume θ (θ + 1) := by
  have h1 : IntegrableOn (fun β => e ((x : ℝ) * β) * H β) (Set.Ioc θ (θ + 1)) :=
    hH.integrableOn.bdd_mul (c := 1)
      ((continuous_e.comp (by fun_prop)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun β => by rw [norm_e])
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).2 ?_
  refine h1.congr_fun (fun β _ => mul_comm _ _) measurableSet_Ioc

end ChartL2

section Basic

variable {θ : ℝ} {H H' : ℝ → ℂ}

theorem invFZ_add (hH : ChartL2 θ H) (hH' : ChartL2 θ H') (x : ℤ) :
    invFZ θ (fun β => H β + H' β) x = invFZ θ H x + invFZ θ H' x := by
  unfold invFZ
  simp_rw [add_mul]
  exact intervalIntegral.integral_add (hH.integrable_mul_e x) (hH'.integrable_mul_e x)

theorem invFZ_const_mul (c : ℂ) (x : ℤ) :
    invFZ θ (fun β => c * H β) x = c * invFZ θ H x := by
  unfold invFZ
  simp_rw [mul_assoc]
  exact intervalIntegral.integral_const_mul c _

theorem invFZ_sub (hH : ChartL2 θ H) (hH' : ChartL2 θ H') (x : ℤ) :
    invFZ θ (fun β => H β - H' β) x = invFZ θ H x - invFZ θ H' x := by
  have h := invFZ_add hH (hH'.const_mul (-1)) x
  have h2 : (fun β => H β + (-1 : ℂ) * H' β) = fun β => H β - H' β := by
    funext β; ring
  rw [h2, invFZ_const_mul] at h
  rw [h]; ring

/-- The sequence with density `H` is bounded by `∫ |H|`. -/
theorem norm_invFZ_le (x : ℤ) : ‖invFZ θ H x‖ ≤ ∫ β in θ..θ + 1, ‖H β‖ := by
  unfold invFZ
  refine (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans ?_
  refine le_of_eq (intervalIntegral.integral_congr fun β _ => ?_)
  simp [norm_e]

end Basic

/-! ### Parseval -/

/-- **Parseval for the carrier**: for a density `H ∈ L²(θ, θ + 1]`,
`∑_x |invFZ θ H x|² = ∫_θ^{θ+1} |H|²`. -/
theorem hasSum_sq_invFZ {θ : ℝ} {H : ℝ → ℂ} (hH : ChartL2 θ H) :
    HasSum (fun x : ℤ => ‖invFZ θ H x‖ ^ 2) (∫ β in θ..θ + 1, ‖H β‖ ^ 2) := by
  have hab : θ < θ + 1 := by linarith
  have h := hasSum_sq_fourierCoeffOn hab hH
  have h1 : ∀ n : ℤ, fourierCoeffOn hab H n = invFZ θ H (-n) := by
    intro n
    rw [fourierCoeffOn_eq_integral _ _ hab]
    simp only [invFZ, add_sub_cancel_left, div_one, one_smul]
    refine intervalIntegral.integral_congr fun β _ => ?_
    simp only [fourier_coe_apply, smul_eq_mul]
    rw [mul_comm]
    congr 1
    rw [e_eq_exp_mul]
    congr 1
    push_cast
    ring
  simp only [add_sub_cancel_left, inv_one, one_smul] at h
  simp_rw [h1] at h
  exact (Equiv.neg ℤ).hasSum_iff.1 h

/-- Parseval in `ℝ≥0∞` form: `∑_x ‖invFZ θ H x‖ₑ² = ofReal (∫_θ^{θ+1} |H|²)`. -/
theorem tsum_enorm_sq_invFZ {θ : ℝ} {H : ℝ → ℂ} (hH : ChartL2 θ H) :
    ∑' x : ℤ, ‖invFZ θ H x‖ₑ ^ 2 = ENNReal.ofReal (∫ β in θ..θ + 1, ‖H β‖ ^ 2) := by
  have h := hasSum_sq_invFZ hH
  rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun x => by positivity) h.summable]
  refine tsum_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The `ℓ²` norm of a density sequence is the `L²` norm of the density. -/
theorem l2enorm_invFZ {θ : ℝ} {H : ℝ → ℂ} (hH : ChartL2 θ H) :
    l2enorm (invFZ θ H) = ENNReal.ofReal (∫ β in θ..θ + 1, ‖H β‖ ^ 2) ^ (1 / 2 : ℝ) := by
  rw [l2enorm, tsum_enorm_sq_invFZ hH]

/-- The multiplier bound on `ℓ²`: if `|m H| ≤ M |H|` pointwise,
`‖invFZ θ (m H)‖_{ℓ²} ≤ M ‖invFZ θ H‖_{ℓ²}`. -/
theorem l2enorm_invFZ_mul_le {θ : ℝ} {H m : ℝ → ℂ} {M : ℝ} (hM0 : 0 ≤ M)
    (hm : AEStronglyMeasurable m (volume.restrict (Set.Ioc θ (θ + 1))))
    (hb : ∀ β, ‖m β * H β‖ ≤ M * ‖H β‖) (hH : ChartL2 θ H) :
    l2enorm (invFZ θ (fun β => m β * H β)) ≤ ENNReal.ofReal M * l2enorm (invFZ θ H) := by
  have hmH := hH.mul_of_le hm hb
  have hi1 : IntervalIntegrable (fun β => ‖m β * H β‖ ^ 2) volume θ (θ + 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).2
      ((memLp_two_iff_integrable_sq_norm hmH.aestronglyMeasurable).1 hmH)
  have hi2 : IntervalIntegrable (fun β => M ^ 2 * ‖H β‖ ^ 2) volume θ (θ + 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).2
      (((memLp_two_iff_integrable_sq_norm hH.aestronglyMeasurable).1 hH).const_mul _)
  have h1 : ∫ β in θ..θ + 1, ‖m β * H β‖ ^ 2 ≤ M ^ 2 * ∫ β in θ..θ + 1, ‖H β‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith) hi1 hi2 fun β _ => ?_
    calc ‖m β * H β‖ ^ 2 ≤ (M * ‖H β‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hb β) 2
      _ = M ^ 2 * ‖H β‖ ^ 2 := by ring
  rw [l2enorm_invFZ hmH, l2enorm_invFZ hH]
  calc ENNReal.ofReal (∫ β in θ..θ + 1, ‖m β * H β‖ ^ 2) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (M ^ 2 * ∫ β in θ..θ + 1, ‖H β‖ ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h1) (by norm_num)
    _ = ENNReal.ofReal M * ENNReal.ofReal (∫ β in θ..θ + 1, ‖H β‖ ^ 2) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_pow hM0, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num

/-! ### Finitely supported sequences -/

/-- For a finitely supported `f`, the sequence of the density `f̂` on any chart is `f`. -/
theorem invFZ_fourierZ (θ : ℝ) (f : ℤ →₀ ℂ) (x : ℤ) : invFZ θ (fourierZ f) x = f x := by
  have hper : Function.Periodic (fun ξ : ℝ => fourierZ f ξ * e ((x : ℝ) * ξ)) 1 := by
    intro ξ
    have h1 := fourierZ_periodic f ξ
    have h2 : e ((x : ℝ) * (ξ + 1)) = e ((x : ℝ) * ξ) := by
      have := e_add_intCast ((x : ℝ) * ξ) x
      rw [← this]; congr 1; ring
    simp only [h1, h2]
  unfold invFZ
  rw [hper.intervalIntegral_add_eq θ 0, zero_add]
  exact (fourierZ_inversion f x).symm

/-- A density that is a trigonometric polynomial is in `L²`. -/
theorem chartL2_fourierZ (θ : ℝ) (f : ℤ →₀ ℂ) : ChartL2 θ (fourierZ f) :=
  ChartL2.of_continuousOn (continuous_fourierZ f).continuousOn

/-- **Convolution with a kernel given by a density**: for finitely supported `f` and
`k = invFZ θ M` (`M` square integrable on the chart),
`∑_n f(n) k(x - n) = invFZ θ (M f̂)(x)`. -/
theorem invFZ_conv_fourierZ {θ : ℝ} {M : ℝ → ℂ} (hM : ChartL2 θ M) (f : ℤ →₀ ℂ) (x : ℤ) :
    ∑ n ∈ f.support, f n * invFZ θ M (x - n) = invFZ θ (fun β => M β * fourierZ f β) x := by
  have hterm : ∀ n : ℤ, f n * invFZ θ M (x - n) =
      ∫ β in θ..θ + 1, f n * (M β * e (((x - n : ℤ) : ℝ) * β)) := by
    intro n
    unfold invFZ
    rw [← intervalIntegral.integral_const_mul]
  have hint : ∀ n ∈ f.support, IntervalIntegrable
      (fun β => f n * (M β * e (((x - n : ℤ) : ℝ) * β))) volume θ (θ + 1) := fun n _ =>
    (hM.integrable_mul_e (x - n)).const_mul (f n)
  simp_rw [hterm]
  rw [← intervalIntegral.integral_finsetSum hint]
  unfold invFZ
  refine intervalIntegral.integral_congr fun β _ => ?_
  simp only
  rw [fourierZ_eq_sum_of_support_subset f (subset_refl f.support), Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  have : e (((x - n : ℤ) : ℝ) * β) = e ((x : ℝ) * β) * e (-((n : ℝ) * β)) := by
    rw [← e_add]; congr 1; push_cast; ring
  rw [this]; ring

end PrimeCarleson.Proof.Paper

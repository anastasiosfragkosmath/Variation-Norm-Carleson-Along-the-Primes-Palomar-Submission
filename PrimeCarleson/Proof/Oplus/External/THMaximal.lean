module

public import PrimeCarleson.Proof.Common.HardyLittlewoodR
public import PrimeCarleson.Proof.Oplus.Defs.Dyadic
public import PrimeCarleson.Proof.Oplus.Estimates.WavePacketBound
public import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# The superlevel set of the Hardy–Littlewood maximal function of `1_F`

Source: Grafakos–Tao–Terwilleger, L805–L808 and L924–L928.

* `maxSuperlevel F lam = Ω_λ = {M[1_F] > λ}` (the Hardy–Littlewood maximal function of
  `Common/HardyLittlewoodR.lean`, *not* the dyadic one);
* `isOpen_maxSuperlevel`;
* `volume_inter_Icc_le_of_notMem`: `|F ∩ [a, b]| ≤ λ (b - a)` if `a ≤ x ≤ b` and `x ∉ Ω_λ`;
* `ae_mem_maxSuperlevel_of_mem`: for `λ < 1` and `F` measurable, almost every point of `F`
  lies in `Ω_λ` (Lebesgue density, `1_F ≤ M[1_F]` a.e.);
* `integral_indicator_mul_weight_le`: if `x₀ ∈ I` with `x₀ ∉ Ω_λ` then
  `∫_F (1 + |y - c(I)|/|I|)^{-2} dy ≤ 16 λ |I|`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson.Proof.Common

/-- `Ω_λ = {x : M[1_F](x) > λ}`, the superlevel set of the Hardy–Littlewood maximal function of
the indicator of `F` ([O+] L2653-L2660 and the tile-energy bound). -/
def maxSuperlevel (F : Set ℝ) (lam : ℝ) : Set ℝ :=
  {x | ENNReal.ofReal lam < maximalHLR (F.indicator (fun _ => (1 : ℝ))) x}

/-- `Ω_λ` is open (the maximal function is lower semicontinuous). -/
theorem isOpen_maxSuperlevel (F : Set ℝ) (lam : ℝ) : IsOpen (maxSuperlevel F lam) :=
  lowerSemicontinuous_iff_isOpen_preimage.1
    (lowerSemicontinuous_maximalHLR (F.indicator (fun _ => (1 : ℝ)))) _

/-- `Ω_λ` is measurable. -/
theorem measurableSet_maxSuperlevel (F : Set ℝ) (lam : ℝ) : MeasurableSet (maxSuperlevel F lam) :=
  (isOpen_maxSuperlevel F lam).measurableSet

/-- The average of the indicator of `F` over `[a, b]`. -/
theorem laverage_indicator_Icc {F : Set ℝ} (hF : MeasurableSet F) (a b : ℝ) :
    ⨍⁻ y in Icc a b, ‖F.indicator (fun _ => (1 : ℝ)) y‖ₑ ∂volume =
      volume (F ∩ Icc a b) / ENNReal.ofReal (b - a) := by
  rw [laverage_eq, Measure.restrict_apply_univ, Real.volume_Icc]
  congr 1
  have : ∀ y, ‖F.indicator (fun _ => (1 : ℝ)) y‖ₑ = F.indicator (fun _ => (1 : ℝ≥0∞)) y := by
    intro y
    by_cases hy : y ∈ F <;> simp [hy]
  simp_rw [this]
  rw [lintegral_indicator_const hF, one_mul, Measure.restrict_apply hF]

/-- If `x ∉ Ω_λ` and `x ∈ [a, b]` then `|F ∩ [a, b]| ≤ λ (b - a)`. -/
theorem volume_inter_Icc_le_of_notMem {F : Set ℝ} (hF : MeasurableSet F) {lam x a b : ℝ}
    (hlam : 0 ≤ lam) (hx : x ∉ maxSuperlevel F lam) (hxa : a ≤ x) (hxb : x ≤ b) (hab : a < b) :
    volume (F ∩ Icc a b) ≤ ENNReal.ofReal (lam * (b - a)) := by
  have h1 : ⨍⁻ y in Icc a b, ‖F.indicator (fun _ => (1 : ℝ)) y‖ₑ ∂volume ≤
      maximalHLR (F.indicator (fun _ => (1 : ℝ))) x :=
    le_iSup₂_of_le a b <| le_iSup₂_of_le hab ⟨hxa, hxb⟩ le_rfl
  have h2 : maximalHLR (F.indicator (fun _ => (1 : ℝ))) x ≤ ENNReal.ofReal lam := not_lt.1 hx
  rw [laverage_indicator_Icc hF a b] at h1
  have hpos : ENNReal.ofReal (b - a) ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  rw [ENNReal.div_le_iff hpos ENNReal.ofReal_ne_top] at h1
  rw [ENNReal.ofReal_mul hlam]
  exact h1.trans (mul_le_mul_left h2 _)

/-- For `λ < 1`, almost every point of a measurable set `F` lies in `Ω_λ`
(Lebesgue's density theorem: `1_F ≤ M[1_F]` almost everywhere). -/
theorem ae_mem_maxSuperlevel_of_mem {F : Set ℝ} (hF : MeasurableSet F) {lam : ℝ} (hlam : lam < 1) :
    ∀ᵐ x : ℝ, x ∈ F → x ∈ maxSuperlevel F lam := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet
    (volume : Measure ℝ) hF] with x hx hxF
  rw [Set.indicator_of_mem hxF, Pi.one_apply] at hx
  have hlt : ENNReal.ofReal lam < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hlam
  obtain ⟨r, hr, hrpos⟩ := ((hx.eventually (lt_mem_nhds hlt)).and self_mem_nhdsWithin).exists
  have hr0 : 0 < r := hrpos
  rw [Real.closedBall_eq_Icc, Real.volume_Icc] at hr
  have hab : x - r < x + r := by linarith
  have h1 : ⨍⁻ y in Icc (x - r) (x + r), ‖F.indicator (fun _ => (1 : ℝ)) y‖ₑ ∂volume ≤
      maximalHLR (F.indicator (fun _ => (1 : ℝ))) x :=
    le_iSup₂_of_le (x - r) (x + r) <| le_iSup₂_of_le hab ⟨by linarith, by linarith⟩ le_rfl
  rw [laverage_indicator_Icc hF] at h1
  exact lt_of_lt_of_le hr h1

/-! ### Section E: weighted averages are controlled by the maximal function -/

/-- The weight `(1 + |y - c|/L)^{-2}` is dominated by a sum of indicators of the intervals
`[c - 2^n L, c + 2^n L]`. -/
theorem weight_le_tsum_indicator {c L : ℝ} (hL : 0 < L) (y : ℝ) :
    ENNReal.ofReal ((1 + |y - c| / L) ^ (-2 : ℤ)) ≤
      ∑' n : ℕ, (Icc (c - 2 ^ n * L) (c + 2 ^ n * L)).indicator
        (fun _ => ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ n)) y := by
  classical
  set t := |y - c| / L with ht
  have ht0 : 0 ≤ t := by positivity
  have hex : ∃ n : ℕ, t ≤ 2 ^ n := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt t (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, hn.le⟩
  set n₀ := Nat.find hex with hn₀
  have hn₀spec : t ≤ 2 ^ n₀ := Nat.find_spec hex
  have hmem : y ∈ Icc (c - 2 ^ n₀ * L) (c + 2 ^ n₀ * L) := by
    have : |y - c| ≤ 2 ^ n₀ * L := by
      rw [ht, div_le_iff₀ hL] at hn₀spec; exact hn₀spec
    rw [abs_le] at this
    constructor <;> linarith [this.1, this.2]
  refine le_trans ?_ (ENNReal.le_tsum n₀)
  rw [indicator_of_mem hmem]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases Nat.eq_zero_or_pos n₀ with h0 | hpos
  · rw [h0]
    have : (1 + t) ^ (-2 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ (by linarith) (by norm_num)
    simpa using this.trans (by norm_num)
  · obtain ⟨m, hm⟩ : ∃ m, n₀ = m + 1 := ⟨n₀ - 1, by omega⟩
    have hmin : ¬ t ≤ 2 ^ m := Nat.find_min hex (by omega : m < n₀)
    rw [not_le] at hmin
    rw [hm]
    have h2m : (0 : ℝ) < 2 ^ m := by positivity
    have h1 : (2 : ℝ) ^ m ≤ 1 + t := by linarith
    have e : ((2 : ℝ) ^ m) ^ 2 = 4 ^ m := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    calc (1 + t) ^ (-2 : ℤ) = ((1 + t) ^ 2)⁻¹ := by rw [zpow_neg, zpow_ofNat]
      _ ≤ (((2 : ℝ) ^ m) ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ h2m.le h1 2)
      _ = 4 * (1 / 4 : ℝ) ^ (m + 1) := by
          rw [e, pow_succ, one_div, inv_pow]
          field_simp

/-- **Section E in `ℝ≥0∞` form.** If `|F ∩ [c - 2^n L, c + 2^n L]| ≤ λ · 2 · 2^n L` for all `n`
(true when a point of the interval is outside `Ω_λ`, by `volume_inter_Icc_le_of_notMem`), then
`∫_F (1 + |y - c|/L)^{-2} ≤ 16 λ L`. -/
theorem lintegral_indicator_mul_weight_le {F : Set ℝ} {lam c L : ℝ}
    (hlam : 0 ≤ lam) (hL : 0 < L)
    (hgood : ∀ n : ℕ, volume (F ∩ Icc (c - 2 ^ n * L) (c + 2 ^ n * L)) ≤
      ENNReal.ofReal (lam * (2 * (2 ^ n * L)))) :
    ∫⁻ y in F, ENNReal.ofReal ((1 + |y - c| / L) ^ (-2 : ℤ)) ≤ ENNReal.ofReal (16 * lam * L) := by
  calc ∫⁻ y in F, ENNReal.ofReal ((1 + |y - c| / L) ^ (-2 : ℤ))
      ≤ ∫⁻ y in F, ∑' n : ℕ, (Icc (c - 2 ^ n * L) (c + 2 ^ n * L)).indicator
          (fun _ => ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ n)) y :=
        lintegral_mono fun y => weight_le_tsum_indicator hL y
    _ = ∑' n : ℕ, ∫⁻ y in F, (Icc (c - 2 ^ n * L) (c + 2 ^ n * L)).indicator
          (fun _ => ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ n)) y := by
        refine lintegral_tsum fun n => ?_
        exact (measurable_const.indicator measurableSet_Icc).aemeasurable
    _ = ∑' n : ℕ, ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ n) *
          volume (F ∩ Icc (c - 2 ^ n * L) (c + 2 ^ n * L)) := by
        refine tsum_congr fun n => ?_
        rw [lintegral_indicator_const measurableSet_Icc, Measure.restrict_apply measurableSet_Icc,
          inter_comm]
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (8 * lam * L * (1 / 2 : ℝ) ^ n) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        calc ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ n) *
              volume (F ∩ Icc (c - 2 ^ n * L) (c + 2 ^ n * L))
            ≤ ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ n) *
                ENNReal.ofReal (lam * (2 * (2 ^ n * L))) := mul_le_mul' le_rfl (hgood n)
          _ = ENNReal.ofReal (8 * lam * L * (1 / 2 : ℝ) ^ n) := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              congr 1
              have h2 : ((1 : ℝ) / 2) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
              have h4 : (1 / 4 : ℝ) ^ n = ((1 / 2 : ℝ) ^ n) ^ 2 := by
                rw [← pow_mul, mul_comm, pow_mul]; norm_num
              rw [h4]
              calc 4 * ((1 / 2 : ℝ) ^ n) ^ 2 * (lam * (2 * (2 ^ n * L)))
                  = 8 * lam * L * (1 / 2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n * 2 ^ n) := by ring
                _ = 8 * lam * L * (1 / 2 : ℝ) ^ n := by rw [h2]; ring
    _ = ENNReal.ofReal (16 * lam * L) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
          ((summable_geometric_two).mul_left _), tsum_mul_left, tsum_geometric_two]
        congr 1; ring

/-- **Section E** (real form): `∫_F (1 + |y - c|/L)^{-2} dy ≤ 16 λ L`. -/
theorem integral_indicator_mul_weight_le {F : Set ℝ} {lam c L : ℝ}
    (hlam : 0 ≤ lam) (hL : 0 < L)
    (hgood : ∀ n : ℕ, volume (F ∩ Icc (c - 2 ^ n * L) (c + 2 ^ n * L)) ≤
      ENNReal.ofReal (lam * (2 * (2 ^ n * L)))) :
    ∫ y in F, (1 + |y - c| / L) ^ (-2 : ℤ) ≤ 16 * lam * L := by
  have hint : IntegrableOn (fun y : ℝ => (1 + |y - c| / L) ^ (-2 : ℤ)) F := by
    have := integrable_one_add_abs_div_zpow (N := 2) (le_refl 2) c hL
    exact (by simpa using this : Integrable fun y : ℝ => (1 + |y - c| / L) ^ (-2 : ℤ)).integrableOn
  have hnn : 0 ≤ᵐ[volume.restrict F] fun y : ℝ => (1 + |y - c| / L) ^ (-2 : ℤ) :=
    Eventually.of_forall fun y => by positivity
  have h := lintegral_indicator_mul_weight_le hlam hL hgood
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

end PrimeCarleson.Proof.Oplus

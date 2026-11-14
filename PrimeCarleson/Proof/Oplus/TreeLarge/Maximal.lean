module

public import PrimeCarleson.Proof.Common.HardyLittlewoodR
public import PrimeCarleson.Proof.Oplus.SquareFunction.Main

/-!
# A Schwartz mollifier is dominated by the Hardy-Littlewood maximal function ([O+] L2361-L2370)

Source: [O+] `treeestimatelargeintervals`, L2350–L2370
(L2361-L2370: "the variation norm ... is dominated by
averages at scales `≥ |J|`"; the passage from the Schwartz kernel `ψ_{C + log₂|J|}` to the averages
over `(x - R, x + R)`, `R ≥ |J|`, is not written in the source).

* `exists_schwartz_decay_two`: `(1 + |u|)² |ψ(u)| ≤ C_ψ` for a Schwartz function;
* `lintegral_kernel_le_maximalHLR`: `∫ R⁻¹ (1 + |x' - y|/R)^{-2} W(y) dy ≤ 10 M[W](x')` for
  measurable `W ≥ 0` (the kernel is a sum of the indicators of the intervals `|x' - y| < 2^n R` with
  weights `4^{-(n-1)}`, and the average of `W` over an interval containing `x'` is at most
  `M[W](x')`);
* `lintegral_schwartzScale_le_maximalHLR`: for `|x - x'| ≤ 2 · 2^c`,
  `∫ |ψ_c(x - y)| W(y) dy ≤ κ_ψ M[W](x')`, with `κ_ψ = 90 C_ψ` (the kernel at `x` is at most `9`
  times
  the kernel at `x'` since `1 + |x' - y|/R ≤ 3 (1 + |x - y|/R)`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson.Proof.Common

/-- A Schwartz function decays quadratically. -/
theorem exists_schwartz_decay_two (ψ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, (1 + |u|) ^ 2 * ‖ψ u‖ ≤ C := by
  refine ⟨2 ^ 2 * ((Finset.Iic ((2 : ℕ), (0 : ℕ))).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) ψ,
    by positivity, fun u => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((2 : ℕ), (0 : ℕ)))
    (k := 2) (n := 0) le_rfl le_rfl ψ u
  rw [norm_iteratedFDeriv_zero] at h
  exact h

/-- The geometric kernel `R⁻¹ (1 + |x' - y|/R)^{-2}` is dominated by `10 M[W](x')`. -/
theorem lintegral_kernel_le_maximalHLR {R : ℝ} (hR : 0 < R) (x' : ℝ) {W : ℝ → ℝ≥0∞}
    (hW : Measurable W) :
    ∫⁻ y, ENNReal.ofReal (R⁻¹ * (1 + |x' - y| / R) ^ (-2 : ℤ)) * W y ≤
      10 * maximalHLR W x' := by
  set M := maximalHLR W x' with hM
  -- the dyadic majorant
  set b : ℕ → ℝ := fun n => if n = 0 then 1 else (1 / 4 : ℝ) ^ (n - 1) with hb
  have hb_zero : b 0 = 1 := by simp [hb]
  have hb_succ : ∀ n, b (n + 1) = (1 / 4 : ℝ) ^ n := fun n => by simp [hb]
  have hb0 : ∀ n, 0 ≤ b n := fun n => by
    cases n
    · rw [hb_zero]; norm_num
    · rw [hb_succ]; positivity
  set B : ℕ → Set ℝ := fun n => Ioo (x' - 2 ^ n * R) (x' + 2 ^ n * R) with hBdef
  have hBm : ∀ n, MeasurableSet (B n) := fun n => measurableSet_Ioo
  have hpt : ∀ y, ENNReal.ofReal (R⁻¹ * (1 + |x' - y| / R) ^ (-2 : ℤ)) ≤
      ∑' n, ENNReal.ofReal (R⁻¹ * b n) * (B n).indicator (fun _ => (1 : ℝ≥0∞)) y := by
    intro y
    set u : ℝ := |x' - y| / R with hu
    have hu0 : 0 ≤ u := by positivity
    have hmemB : ∀ n : ℕ, u < 2 ^ n → y ∈ B n := by
      intro n hn
      have : |x' - y| < 2 ^ n * R := by
        rw [hu, div_lt_iff₀ hR] at hn; linarith
      rw [abs_lt] at this
      exact ⟨by linarith, by linarith⟩
    rcases lt_or_ge u 1 with h1 | h1
    · refine le_trans ?_ (ENNReal.le_tsum 0)
      have hy : y ∈ B 0 := hmemB 0 (by simpa using h1)
      rw [Set.indicator_of_mem hy, mul_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have : (1 + u) ^ (-2 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ (by linarith) (by norm_num)
      rw [hb_zero]
      nlinarith [inv_pos.2 hR]
    · obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near h1 (by norm_num : (1 : ℝ) < 2)
      refine le_trans ?_ (ENNReal.le_tsum (n + 1))
      have hy : y ∈ B (n + 1) := hmemB (n + 1) hn2
      rw [Set.indicator_of_mem hy, mul_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 : (1 + u) ^ (-2 : ℤ) ≤ (1 / 4 : ℝ) ^ n := by
        have e0 : (1 + u) ^ (-2 : ℤ) = ((1 + u) ^ 2)⁻¹ := by rw [zpow_neg]; norm_cast
        rw [e0]
        have h3 : (4 : ℝ) ^ n ≤ (1 + u) ^ 2 := by
          have h4 : (2 : ℝ) ^ n ≤ u := hn1
          have : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num
          rw [this]
          have : (2 : ℝ) ^ n ≤ 1 + u := by linarith
          exact pow_le_pow_left₀ (by positivity) this 2
        rw [one_div, inv_pow]
        exact inv_anti₀ (by positivity) h3
      rw [hb_succ]
      nlinarith [inv_pos.2 hR]
  -- averages
  have hint : ∀ n : ℕ, ∫⁻ y in B n, W y ≤ ENNReal.ofReal (2 * 2 ^ n * R) * M := by
    intro n
    have hpos : 0 < (2 : ℝ) ^ n * R := by positivity
    have hab : x' - 2 ^ n * R < x' + 2 ^ n * R := by linarith
    have hx : x' ∈ B n := ⟨by linarith, by linarith⟩
    have h := laverage_le_maximalHLR W hab (subset_refl _) Ioo_subset_Icc_self hx
    rw [setLAverage_eq] at h
    simp only [enorm_eq_self] at h
    have hvol : volume (B n) = ENNReal.ofReal (2 * 2 ^ n * R) := by
      rw [hBdef]
      simp only [Real.volume_Ioo]
      congr 1; ring
    have h2 : (volume (B n)) ≠ 0 := by
      rw [hvol]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have h3 : (volume (B n)) ≠ ⊤ := by rw [hvol]; exact ENNReal.ofReal_ne_top
    have h4 := (ENNReal.div_le_iff h2 h3).1 h
    rw [hvol] at h4
    rw [mul_comm]
    exact h4
  have hsumb : ∑' n : ℕ, ENNReal.ofReal (R⁻¹ * b n) * ENNReal.ofReal (2 * 2 ^ n * R) ≤ 10 := by
    have e : ∀ n : ℕ, ENNReal.ofReal (R⁻¹ * b n) * ENNReal.ofReal (2 * 2 ^ n * R) =
        ENNReal.ofReal (2 * b n * 2 ^ n) := by
      intro n
      rw [← ENNReal.ofReal_mul (by have := hb0 n; positivity)]
      congr 1
      field_simp
    simp_rw [e]
    set t : ℕ → ℝ := fun n => 2 * b n * 2 ^ n with ht
    have ht0 : ∀ n, 0 ≤ t n := fun n => by have := hb0 n; simp only [ht]; positivity
    have hts : ∀ n, t (n + 1) = 4 * (1 / 2 : ℝ) ^ n := by
      intro n
      simp only [ht, hb_succ]
      have h1 : (1 / 4 : ℝ) ^ n * 2 ^ n = (1 / 2) ^ n := by rw [← mul_pow]; norm_num
      calc 2 * (1 / 4 : ℝ) ^ n * 2 ^ (n + 1) = 4 * ((1 / 4 : ℝ) ^ n * 2 ^ n) := by ring
        _ = 4 * (1 / 2 : ℝ) ^ n := by rw [h1]
    have hsum : Summable t := by
      rw [← summable_nat_add_iff 1]
      simp_rw [hts]
      exact (summable_geometric_two).mul_left 4
    rw [← ENNReal.ofReal_tsum_of_nonneg ht0 hsum]
    rw [hsum.tsum_eq_zero_add]
    simp_rw [hts]
    rw [tsum_mul_left, tsum_geometric_two]
    have : t 0 = 2 := by simp [ht, hb_zero]
    rw [this]
    have : (2 : ℝ) + 4 * 2 = 10 := by norm_num
    rw [this]
    simp
  calc ∫⁻ y, ENNReal.ofReal (R⁻¹ * (1 + |x' - y| / R) ^ (-2 : ℤ)) * W y
      ≤ ∫⁻ y, (∑' n, ENNReal.ofReal (R⁻¹ * b n) * (B n).indicator (fun _ => (1 : ℝ≥0∞)) y) *
          W y := lintegral_mono fun y => mul_le_mul_left (hpt y) _
    _ = ∫⁻ y, ∑' n, ENNReal.ofReal (R⁻¹ * b n) *
          ((B n).indicator (fun _ => (1 : ℝ≥0∞)) y * W y) := by
        refine lintegral_congr fun y => ?_
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun n => ?_
        ring
    _ = ∑' n, ∫⁻ y, ENNReal.ofReal (R⁻¹ * b n) *
          ((B n).indicator (fun _ => (1 : ℝ≥0∞)) y * W y) :=
        lintegral_tsum fun n => (measurable_const.mul
          ((measurable_const.indicator (hBm n)).mul hW)).aemeasurable
    _ = ∑' n, ENNReal.ofReal (R⁻¹ * b n) * ∫⁻ y in B n, W y := by
        refine tsum_congr fun n => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        rw [← lintegral_indicator (hBm n)]
        refine lintegral_congr fun y => ?_
        by_cases hy : y ∈ B n
        · simp [Set.indicator_of_mem hy]
        · simp [Set.indicator_of_notMem hy]
    _ ≤ ∑' n, ENNReal.ofReal (R⁻¹ * b n) * (ENNReal.ofReal (2 * 2 ^ n * R) * M) :=
        ENNReal.tsum_le_tsum fun n => mul_le_mul_right (hint n) _
    _ = (∑' n : ℕ, ENNReal.ofReal (R⁻¹ * b n) * ENNReal.ofReal (2 * 2 ^ n * R)) * M := by
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun n => ?_
        ring
    _ ≤ 10 * M := mul_le_mul_left hsumb _


/-- **The Schwartz kernel is dominated by the maximal function** (L2361-L2370): for `x, x'` with
`|x - x'| ≤ 2^{c+1}`, `∫ |ψ_c(x - y)| W(y) dy ≤ κ M[W](x')`. -/
theorem lintegral_schwartzScale_le_maximalHLR (ψ : 𝓢(ℝ, ℂ)) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (c : ℤ) {W : ℝ → ℝ≥0∞}, Measurable W → ∀ x x' : ℝ,
      |x - x'| ≤ 2 * (2 : ℝ) ^ c →
        ∫⁻ y, ‖schwartzScale ψ c (x - y)‖ₑ * W y ≤ ENNReal.ofReal κ * maximalHLR W x' := by
  obtain ⟨Cψ, hC0, hC⟩ := exists_schwartz_decay_two ψ
  refine ⟨90 * Cψ, by positivity, fun c W hW x x' hxx => ?_⟩
  set R : ℝ := (2 : ℝ) ^ c with hR
  have hR0 : 0 < R := zpow_pos (by norm_num) _
  have hRinv : (2 : ℝ) ^ (-c) = R⁻¹ := by rw [zpow_neg]
  have hpt : ∀ y, ‖schwartzScale ψ c (x - y)‖ₑ ≤
      ENNReal.ofReal (9 * Cψ) * ENNReal.ofReal (R⁻¹ * (1 + |x' - y| / R) ^ (-2 : ℤ)) := by
    intro y
    have h1 := hC (R⁻¹ * (x - y))
    set u : ℝ := |x - y| / R with hu
    set v : ℝ := |x' - y| / R with hv
    have hu0 : 0 ≤ u := by positivity
    have hv0 : 0 ≤ v := by positivity
    have e1 : |R⁻¹ * (x - y)| = u := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hR0), hu]; field_simp
    rw [e1] at h1
    have h2 : 1 + v ≤ 3 * (1 + u) := by
      have h0 : |x' - y| ≤ |x - y| + |x - x'| := by
        calc |x' - y| = |(x - y) - (x - x')| := by ring_nf
          _ ≤ |x - y| + |x - x'| := abs_sub _ _
      have h3 : v ≤ u + 2 := by
        rw [hu, hv, div_add' _ _ _ hR0.ne', div_le_div_iff_of_pos_right hR0]
        nlinarith [hxx]
      linarith
    have h3 : ‖ψ (R⁻¹ * (x - y))‖ * (1 + v) ^ 2 ≤ 9 * Cψ := by
      have : (1 + v) ^ 2 ≤ 9 * (1 + u) ^ 2 := by
        have := pow_le_pow_left₀ (by linarith) h2 2
        nlinarith
      calc ‖ψ (R⁻¹ * (x - y))‖ * (1 + v) ^ 2 ≤ ‖ψ (R⁻¹ * (x - y))‖ * (9 * (1 + u) ^ 2) :=
            mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = 9 * ((1 + u) ^ 2 * ‖ψ (R⁻¹ * (x - y))‖) := by ring
        _ ≤ 9 * Cψ := by linarith
    have e0 : (1 + v) ^ (-2 : ℤ) = ((1 + v) ^ 2)⁻¹ := by rw [zpow_neg]; norm_cast
    rw [enorm_schwartzScale, hRinv, ← ofReal_norm (ψ _), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [e0]
    have h4 : ‖ψ (R⁻¹ * (x - y))‖ ≤ 9 * Cψ * ((1 + v) ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      exact h3
    have := mul_le_mul_of_nonneg_left h4 (inv_pos.2 hR0).le
    nlinarith
  calc ∫⁻ y, ‖schwartzScale ψ c (x - y)‖ₑ * W y
      ≤ ∫⁻ y, ENNReal.ofReal (9 * Cψ) *
          (ENNReal.ofReal (R⁻¹ * (1 + |x' - y| / R) ^ (-2 : ℤ)) * W y) :=
        lintegral_mono fun y => by
          rw [← mul_assoc]
          exact mul_le_mul_left (hpt y) _
    _ = ENNReal.ofReal (9 * Cψ) *
          ∫⁻ y, ENNReal.ofReal (R⁻¹ * (1 + |x' - y| / R) ^ (-2 : ℤ)) * W y :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (9 * Cψ) * (10 * maximalHLR W x') :=
        mul_le_mul_right (lintegral_kernel_le_maximalHLR hR0 x' hW) _
    _ = ENNReal.ofReal (90 * Cψ) * maximalHLR W x' := by
        have : ENNReal.ofReal (90 * Cψ) = ENNReal.ofReal (9 * Cψ) * 10 := by
          rw [show (90 * Cψ) = (9 * Cψ) * 10 by ring, ENNReal.ofReal_mul (by positivity)]
          simp
        rw [this, mul_assoc]


/-- The variation function `W(y) = V^r_{ℓ ∈ ℤ}(ψ_ℓ * g (y))` of the Schwartz averages. -/
def varW (ψ : ℝ → ℂ) (r : ℝ) (g : ℝ → ℂ) (y : ℝ) : ℝ≥0∞ :=
  rVariationOn r (Set.range ((↑) : ℤ → ℝ)) (fun t => schwartzAvg ψ ⌊t⌋ g y)

/-- **The `L^q` norm of `M[W]` on a set** (L2408-L2424): by Hölder (`q ≤ 2`), the `L²` bound for the
maximal function and [O+] `varestpsi` at `p = 2`, for `g ∈ L²` and every set `U`,
`∫_U (M[V^r_ℓ(ψ_ℓ * g)])^q ≤ A^q ‖g‖₂^q |U|^{1 - q/2}` with `A` depending on `ψ, r` only. -/
theorem lintegral_maximalHLR_varW_le {ψ : 𝓢(ℝ, ℂ)} (hψ : ∫ t, ψ t = 1) {r : ℝ} (hr : 2 < r) :
    ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ {q : ℝ}, 1 ≤ q → q ≤ 2 → ∀ {g : ℝ → ℂ}, MemLp g 2 volume →
      ∀ (U : Set ℝ), ∫⁻ x in U, maximalHLR (varW ψ r g) x ^ q ≤
        A ^ q * eLpNorm g 2 volume ^ q * volume U ^ (1 - q / 2) := by
  obtain ⟨K, hK0, hK⟩ := varestpsi_two_eLpNorm ψ hψ hr
  refine ⟨(maximalHLRConst 2 : ℝ≥0∞) * ENNReal.ofReal K, ENNReal.mul_ne_top (by simp)
    ENNReal.ofReal_ne_top, fun {q} hq1 hq2 {g} hg U => ?_⟩
  have hq0 : 0 < q := by linarith
  set A : ℝ≥0∞ := (maximalHLRConst 2 : ℝ≥0∞) * ENNReal.ofReal K with hA
  set Ng := eLpNorm g 2 volume with hNg
  set h : ℝ → ℝ≥0∞ := maximalHLR (varW ψ r g) with hh
  have hmeas : AEStronglyMeasurable h volume := (measurable_maximalHLR _).aestronglyMeasurable
  have h2 : eLpNorm h 2 volume ≤ A * Ng := by
    calc eLpNorm h 2 volume ≤ (maximalHLRConst 2 : ℝ≥0∞) * eLpNorm (varW ψ r g) 2 volume :=
          eLpNorm_maximalHLR_le (by norm_num) _
      _ ≤ (maximalHLRConst 2 : ℝ≥0∞) * (ENNReal.ofReal K * Ng) := by
          gcongr
          exact hK g hg
      _ = A * Ng := by rw [hA, mul_assoc]
  have hq' : (ENNReal.ofReal q) ≤ 2 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal hq2
  have hmeasU : AEStronglyMeasurable h (volume.restrict U) := hmeas.restrict
  have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict U) hq' hmeasU
  have hheq : ∫⁻ x in U, h x ^ q = eLpNorm h (ENNReal.ofReal q) (volume.restrict U) ^ q := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq0).ne'
      ENNReal.ofReal_ne_top hmeasU, ENNReal.toReal_ofReal hq0.le, ← ENNReal.rpow_mul,
      one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
    simp only [enorm_eq_self]
  rw [hheq]
  have hmono : eLpNorm h 2 (volume.restrict U) ≤ eLpNorm h 2 volume :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  rw [Measure.restrict_apply_univ] at hH
  have hexp : 1 / (ENNReal.ofReal q).toReal - 1 / (2 : ℝ≥0∞).toReal = 1 / q - 1 / 2 := by
    rw [ENNReal.toReal_ofReal hq0.le]; simp
  rw [hexp] at hH
  calc eLpNorm h (ENNReal.ofReal q) (volume.restrict U) ^ q
      ≤ (eLpNorm h 2 (volume.restrict U) * volume U ^ (1 / q - 1 / 2)) ^ q :=
        ENNReal.rpow_le_rpow hH hq0.le
    _ ≤ ((A * Ng) * volume U ^ (1 / q - 1 / 2)) ^ q := by
        gcongr
        exact hmono.trans h2
    _ = A ^ q * Ng ^ q * volume U ^ (1 - q / 2) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
          ← ENNReal.rpow_mul]
        congr 2
        field_simp

end PrimeCarleson.Proof.Oplus

module

public import PrimeCarleson.Frozen.Exp
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.PSeries

/-!
# The cutoff `Φ` and the extension of finitely supported sequences

Helper definitions and lemmas for the Magyar–Stein–Wainger transference
`PrimeCarleson.msw_transference_variation`.

* `cutoff` is a Schwartz function `Φ` whose Fourier transform is `1` on `[-1/2, 1/2]`: it is
  the inverse Fourier transform of a smooth compactly supported bump equal to `1` on
  `[-1/2, 1/2]`.
* `cutoffConst` is the constant `A₁ = max (∫ |Φ|, sup_x ∑_n |Φ(x + n)|)`, finite because
  Schwartz functions decay faster than any polynomial.
* `extend f = ∑ₖ f(k) Φ(· - k)` is the extension of a finitely supported `f : ℤ → ℂ`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap FourierTransform

set_option autoImplicit false

namespace PrimeCarleson.Proof.MswTransference

/-- The real smooth bump equal to `1` on `[-1/2, 1/2]` and supported in `[-1, 1]`. -/
def cutoffBump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

theorem cutoffBump_compactSupport :
    HasCompactSupport (fun x : ℝ => ((cutoffBump x : ℝ) : ℂ)) :=
  cutoffBump.hasCompactSupport.comp_left Complex.ofReal_zero

open scoped ContDiff in
theorem cutoffBump_contDiff : ContDiff ℝ ∞ (fun x : ℝ => ((cutoffBump x : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp cutoffBump.contDiff

/-- The complex-valued bump as a Schwartz function. -/
def cutoffBumpSchwartz : 𝓢(ℝ, ℂ) :=
  cutoffBump_compactSupport.toSchwartzMap cutoffBump_contDiff

theorem cutoffBumpSchwartz_apply (x : ℝ) : cutoffBumpSchwartz x = ((cutoffBump x : ℝ) : ℂ) :=
  rfl

theorem cutoffBumpSchwartz_eq_one {ξ : ℝ} (hξ : |ξ| ≤ 1 / 2) : cutoffBumpSchwartz ξ = 1 := by
  rw [cutoffBumpSchwartz_apply, cutoffBump.one_of_mem_closedBall]
  · simp
  · simpa [cutoffBump, Metric.mem_closedBall, Real.dist_eq] using hξ

/-- The cutoff `Φ`: a Schwartz function with `Φ̂ = 1` on `[-1/2, 1/2]`. -/
def cutoff : 𝓢(ℝ, ℂ) := 𝓕⁻ cutoffBumpSchwartz

theorem fourier_cutoff : 𝓕 cutoff = cutoffBumpSchwartz :=
  FourierInvPair.fourier_fourierInv_eq cutoffBumpSchwartz

/-- The character `𝐞` agrees with `e`. -/
theorem fourierChar_eq_e (t : ℝ) : ((Real.fourierChar t : Circle) : ℂ) = PrimeCarleson.e t := by
  rw [Real.fourierChar_apply, PrimeCarleson.e]
  congr 1
  push_cast
  ring

theorem cutoff_fourier_eq_one {ξ : ℝ} (hξ : |ξ| ≤ 1 / 2) :
    ∫ y, cutoff y * e (-(y * ξ)) = 1 := by
  have h := congrArg (fun g : 𝓢(ℝ, ℂ) => g ξ) fourier_cutoff
  simp only [cutoffBumpSchwartz_eq_one hξ] at h
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Circle.smul_def, smul_eq_mul, fourierChar_eq_e]
  ring

/-- A Schwartz function is bounded by `C / (1 + |y|)^2`. -/
theorem exists_decay_bound (g : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, ‖g y‖ ≤ C / (1 + |y|) ^ 2 := by
  refine ⟨2 ^ 2 * (Finset.Iic ((2, 0) : ℕ × ℕ)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g, by positivity, fun y => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((2, 0) : ℕ × ℕ))
    (k := 2) (n := 0) le_rfl le_rfl g y
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  rw [le_div_iff₀ (by positivity), mul_comm]
  simpa [Real.norm_eq_abs] using h

/-- The weight `1 / (1 + |n|)^2` is summable over `ℤ`. -/
theorem summable_one_div_one_add_abs_sq :
    Summable fun n : ℤ => 1 / (1 + |(n : ℝ)|) ^ 2 := by
  have h1 : Summable fun n : ℕ => 1 / (1 + (n : ℝ)) ^ 2 := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa [add_comm] using this
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using h1
  · simpa using h1

theorem exists_tsum_enorm_add_le (g : 𝓢(ℝ, ℂ)) :
    ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x : ℝ, ∑' n : ℤ, ‖g (x + n)‖ₑ ≤ B := by
  obtain ⟨C, hC0, hC⟩ := exists_decay_bound g
  have hsum : Summable fun n : ℤ => 4 * C * (1 / (1 + |(n : ℝ)|) ^ 2) :=
    summable_one_div_one_add_abs_sq.mul_left _
  refine ⟨ENNReal.ofReal (∑' n : ℤ, 4 * C * (1 / (1 + |(n : ℝ)|) ^ 2)), ENNReal.ofReal_lt_top,
    fun x => ?_⟩
  obtain ⟨t, ht0, ht1, ht⟩ : ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ t = x - ⌊x⌋ :=
    ⟨Int.fract x, Int.fract_nonneg x, Int.fract_lt_one x, rfl⟩
  calc ∑' n : ℤ, ‖g (x + n)‖ₑ
      = ∑' n : ℤ, ‖g (t + n)‖ₑ := by
        rw [← (Equiv.subRight ⌊x⌋).tsum_eq (fun n : ℤ => ‖g (x + n)‖ₑ)]
        refine tsum_congr fun n => ?_
        rw [Equiv.subRight_apply, show x + ((n - ⌊x⌋ : ℤ) : ℝ) = t + n by rw [ht]; push_cast; ring]
    _ ≤ ∑' n : ℤ, ENNReal.ofReal (4 * C * (1 / (1 + |(n : ℝ)|) ^ 2)) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        rw [← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        refine (hC (t + n)).trans ?_
        have h1 : 1 + |(n : ℝ)| ≤ 2 * (1 + |t + n|) := by
          have := abs_sub_abs_le_abs_sub (n : ℝ) (t + n)
          have h2 : |(n : ℝ) - (t + n)| = t := by
            rw [show (n : ℝ) - (t + n) = -t by ring, abs_neg, abs_of_nonneg ht0]
          nlinarith [abs_nonneg (t + n)]
        have h3 : (1 + |(n : ℝ)|) ^ 2 ≤ 4 * (1 + |t + n|) ^ 2 := by
          nlinarith [abs_nonneg (n : ℝ), abs_nonneg (t + n)]
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    _ = ENNReal.ofReal (∑' n : ℤ, 4 * C * (1 / (1 + |(n : ℝ)|) ^ 2)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum).symm

/-- The constant `A₁ = max(∫|Φ|, sup_x ∑_n |Φ(x + n)|)`. -/
def cutoffConst : ℝ≥0∞ :=
  max (∫⁻ y, ‖cutoff y‖ₑ) (⨆ x : ℝ, ∑' n : ℤ, ‖cutoff (x + n)‖ₑ)

theorem cutoffConst_lt_top : cutoffConst < ∞ := by
  refine max_lt cutoff.integrable.hasFiniteIntegral ?_
  obtain ⟨B, hB, h⟩ := exists_tsum_enorm_add_le cutoff
  exact lt_of_le_of_lt (iSup_le h) hB

/-- The extension of a finitely supported `f : ℤ → ℂ` by the cutoff. -/
def extend (f : ℤ →₀ ℂ) : 𝓢(ℝ, ℂ) :=
  f.sum fun k c => c • cutoff.compSubConstCLM ℂ (k : ℝ)

theorem extend_apply (f : ℤ →₀ ℂ) (x : ℝ) :
    extend f x = f.sum fun k c => c * cutoff (x - k) := by
  simp [extend, Finsupp.sum]

end PrimeCarleson.Proof.MswTransference

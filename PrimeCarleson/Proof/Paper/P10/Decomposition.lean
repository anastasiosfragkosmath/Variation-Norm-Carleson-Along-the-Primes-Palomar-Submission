module

public import PrimeCarleson.Proof.Paper.P10.Identity
public import PrimeCarleson.Proof.Paper.P9.LocalBound

/-!
# The frequency decomposition `F_R` of `f` and the almost-orthogonality bound

Source: main paper `p:transferprop`, L2220–L2237.

The pieces `F_R` (`winDens N u f R`, the density `1_{I_u} f̂(· + R/N)`) have Fourier support in
`I_u` and satisfy `∑_R ‖F_R‖²_{ℓ²} ≤ ‖f‖²_{ℓ²}`: since `|I_u| < 1/N` the translates
`I_u + R/N`, `0 ≤ R < N`, are disjoint inside `[a, a + 1)` (the bounded overlap which the paper
leaves unwritten is therefore `1`, with the sharp cutoff).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-- The squared `L²` norm of the density `F̂_R` over the chart is the integral over `I_u + R/N`. -/
theorem integral_norm_sq_winDens {N : ℕ} (hN : 0 < N) (u : ℝ) (f : ℤ →₀ ℂ) (R : Fin N) :
    ∫ β in winChart u..winChart u + 1, ‖winDens N u f R β‖ ^ 2 =
      ∫ g in winLo N u + ((R : ℕ) : ℝ) / N..winHi N u + ((R : ℕ) : ℝ) / N, ‖fourierZ f g‖ ^ 2 := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlo : winChart u < winLo N u := by
    unfold winChart winLo
    have : 1 / (100 * (N : ℝ)) ≤ 1 / 100 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hhi : winHi N u < winChart u + 1 := by
    unfold winChart winHi
    have h1 : 1 / (2 * (N : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have h2 : 1 / (100 * (N : ℝ)) ≤ 1 / 100 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hab : winLo N u ≤ winHi N u := by
    have := winHi_sub_winLo hN u
    have h0 : (0 : ℝ) < 13 / (25 * N) := by positivity
    linarith
  rw [← intervalIntegral.integral_comp_add_right (fun g => ‖fourierZ f g‖ ^ 2)]
  rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le hab]
  have hind : ∀ β : ℝ, ‖winDens N u f R β‖ ^ 2 =
      (Set.Icc (winLo N u) (winHi N u)).indicator
        (fun β => ‖fourierZ f (β + ((R : ℕ) : ℝ) / N)‖ ^ 2) β := by
    intro β
    by_cases hβ : β ∈ Set.Icc (winLo N u) (winHi N u)
    · simp only [winDens, hβ, ite_true, Set.indicator_of_mem hβ]
    · simp only [winDens_eq_zero R hβ, Set.indicator_of_notMem hβ, norm_zero]
      norm_num
  simp_rw [hind]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Icc]
  have hsub : Set.Ioc (winChart u) (winChart u + 1) ∩ Set.Icc (winLo N u) (winHi N u) =
      Set.Icc (winLo N u) (winHi N u) :=
    Set.inter_eq_right.2 fun β hβ => ⟨by linarith [hβ.1], by linarith [hβ.2]⟩
  rw [hsub, integral_Icc_eq_integral_Ioc]

/-- **Almost-orthogonality of the pieces `F_R`** (L2220–L2237): `∑_R ‖F_R‖²_{ℓ²} ≤ ‖f‖²_{ℓ²}`, in
the form `famNorm ≤ ‖f‖`. -/
theorem famNorm_winDens_le {N : ℕ} (hN : 0 < N) (u : ℝ) (f : ℤ →₀ ℂ) :
    famNorm (winChart u) (winDens N u f) ≤ l2enorm (⇑f) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hg : Continuous fun g : ℝ => ‖fourierZ f g‖ ^ 2 := (continuous_fourierZ f).norm.pow 2
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun g : ℝ => ‖fourierZ f g‖ ^ 2) volume a b :=
    fun a b => hg.intervalIntegrable _ _
  have hlen := winHi_sub_winLo_lt hN u
  have hI : ∀ R : Fin N, ∑' x : ℤ, ‖invFZ (winChart u) (winDens N u f R) x‖ₑ ^ 2 =
      ENNReal.ofReal (∫ β in winChart u..winChart u + 1, ‖winDens N u f R β‖ ^ 2) :=
    fun R => tsum_enorm_sq_invFZ (chartL2_winDens N u f R _)
  have hnn : ∀ R : Fin N, 0 ≤ ∫ β in winChart u..winChart u + 1, ‖winDens N u f R β‖ ^ 2 := by
    intro R
    refine intervalIntegral.integral_nonneg (by unfold winChart; linarith) fun β _ => by positivity
  -- the sum of the integrals
  have hsum : ∑ R : Fin N, ∫ β in winChart u..winChart u + 1, ‖winDens N u f R β‖ ^ 2 ≤
      ∑ k ∈ f.support, ‖f k‖ ^ 2 := by
    rw [sum_norm_sq_eq_integral_shift f (winLo N u)]
    simp_rw [integral_norm_sq_winDens hN u f]
    rw [Fin.sum_univ_eq_sum_range (fun R : ℕ => ∫ g in winLo N u + (R : ℝ) / N..
      winHi N u + (R : ℝ) / N, ‖fourierZ f g‖ ^ 2) N]
    calc ∑ R ∈ Finset.range N, ∫ g in winLo N u + (R : ℝ) / N..winHi N u + (R : ℝ) / N,
          ‖fourierZ f g‖ ^ 2
        ≤ ∑ R ∈ Finset.range N, ∫ g in winLo N u + (R : ℝ) / N..winLo N u + ((R + 1 : ℕ) : ℝ) / N,
          ‖fourierZ f g‖ ^ 2 := by
          refine Finset.sum_le_sum fun R _ => ?_
          refine intervalIntegral.integral_mono_interval le_rfl ?_ ?_
            (Filter.Eventually.of_forall fun g => by positivity) (hint _ _)
          · have : (0 : ℝ) ≤ 13 / (25 * N) := by positivity
            have h2 := winHi_sub_winLo hN u
            linarith
          · push_cast
            have : winLo N u + ((R : ℝ) + 1) / N = winLo N u + (R : ℝ) / N + 1 / N := by
              field_simp
              ring
            rw [this]
            linarith
      _ = ∫ g in winLo N u..winLo N u + 1, ‖fourierZ f g‖ ^ 2 := by
          have := intervalIntegral.sum_integral_adjacent_intervals
            (f := fun g : ℝ => ‖fourierZ f g‖ ^ 2) (μ := volume)
            (a := fun k : ℕ => winLo N u + (k : ℝ) / N) (n := N) (fun k _ => hint _ _)
          have h0 : winLo N u + ((0 : ℕ) : ℝ) / N = winLo N u := by simp
          have hN' : winLo N u + ((N : ℕ) : ℝ) / N = winLo N u + 1 := by
            rw [div_self hNR.ne']
          rw [h0, hN'] at this
          exact this
  unfold famNorm
  simp_rw [hI]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun R _ => hnn R)]
  calc (ENNReal.ofReal (∑ R : Fin N, ∫ β in winChart u..winChart u + 1, ‖winDens N u f R β‖ ^ 2)) ^
        (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (∑ k ∈ f.support, ‖f k‖ ^ 2)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hsum) (by norm_num)
    _ = l2enorm (⇑f) := by rw [l2enorm, tsum_enorm_sq_finsupp]

end PrimeCarleson.Proof.Paper

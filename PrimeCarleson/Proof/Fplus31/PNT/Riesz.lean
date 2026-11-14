module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Mellin transform of the Riesz kernel

Part of the prime number theorem in progressions (`PNTSW/Perron.lean` generalises it to every line
`re s = σ > 1`). The Riesz kernel `W(u) = max (1 - u) 0` has Mellin transform `1/(s(s+1))` for
`re s > 0`, whence Mellin inversion returns `W` exactly (no truncation error):

* `rieszW`, `rieszW_continuous`;
* `mellin_rieszW`: `mellin W s = 1/(s(s+1))`;
* `rieszW_mellinConvergent`: the Mellin transform converges on every line `re s = σ > 0`, a
  hypothesis of `mellinInv_mellin_eq`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Complex Real

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- the Riesz kernel -/
noncomputable def rieszW (u : ℝ) : ℝ := max (1 - u) 0

theorem rieszW_continuous : Continuous rieszW := by
  unfold rieszW; fun_prop

theorem mellin_rieszW (s : ℂ) (hs : 0 < s.re) :
    mellin (fun u : ℝ => (rieszW u : ℂ)) s = 1 / (s * (s + 1)) := by
  have hmem : ∀ u ∈ Ioi (0 : ℝ), ((u : ℂ) ^ (s - 1)) • (rieszW u : ℂ) =
      Set.indicator (Ioc (0 : ℝ) 1) (fun u : ℝ => (u : ℂ) ^ (s - 1) - (u : ℂ) ^ s) u := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    by_cases h1 : u ≤ 1
    · have hmu : u ∈ Ioc (0 : ℝ) 1 := ⟨hu0, h1⟩
      simp only [Set.indicator_of_mem hmu]
      have : rieszW u = 1 - u := by unfold rieszW; exact max_eq_left (by linarith)
      rw [this, smul_eq_mul]
      have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
      have : (u : ℂ) ^ s = (u : ℂ) ^ (s - 1) * u := by
        calc (u : ℂ) ^ s = (u : ℂ) ^ ((s - 1) + 1) := by ring_nf
          _ = (u : ℂ) ^ (s - 1) * (u : ℂ) ^ (1 : ℂ) := Complex.cpow_add _ _ hu'
          _ = (u : ℂ) ^ (s - 1) * u := by rw [Complex.cpow_one]
      rw [this]; push_cast; ring
    · have hnu : u ∉ Ioc (0 : ℝ) 1 := fun h => h1 h.2
      simp only [Set.indicator_of_notMem hnu]
      have : rieszW u = 0 := by unfold rieszW; exact max_eq_right (by linarith [not_le.mp h1])
      rw [this]; simp
  unfold mellin
  rw [setIntegral_congr_fun measurableSet_Ioi hmem, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, Set.inter_eq_left.mpr Set.Ioc_subset_Ioi_self]
  have hint : ∀ r : ℂ, 0 < r.re + 1 →
      ∫ u in Ioc (0 : ℝ) 1, (u : ℂ) ^ r = 1 / (r + 1) := by
    intro r hr
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_cpow (Or.inl (by linarith))]
    have hr0 : r + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    simp only [Complex.ofReal_one, Complex.ofReal_zero, Complex.one_cpow, Complex.zero_cpow hr0]
    simp
  have hI1 : IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ (s - 1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)
  have hI2 : IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ s) volume 0 1 :=
    intervalIntegral.intervalIntegrable_cpow' (by linarith)
  rw [integral_sub (hI1.1) (hI2.1)]
  rw [hint (s - 1) (by simp; linarith), hint s (by linarith), show s - 1 + 1 = s by ring]
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hs1 : s + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  field_simp
  ring


theorem rieszW_mellinConvergent (σ : ℝ) (hσ : 0 < σ) :
    MellinConvergent (fun u : ℝ => (rieszW u : ℂ)) (σ : ℂ) := by
  have hcont : Continuous (fun u : ℝ => (rieszW u : ℂ)) :=
    Complex.continuous_ofReal.comp rieszW_continuous
  have htop : (fun u : ℝ => (rieszW u : ℂ)) =O[Filter.atTop]
      (fun x : ℝ => x ^ (-(σ + 1))) := by
    refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have : rieszW x = 0 := by unfold rieszW; exact max_eq_right (by linarith)
    simp [this]
  have hbot : (fun u : ℝ => (rieszW u : ℂ)) =O[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => x ^ (-(0 : ℝ))) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with x hx
    have : rieszW x = 1 - x := by unfold rieszW; exact max_eq_left (by linarith [hx.2])
    simp only [this, Complex.norm_real, Real.norm_eq_abs, neg_zero, Real.rpow_zero, norm_one,
      mul_one]
    rw [abs_of_nonneg (by linarith [hx.2])]
    linarith [hx.1]
  exact mellinConvergent_of_isBigO_rpow (a := σ + 1) (b := 0)
    (hcont.continuousOn.locallyIntegrableOn measurableSet_Ioi) htop (by simp) hbot
    (by simpa using hσ)

end PrimeCarleson.Proof.Fplus31

module

public import Carleson.ToMathlib.RealInterpolation.Main
public import Carleson.ToMathlib.LorentzType
public import PrimeCarleson.Proof.Common.Interpolation

/-!
# Marcinkiewicz interpolation from restricted weak-type bounds

Source: [O+] L879–L880: "by interpolation it suffices to prove for `p ≥ r'` the restricted weak
type bound" (used in the interpolation step of the proof of [O+] Theorem 1.2).

For `0 < p₀ < p₁ < ∞`, `0 < θ < 1`, `1/p = (1-θ)/p₀ + θ/p₁` and an operator `T` that is
subadditive on a class `P` closed under truncation (`MeasureTheory.trunc`, `truncCompl`) and
satisfies the restricted weak-type bounds `‖T f‖_{L^{p_i,∞}} ≤ M_i ‖f‖_{L^{p_i,1}}`
(`wnorm`, `eLorentzNorm · · 1` of the vendored Carleson project, `M_i > 0`), we prove

`‖T f‖_{L^p} ≤ C(p₀, p₁, p, θ) M₀^{1-θ} M₁^θ ‖f‖_{L^p}`

(`eLpNorm_le_interpolation_of_restricted`), with the explicit constant `restrictedInterpConst`,
finite by `restrictedInterpConst_ne_top`.

The vendored Lean Carleson project has no Lorentz-space interpolation theorem (the upstream
`LorentzInterpolation.lean` has three unproved declarations and is not vendored).  The proof
reduces to the vendored Marcinkiewicz theorem for weak-type bounds
(`eLpNorm_le_interpolation_of_truncClosed` of `PrimeCarleson.Proof.Common.Interpolation`) in two
steps:

1. *Restricted to weak type at intermediate exponents.* For `p₀ < a < p₁` and `f ∈ L^a`, split
   `f = f 1_{|f| ≤ s} + f 1_{|f| > s}` at the height `s = λ τ` (`τ` a level of `T f`), bound the
   Lorentz norms `‖f 1_{|f| > s}‖_{p₀,1}` and `‖f 1_{|f| ≤ s}‖_{p₁,1}` by the layer cake formula
   `‖g‖_{p,1} = p ∫₀^∞ d_g(t)^{1/p} dt` and the Chebyshev bound `d_f(t) ≤ (‖f‖_a / t)^a`
   (`eLorentzNorm_truncCompl_le`, `eLorentzNorm_trunc_le`; the power-law integrals are
   `lintegral_nnreal_max_inv_rpow`, `lintegral_nnreal_Iio_inv_rpow`), apply the restricted
   bounds to the two pieces (`distribution_le_of_restricted`), and choose the balancing height
   `M₀^{p₀} λ^{p₀} = M₁^{p₁} λ^{p₁}` to obtain
   `‖T f‖_{L^{a,∞}} ≤ 2 (K_a M₀^{p₀} λ^{p₀-a})^{1/a} ‖f‖_{L^a}` (`wnorm_le_of_restricted`).
2. *Marcinkiewicz between `a₀ < p < a₁`.* With `1/a₀ = (1-θ/2)/p₀ + (θ/2)/p₁`,
   `1/a₁ = ((1-θ)/2)/p₀ + ((1+θ)/2)/p₁` (`interA0`, `interA1`) the parameter of `p` between `a₀`
   and `a₁` is again `θ`, and the exponents of `M₀`, `M₁` in the two weak-type constants combine
   to `1 - θ`, `θ` (`balance_final`, `W_product`).

The hypotheses `h₀`, `h₁` are only used for the two truncations `trunc f s`, `truncCompl f s` of
the function `f` itself, which is why a general class `P` closed under truncation is allowed.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Common

/-! ### Coefficients -/

/-- The coefficient `(a/p)/(a/p - 1)` of the bound for `‖f^{>s}‖_{p,1}`. -/
def kAbove (p a : ℝ) : ℝ := (a / p) / (a / p - 1)

/-- The coefficient `1/(1 - a/p)` of the bound for `‖f^{≤s}‖_{p,1}`. -/
def kBelow (p a : ℝ) : ℝ := 1 / (1 - a / p)

/-! ### Power-law integrals over `ℝ≥0` -/

section Integrals

/-- The tail integral `∫₀^∞ (max s t)^{-γ} dt = s^{1-γ} γ / (γ - 1)` for `γ > 1`. -/
theorem lintegral_nnreal_max_inv_rpow {γ : ℝ} (hγ : 1 < γ) {s : ℝ≥0} (hs : 0 < s) :
    ∫⁻ t : ℝ≥0, (max (s : ℝ≥0∞) t)⁻¹ ^ γ =
      ENNReal.ofReal ((s : ℝ) ^ (1 - γ) * (γ / (γ - 1))) := by
  have hs' : (0 : ℝ) < s := hs
  rw [lintegral_nnreal_eq_lintegral_Ioi_ofReal (f := fun v => (max (s : ℝ≥0∞) v)⁻¹ ^ γ)]
  have hfun : ∀ x ∈ Ioi (0 : ℝ), (max (s : ℝ≥0∞) (ENNReal.ofReal x))⁻¹ ^ γ =
      ENNReal.ofReal (max (s : ℝ) x ^ (-γ)) := by
    intro x hx
    have hx' : (0 : ℝ) < x := hx
    have hm : 0 < max (s : ℝ) x := lt_max_of_lt_left hs'
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_max, ← ENNReal.ofReal_inv_of_pos hm,
      ENNReal.ofReal_rpow_of_pos (inv_pos.2 hm), Real.rpow_neg hm.le, Real.inv_rpow hm.le]
  rw [setLIntegral_congr_fun measurableSet_Ioi hfun]
  rw [← Ioc_union_Ioi_eq_Ioi hs'.le, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  have h1 : ∫⁻ x in Ioc (0 : ℝ) s, ENNReal.ofReal (max (s : ℝ) x ^ (-γ)) =
      ENNReal.ofReal ((s : ℝ) ^ (-γ) * s) := by
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => ENNReal.ofReal ((s : ℝ) ^ (-γ)))]
    · rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
    · intro x hx
      simp only [max_eq_left hx.2]
  have h2 : ∫⁻ x in Ioi (s : ℝ), ENNReal.ofReal (max (s : ℝ) x ^ (-γ)) =
      ENNReal.ofReal ((s : ℝ) ^ (-γ + 1) / |(-γ) + 1|) := by
    rw [← lintegral_Ioi_rpow_of_lt_abs hs' (by linarith)]
    refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp only [max_eq_right (le_of_lt (mem_Ioi.1 hx))]
  rw [h1, h2, ← ENNReal.ofReal_add (by positivity)]
  · congr 1
    have hγ1 : γ - 1 ≠ 0 := by linarith
    have habs : |(-γ) + 1| = γ - 1 := by rw [abs_of_neg (by linarith)]; ring
    have e1 : (s : ℝ) ^ (-γ) * s = (s : ℝ) ^ (1 - γ) := by
      rw [show (1 - γ) = (-γ) + 1 by ring, Real.rpow_add hs', Real.rpow_one]
    rw [habs, e1, show -γ + 1 = 1 - γ by ring]
    field_simp
    ring
  · exact div_nonneg (Real.rpow_nonneg hs'.le _) (abs_nonneg _)

/-- The head integral `∫₀^s t^{-γ} dt = s^{1-γ} / (1 - γ)` for `γ < 1`. -/
theorem lintegral_nnreal_Iio_inv_rpow {γ : ℝ} (hγ : γ < 1) {s : ℝ≥0} (hs : 0 < s) :
    ∫⁻ t : ℝ≥0, (Iio (s : ℝ≥0∞)).indicator (fun v => v⁻¹ ^ γ) t =
      ENNReal.ofReal ((s : ℝ) ^ (1 - γ) / (1 - γ)) := by
  have hs' : (0 : ℝ) < s := hs
  rw [lintegral_nnreal_eq_lintegral_Ioi_ofReal
    (f := (Iio (s : ℝ≥0∞)).indicator (fun v => v⁻¹ ^ γ))]
  have hfun : ∀ x ∈ Ioi (0 : ℝ), (Iio (s : ℝ≥0∞)).indicator (fun v => v⁻¹ ^ γ)
      (ENNReal.ofReal x) = (Iio (s : ℝ)).indicator (fun x => ENNReal.ofReal (x ^ (-γ))) x := by
    intro x hx
    have hx' : (0 : ℝ) < x := hx
    by_cases hxs : x < s
    · have : ENNReal.ofReal x ∈ Iio (s : ℝ≥0∞) := by
        rw [mem_Iio, ← ENNReal.ofReal_coe_nnreal]
        exact (ENNReal.ofReal_lt_ofReal_iff hs').2 hxs
      rw [indicator_of_mem this, indicator_of_mem (mem_Iio.2 hxs),
        ← ENNReal.ofReal_inv_of_pos hx', ENNReal.ofReal_rpow_of_pos (inv_pos.2 hx'),
        Real.rpow_neg hx'.le, Real.inv_rpow hx'.le]
    · have : ENNReal.ofReal x ∉ Iio (s : ℝ≥0∞) := by
        rw [mem_Iio, not_lt, ← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal (not_lt.1 hxs)
      rw [indicator_of_notMem this, indicator_of_notMem (by simpa using hxs)]
  rw [setLIntegral_congr_fun measurableSet_Ioi hfun,
    setLIntegral_indicator measurableSet_Iio, Iio_inter_Ioi,
    lintegral_rpow_of_gt hs'.le (by linarith)]
  congr 1
  rw [show -γ + 1 = 1 - γ by ring]

end Integrals

/-! ### Distribution functions of truncations and Lorentz norms -/

section Lorentz

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [TopologicalSpace E]
  [ESeminormedAddMonoid E]

/-- The distribution function of the complement of a truncation: the level set
`{t < ‖f^{>s}‖}` is contained in `{max s t < ‖f‖}`. -/
theorem distribution_truncCompl_le (f : α → E) (s t : ℝ≥0∞) :
    distribution (truncCompl f s) t μ ≤ distribution f (max s t) μ := by
  refine measure_mono fun x hx => ?_
  rw [mem_ofPred_eq] at hx ⊢
  rw [truncCompl_eq] at hx
  by_cases h : s < ‖f x‖ₑ
  · simp only [h, ite_true] at hx
    exact max_lt h hx
  · simp [h] at hx

/-- The distribution function of a truncation vanishes above the truncation height and is bounded
by that of `f` below it. -/
theorem distribution_trunc_le (f : α → E) (s t : ℝ≥0∞) :
    distribution (trunc f s) t μ ≤ (Iio s).indicator (fun v => distribution f v μ) t := by
  by_cases hts : t < s
  · rw [indicator_of_mem (mem_Iio.2 hts)]
    exact measure_mono fun x hx => lt_of_lt_of_le hx trunc_le_func
  · rw [indicator_of_notMem (by simpa using hts)]
    have h0 : {x | t < ‖trunc f s x‖ₑ} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      exact (trunc_le x).trans (max_le zero_le (not_lt.1 hts))
    change μ {x | t < ‖trunc f s x‖ₑ} ≤ _
    rw [h0]
    simp

/-- Layer-cake bound for the Lorentz norm `L^{p,1}`: a bound `d_g(t) ≤ B(t)` for the distribution
function gives `‖g‖_{L^{p,1}} ≤ p ∫₀^∞ B(t)^{1/p} dt`. -/
theorem eLorentzNorm_one_le_of_distribution_le {g : α → E} (hg : AEStronglyMeasurable g μ)
    {p : ℝ} (hp : 0 < p) {B : ℝ≥0 → ℝ≥0∞} (hB : ∀ t : ℝ≥0, 0 < t → distribution g t μ ≤ B t) :
    eLorentzNorm g (ENNReal.ofReal p) 1 μ ≤ ENNReal.ofReal p * ∫⁻ t : ℝ≥0, B t ^ p⁻¹ := by
  rw [eLorentzNorm_eq_eLorentzNorm' (ENNReal.ofReal_pos.2 hp).ne' ENNReal.ofReal_ne_top hg,
    eLorentzNorm'_eq_integral_distribution_rpow, ENNReal.toReal_ofReal hp.le]
  refine mul_le_mul_right ?_ _
  rw [lintegral_nnreal_eq_lintegral_toNNReal_Ioi,
    lintegral_nnreal_eq_lintegral_toNNReal_Ioi (fun t => B t ^ p⁻¹)]
  refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
  gcongr
  exact hB _ (Real.toNNReal_pos.2 hx)

/-- The Chebyshev bound `d_f(v) ≤ v^{-a} ‖f‖_a^a` for `f ∈ L^a`, `0 < v < ∞`. -/
theorem distribution_le_inv_rpow_mul {f : α → E} {a : ℝ} (ha : 0 < a) {v : ℝ≥0∞} (hv0 : v ≠ 0)
    (hvt : v ≠ ⊤) :
    distribution f v μ ≤ v⁻¹ ^ a * eLpNorm f (ENNReal.ofReal a) μ ^ a := by
  have := distribution_le_mul_pow_eLpNorm_enorm (μ := μ) (p := ENNReal.ofReal a)
    (ENNReal.ofReal_pos.2 ha).ne' ENNReal.ofReal_ne_top (f := f) (ε := v) hv0
    (fun h => absurd h hvt)
  rwa [ENNReal.toReal_ofReal ha.le] at this

/-- **`L^{p,1}` norm of the part of `f ∈ L^a` above height `s`**, for `p < a`:
`‖f 1_{|f| > s}‖_{L^{p,1}} ≤ p ‖f‖_a^{a/p} s^{1-a/p} (a/p)/(a/p - 1)`. -/
theorem eLorentzNorm_truncCompl_le {f : α → E} {p a : ℝ} (hp : 0 < p) (hpa : p < a)
    (hf : MemLp f (ENNReal.ofReal a) μ) {s : ℝ≥0} (hs : 0 < s) :
    eLorentzNorm (truncCompl f s) (ENNReal.ofReal p) 1 μ ≤
      ENNReal.ofReal p * (eLpNorm f (ENNReal.ofReal a) μ ^ (a / p) *
        ENNReal.ofReal ((s : ℝ) ^ (1 - a / p) * ((a / p) / (a / p - 1)))) := by
  have ha : 0 < a := hp.trans hpa
  have hγ : 1 < a / p := by rw [lt_div_iff₀ hp]; linarith
  set N := eLpNorm f (ENNReal.ofReal a) μ with hN
  have hNt : N ≠ ⊤ := hf.eLpNorm_lt_top.ne
  refine (eLorentzNorm_one_le_of_distribution_le hf.aestronglyMeasurable.truncCompl hp
    (B := fun t => (max (s : ℝ≥0∞) t)⁻¹ ^ a * N ^ a) ?_).trans ?_
  · intro t ht
    refine (distribution_truncCompl_le f s t).trans ?_
    refine distribution_le_inv_rpow_mul ha ?_ ?_
    · simp [hs.ne']
    · simp
  · refine le_of_eq ?_
    congr 1
    have hpt : ∀ t : ℝ≥0, ((max (s : ℝ≥0∞) t)⁻¹ ^ a * N ^ a) ^ p⁻¹ =
        N ^ (a / p) * (max (s : ℝ≥0∞) t)⁻¹ ^ (a / p) := by
      intro t
      rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hp.le), ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul, mul_comm, div_eq_inv_mul]
      ring_nf
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) hNt),
      lintegral_nnreal_max_inv_rpow hγ hs]

/-- **`L^{p,1}` norm of the part of `f ∈ L^a` up to height `s`**, for `a < p`:
`‖f 1_{|f| ≤ s}‖_{L^{p,1}} ≤ p ‖f‖_a^{a/p} s^{1-a/p} / (1 - a/p)`. -/
theorem eLorentzNorm_trunc_le {f : α → E} {p a : ℝ} (ha : 0 < a) (hap : a < p)
    (hf : MemLp f (ENNReal.ofReal a) μ) {s : ℝ≥0} (hs : 0 < s) :
    eLorentzNorm (trunc f s) (ENNReal.ofReal p) 1 μ ≤
      ENNReal.ofReal p * (eLpNorm f (ENNReal.ofReal a) μ ^ (a / p) *
        ENNReal.ofReal ((s : ℝ) ^ (1 - a / p) / (1 - a / p))) := by
  have hp : 0 < p := ha.trans hap
  have hγ : a / p < 1 := by rw [div_lt_one hp]; exact hap
  set N := eLpNorm f (ENNReal.ofReal a) μ with hN
  have hNt : N ≠ ⊤ := hf.eLpNorm_lt_top.ne
  refine (eLorentzNorm_one_le_of_distribution_le hf.aestronglyMeasurable.trunc hp
    (B := fun t => (Iio (s : ℝ≥0∞)).indicator (fun v => v⁻¹ ^ a * N ^ a) t) ?_).trans ?_
  · intro t ht
    refine (distribution_trunc_le f s t).trans ?_
    by_cases hm : (t : ℝ≥0∞) ∈ Iio (s : ℝ≥0∞)
    · rw [indicator_of_mem hm, indicator_of_mem hm]
      exact distribution_le_inv_rpow_mul ha (by simpa using ht.ne') (by simp)
    · rw [indicator_of_notMem hm, indicator_of_notMem hm]
  · refine le_of_eq ?_
    congr 1
    have hpt : ∀ t : ℝ≥0, (Iio (s : ℝ≥0∞)).indicator (fun v => v⁻¹ ^ a * N ^ a) t ^ p⁻¹ =
        N ^ (a / p) * (Iio (s : ℝ≥0∞)).indicator (fun v => v⁻¹ ^ (a / p)) t := by
      intro t
      by_cases h : (t : ℝ≥0∞) ∈ Iio (s : ℝ≥0∞)
      · rw [indicator_of_mem h, indicator_of_mem h,
          ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hp.le), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul, mul_comm, div_eq_inv_mul]
        ring_nf
      · rw [indicator_of_notMem h, indicator_of_notMem h, ENNReal.zero_rpow_of_pos (inv_pos.2 hp),
          mul_zero]
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) hNt),
      lintegral_nnreal_Iio_inv_rpow hγ hs]

end Lorentz

/-! ### From restricted weak type at the endpoints to weak type in between -/

section StepA

variable {α α' E₁ E₂ : Type*} [MeasurableSpace α] [MeasurableSpace α'] {μ : Measure α}
  {ν : Measure α'} [TopologicalSpace E₁] [ESeminormedAddMonoid E₁] [TopologicalSpace E₂]
  [ESeminormedAddMonoid E₂]

/-- A weak-`L^q` bound `‖g‖_{L^{q,∞}} ≤ X` gives `d_g(τ) ≤ (X / τ)^q`. -/
theorem distribution_le_of_wnorm_le {g : α' → E₂} (hg : AEStronglyMeasurable g ν) {q : ℝ}
    (hq : 0 < q) {X : ℝ≥0∞} (h : wnorm g (ENNReal.ofReal q) ν ≤ X) {τ : ℝ≥0} (hτ : 0 < τ) :
    distribution g τ ν ≤ (X / τ) ^ q := by
  rw [wnorm_eq_iSup_mul_distribution_rpow hg (ENNReal.ofReal_pos.2 hq).ne'
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq.le] at h
  have h1 : (τ : ℝ≥0∞) * distribution g τ ν ^ q⁻¹ ≤ X :=
    le_trans (le_iSup (fun t : ℝ≥0 => (t : ℝ≥0∞) * distribution g t ν ^ q⁻¹) τ) h
  have h2 : distribution g τ ν ^ q⁻¹ ≤ X / τ := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hτ.ne')) (Or.inl (by simp)), mul_comm]
    exact h1
  calc distribution g τ ν = (distribution g τ ν ^ q⁻¹) ^ q := by
        rw [ENNReal.rpow_inv_rpow hq.ne']
    _ ≤ (X / τ) ^ q := ENNReal.rpow_le_rpow h2 hq.le

/-- **Distribution bound from restricted weak-type bounds at two exponents** (the splitting step of
the Marcinkiewicz argument): for `0 < p₀ < a < p₁`, `T` subadditive on a class `P` closed under
truncation with `L^{p_i,1} → L^{p_i,∞}` bounds `M_i`, `f ∈ P ∩ L^a` and heights `τ, s > 0`,
`d_{Tf}(2τ) ≤ (M₀ ‖f^{>s}‖_{p₀,1} / τ)^{p₀} + (M₁ ‖f^{≤s}‖_{p₁,1} / τ)^{p₁}`, with the two Lorentz
norms bounded in terms of `‖f‖_a` and `s`. -/
theorem distribution_le_of_restricted (P : (α → E₁) → Prop)
    (hPt : ∀ f (s : ℝ≥0∞), P f → P (trunc f s))
    (hPc : ∀ f (s : ℝ≥0∞), P f → P (truncCompl f s))
    {p₀ p₁ a : ℝ} (hp₀ : 0 < p₀) (hp₀a : p₀ < a) (hap₁ : a < p₁) {M₀ M₁ : ℝ≥0}
    (T : (α → E₁) → α' → E₂) (hmeas : ∀ f, P f → AEStronglyMeasurable (T f) ν)
    (hsub : ∀ f g, P f → P g → ∀ᵐ x ∂ν, ‖T (f + g) x‖ₑ ≤ ‖T f x‖ₑ + ‖T g x‖ₑ)
    (h₀ : ∀ f, P f → MemLorentz f (ENNReal.ofReal p₀) 1 μ →
      wnorm (T f) (ENNReal.ofReal p₀) ν ≤ M₀ * eLorentzNorm f (ENNReal.ofReal p₀) 1 μ)
    (h₁ : ∀ f, P f → MemLorentz f (ENNReal.ofReal p₁) 1 μ →
      wnorm (T f) (ENNReal.ofReal p₁) ν ≤ M₁ * eLorentzNorm f (ENNReal.ofReal p₁) 1 μ)
    {f : α → E₁} (hf : P f) (hfa : MemLp f (ENNReal.ofReal a) μ) {τ s : ℝ≥0} (hτ : 0 < τ)
    (hs : 0 < s) :
    distribution (T f) ((τ : ℝ≥0∞) + τ) ν ≤
      ((M₀ : ℝ≥0∞) * (ENNReal.ofReal p₀ * (eLpNorm f (ENNReal.ofReal a) μ ^ (a / p₀) *
        ENNReal.ofReal ((s : ℝ) ^ (1 - a / p₀) * kAbove p₀ a))) / τ) ^ p₀ +
      ((M₁ : ℝ≥0∞) * (ENNReal.ofReal p₁ * (eLpNorm f (ENNReal.ofReal a) μ ^ (a / p₁) *
        ENNReal.ofReal ((s : ℝ) ^ (1 - a / p₁) * kBelow p₁ a))) / τ) ^ p₁ := by
  have ha : 0 < a := hp₀.trans hp₀a
  have hp₁ : 0 < p₁ := ha.trans hap₁
  have hNt : eLpNorm f (ENNReal.ofReal a) μ ≠ ⊤ := hfa.eLpNorm_lt_top.ne
  set g₁ := truncCompl f s with hg₁
  set g₂ := trunc f s with hg₂
  have hg₁P : P g₁ := hPc f s hf
  have hg₂P : P g₂ := hPt f s hf
  have hB₁ := eLorentzNorm_truncCompl_le hp₀ hp₀a hfa hs
  have hB₂ := eLorentzNorm_trunc_le ha hap₁ hfa hs
  simp only [div_eq_mul_one_div ((s : ℝ) ^ (1 - a / p₁))] at hB₂
  change eLorentzNorm g₂ (ENNReal.ofReal p₁) 1 μ ≤ ENNReal.ofReal p₁ *
    (eLpNorm f (ENNReal.ofReal a) μ ^ (a / p₁) *
      ENNReal.ofReal ((s : ℝ) ^ (1 - a / p₁) * kBelow p₁ a)) at hB₂
  have hlt₁ : MemLorentz g₁ (ENNReal.ofReal p₀) 1 μ := by
    refine lt_of_le_of_lt hB₁ ?_
    have : 0 < a / p₀ := div_pos ha hp₀
    finiteness
  have hlt₂ : MemLorentz g₂ (ENNReal.ofReal p₁) 1 μ := by
    refine lt_of_le_of_lt hB₂ ?_
    have : 0 < a / p₁ := div_pos ha hp₁
    finiteness
  have hd₁ := distribution_le_of_wnorm_le (hmeas g₁ hg₁P) hp₀
    ((h₀ g₁ hg₁P hlt₁).trans (mul_le_mul_right hB₁ _)) hτ
  have hd₂ := distribution_le_of_wnorm_le (hmeas g₂ hg₂P) hp₁
    ((h₁ g₂ hg₂P hlt₂).trans (mul_le_mul_right hB₂ _)) hτ
  have hsum := hsub g₂ g₁ hg₂P hg₁P
  rw [hg₂, hg₁, trunc_add_truncCompl] at hsum
  have hsum' : ∀ᵐ x ∂ν, ‖T f x‖ₑ ≤ 1 * (‖T g₁ x‖ₑ + ‖T g₂ x‖ₑ) := by
    filter_upwards [hsum] with x hx
    rw [one_mul, add_comm]
    exact hx
  have := distribution_add_le_of_enorm (A := 1) (t := (τ : ℝ≥0∞)) (s := (τ : ℝ≥0∞)) hsum'
  rw [one_mul] at this
  exact this.trans (add_le_add hd₁ hd₂)

end StepA

/-! ### The real-variable algebra -/

section Algebra

/-- The exponent-dependent constant `K_a = (p₀ k_>)^{p₀} + (p₁ k_≤)^{p₁}` of the weak-type bound at
the intermediate exponent `a`. -/
def restrictedK (p₀ p₁ a : ℝ) : ℝ :=
  (p₀ * kAbove p₀ a) ^ p₀ + (p₁ * kBelow p₁ a) ^ p₁

theorem kAbove_pos {p a : ℝ} (hp : 0 < p) (hpa : p < a) : 0 < kAbove p a := by
  have h1 : 1 < a / p := by rw [lt_div_iff₀ hp]; linarith
  exact div_pos (by linarith) (by linarith)

theorem kBelow_pos {p a : ℝ} (ha : 0 < a) (hap : a < p) : 0 < kBelow p a := by
  have hp : 0 < p := ha.trans hap
  have h1 : a / p < 1 := by rw [div_lt_one hp]; exact hap
  exact one_div_pos.2 (by linarith)

theorem restrictedK_pos {p₀ p₁ a : ℝ} (hp₀ : 0 < p₀) (hp₀a : p₀ < a) (hap₁ : a < p₁) :
    0 < restrictedK p₀ p₁ a := by
  have ha : 0 < a := hp₀.trans hp₀a
  have hp₁ : 0 < p₁ := ha.trans hap₁
  unfold restrictedK
  have := kAbove_pos hp₀ hp₀a
  have := kBelow_pos ha hap₁
  positivity

/-- One summand: `(M c N^{a/q} (λ τ)^{1-a/q} / τ)^q = (M c)^q N^a λ^{q-a} τ^{-a}`. -/
theorem single_term_eq {M c N l τ q a : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c) (hN : 0 ≤ N) (hl : 0 < l)
    (hτ : 0 < τ) (hq : 0 < q) :
    (M * (c * (N ^ (a / q) * ((l * τ) ^ (1 - a / q)))) / τ) ^ q =
      (M * c) ^ q * N ^ a * l ^ (q - a) * τ ^ (-a) := by
  have hlτ : 0 < l * τ := mul_pos hl hτ
  have e1 : M * (c * (N ^ (a / q) * ((l * τ) ^ (1 - a / q)))) / τ =
      (M * c) * (N ^ (a / q) * ((l * τ) ^ (1 - a / q))) / τ := by ring
  rw [e1, Real.div_rpow (by positivity) hτ.le, Real.mul_rpow (mul_nonneg hM hc) (by positivity),
    Real.mul_rpow (Real.rpow_nonneg hN _) (Real.rpow_nonneg hlτ.le _), ← Real.rpow_mul hN,
    ← Real.rpow_mul hlτ.le, Real.mul_rpow hl.le hτ.le]
  have e2 : a / q * q = a := by field_simp
  have e3 : (1 - a / q) * q = q - a := by field_simp
  rw [e2, e3]
  have e4 : τ ^ (q - a) = τ ^ (-a) * τ ^ q := by
    rw [← Real.rpow_add hτ]; congr 1; ring
  rw [e4]
  have : τ ^ q ≠ 0 := (Real.rpow_pos_of_pos hτ q).ne'
  field_simp

/-- Balancing the two summands (`M₀^{p₀} λ^{p₀} = M₁^{p₁} λ^{p₁}`) at height `s = λ τ` gives
`term₀ + term₁ = K_a (M₀^{p₀} λ^{p₀-a}) N^a τ^{-a}`. -/
theorem two_terms_eq {p₀ p₁ a M₀ M₁ N l τ : ℝ} (hp₀ : 0 < p₀) (hp₀a : p₀ < a) (hap₁ : a < p₁)
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (hN : 0 ≤ N) (hl : 0 < l) (hτ : 0 < τ)
    (hbal : M₀ ^ p₀ * l ^ p₀ = M₁ ^ p₁ * l ^ p₁) :
    (M₀ * (p₀ * (N ^ (a / p₀) * ((l * τ) ^ (1 - a / p₀) * kAbove p₀ a))) / τ) ^ p₀ +
      (M₁ * (p₁ * (N ^ (a / p₁) * ((l * τ) ^ (1 - a / p₁) * kBelow p₁ a))) / τ) ^ p₁ =
      restrictedK p₀ p₁ a * (M₀ ^ p₀ * l ^ (p₀ - a)) * N ^ a * τ ^ (-a) := by
  have ha : 0 < a := hp₀.trans hp₀a
  have hp₁ : 0 < p₁ := ha.trans hap₁
  have hk₀ := kAbove_pos hp₀ hp₀a
  have hk₁ := kBelow_pos ha hap₁
  have e₀ : M₀ * (p₀ * (N ^ (a / p₀) * ((l * τ) ^ (1 - a / p₀) * kAbove p₀ a))) =
      M₀ * ((p₀ * kAbove p₀ a) * (N ^ (a / p₀) * ((l * τ) ^ (1 - a / p₀)))) := by ring
  have e₁ : M₁ * (p₁ * (N ^ (a / p₁) * ((l * τ) ^ (1 - a / p₁) * kBelow p₁ a))) =
      M₁ * ((p₁ * kBelow p₁ a) * (N ^ (a / p₁) * ((l * τ) ^ (1 - a / p₁)))) := by ring
  rw [e₀, e₁, single_term_eq hM₀.le (by positivity) hN hl hτ hp₀,
    single_term_eq hM₁.le (by positivity) hN hl hτ hp₁,
    Real.mul_rpow hM₀.le (by positivity), Real.mul_rpow hM₁.le (by positivity)]
  have hb : M₁ ^ p₁ * l ^ (p₁ - a) = M₀ ^ p₀ * l ^ (p₀ - a) := by
    rw [Real.rpow_sub hl, Real.rpow_sub hl, ← mul_div_assoc, ← mul_div_assoc, hbal]
  unfold restrictedK
  have : M₁ ^ p₁ * (p₁ * kBelow p₁ a) ^ p₁ * N ^ a * l ^ (p₁ - a) * τ ^ (-a) =
      (p₁ * kBelow p₁ a) ^ p₁ * (M₁ ^ p₁ * l ^ (p₁ - a)) * N ^ a * τ ^ (-a) := by ring
  rw [this, hb]
  ring

/-- The balancing identity: with `M₀^{p₀} λ^{p₀} = M₁^{p₁} λ^{p₁}`, `1/p = (1-θ)/p₀ + θ/p₁` and
`1/p = (1-θ)/a₀ + θ/a₁`, one has
`(M₀^{p₀} λ^{p₀-a₀})^{(1-θ)/a₀} (M₀^{p₀} λ^{p₀-a₁})^{θ/a₁} = M₀^{1-θ} M₁^θ`. -/
theorem balance_final {p₀ p₁ p θ a₀ a₁ M₀ M₁ l : ℝ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (hl : 0 < l)
    (hpp : 1 / p = (1 - θ) / p₀ + θ / p₁) (hpa : 1 / p = (1 - θ) / a₀ + θ / a₁)
    (hbal : M₀ ^ p₀ * l ^ p₀ = M₁ ^ p₁ * l ^ p₁) :
    (M₀ ^ p₀ * l ^ (p₀ - a₀)) ^ ((1 - θ) / a₀) * (M₀ ^ p₀ * l ^ (p₀ - a₁)) ^ (θ / a₁) =
      M₀ ^ (1 - θ) * M₁ ^ θ := by
  have h1 : (M₀ ^ p₀ * l ^ (p₀ - a₀)) ^ ((1 - θ) / a₀) * (M₀ ^ p₀ * l ^ (p₀ - a₁)) ^ (θ / a₁) =
      M₀ ^ (p₀ * (1 / p)) * l ^ (p₀ * (1 / p) - 1) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hM₀.le _) (Real.rpow_nonneg hl.le _),
      Real.mul_rpow (Real.rpow_nonneg hM₀.le _) (Real.rpow_nonneg hl.le _),
      ← Real.rpow_mul hM₀.le, ← Real.rpow_mul hM₀.le, ← Real.rpow_mul hl.le,
      ← Real.rpow_mul hl.le]
    have eM : p₀ * ((1 - θ) / a₀) + p₀ * (θ / a₁) = p₀ * (1 / p) := by rw [hpa]; ring
    have el : (p₀ - a₀) * ((1 - θ) / a₀) + (p₀ - a₁) * (θ / a₁) = p₀ * (1 / p) - 1 := by
      rw [hpa]; field_simp; ring
    calc _ = (M₀ ^ (p₀ * ((1 - θ) / a₀)) * M₀ ^ (p₀ * (θ / a₁))) *
          (l ^ ((p₀ - a₀) * ((1 - θ) / a₀)) * l ^ ((p₀ - a₁) * (θ / a₁))) := by ring
      _ = _ := by rw [← Real.rpow_add hM₀, ← Real.rpow_add hl, eM, el]
  have hx : M₀ ^ (p₀ * (θ / p₁)) * l ^ (p₀ * (θ / p₁)) = M₁ ^ θ * l ^ θ := by
    have : (M₀ ^ p₀ * l ^ p₀) ^ (θ / p₁) = (M₁ ^ p₁ * l ^ p₁) ^ (θ / p₁) := by rw [hbal]
    rw [Real.mul_rpow (Real.rpow_nonneg hM₀.le _) (Real.rpow_nonneg hl.le _),
      Real.mul_rpow (Real.rpow_nonneg hM₁.le _) (Real.rpow_nonneg hl.le _),
      ← Real.rpow_mul hM₀.le, ← Real.rpow_mul hl.le, ← Real.rpow_mul hM₁.le,
      ← Real.rpow_mul hl.le, mul_div_cancel₀ _ hp₁.ne'] at this
    exact this
  have hu : l ^ (p₀ * (1 / p) - 1) = l ^ (p₀ * (θ / p₁)) / l ^ θ := by
    rw [← Real.rpow_sub hl]
    congr 1
    rw [hpp]
    field_simp
    ring
  have hMpos : 0 < M₀ ^ (p₀ * (θ / p₁)) := Real.rpow_pos_of_pos hM₀ _
  have hlθ : 0 < l ^ θ := Real.rpow_pos_of_pos hl _
  have hl2 : l ^ (p₀ * (θ / p₁)) = M₁ ^ θ * l ^ θ / M₀ ^ (p₀ * (θ / p₁)) := by
    rw [eq_div_iff hMpos.ne']
    rw [← hx]; ring
  have hexp : p₀ * (1 / p) - p₀ * (θ / p₁) = 1 - θ := by
    rw [hpp]; field_simp; ring
  rw [h1, hu, hl2]
  have e2 : M₀ ^ (p₀ * (1 / p)) = M₀ ^ (1 - θ) * M₀ ^ (p₀ * (θ / p₁)) := by
    rw [← Real.rpow_add hM₀]; congr 1; linarith
  rw [e2]
  field_simp

/-- Assembling the two endpoint constants: `W₀^{1-θ} W₁^θ` for `W_j = 2 (K_j R_j)^{1/a_j}`. -/
theorem W_product {K₀ K₁ R₀ R₁ a₀ a₁ θ : ℝ} (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (hR₀ : 0 < R₀)
    (hR₁ : 0 < R₁) :
    (2 * (K₀ * R₀) ^ a₀⁻¹) ^ (1 - θ) * (2 * (K₁ * R₁) ^ a₁⁻¹) ^ θ =
      (2 * K₀ ^ ((1 - θ) / a₀) * K₁ ^ (θ / a₁)) * (R₀ ^ ((1 - θ) / a₀) * R₁ ^ (θ / a₁)) := by
  have hKR₀ : 0 ≤ K₀ * R₀ := (mul_pos hK₀ hR₀).le
  have hKR₁ : 0 ≤ K₁ * R₁ := (mul_pos hK₁ hR₁).le
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hKR₀ _),
    Real.mul_rpow (by norm_num) (Real.rpow_nonneg hKR₁ _), ← Real.rpow_mul hKR₀,
    ← Real.rpow_mul hKR₁, Real.mul_rpow hK₀.le hR₀.le, Real.mul_rpow hK₁.le hR₁.le,
    inv_mul_eq_div, inv_mul_eq_div]
  have h2 : (2 : ℝ) ^ (1 - θ) * 2 ^ θ = 2 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  calc _ = ((2 : ℝ) ^ (1 - θ) * 2 ^ θ) * K₀ ^ ((1 - θ) / a₀) * K₁ ^ (θ / a₁) *
        (R₀ ^ ((1 - θ) / a₀) * R₁ ^ (θ / a₁)) := by ring
    _ = _ := by rw [h2]

end Algebra

/-- The intermediate exponent `a₀` with `1/a₀ = (1 - θ/2)/p₀ + (θ/2)/p₁`. -/
def interA0 (p₀ p₁ θ : ℝ) : ℝ := ((1 - θ / 2) / p₀ + (θ / 2) / p₁)⁻¹

/-- The intermediate exponent `a₁` with `1/a₁ = ((1 - θ)/2)/p₀ + ((1 + θ)/2)/p₁`. -/
def interA1 (p₀ p₁ θ : ℝ) : ℝ := (((1 - θ) / 2) / p₀ + ((1 + θ) / 2) / p₁)⁻¹

section Exponents2

variable {p₀ p₁ θ : ℝ}

theorem interA0_bounds (hp₀ : 0 < p₀) (hp : p₀ < p₁) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    p₀ < interA0 p₀ p₁ θ ∧ interA0 p₀ p₁ θ < p₁ := by
  have hp₁ : 0 < p₁ := hp₀.trans hp
  have hv : 1 / p₁ < 1 / p₀ := one_div_lt_one_div_of_lt hp₀ hp
  have e : (1 - θ / 2) / p₀ + (θ / 2) / p₁ = (1 - θ / 2) * (1 / p₀) + (θ / 2) * (1 / p₁) := by
    ring
  have hApos : 0 < (1 - θ / 2) / p₀ + (θ / 2) / p₁ :=
    add_pos (div_pos (by linarith) hp₀) (div_pos (by linarith) hp₁)
  have hv0 : 0 < 1 / p₁ := by positivity
  unfold interA0
  constructor
  · refine (lt_inv_comm₀ hp₀ hApos).2 ?_
    rw [e, ← one_div]
    nlinarith
  · refine (inv_lt_comm₀ hApos hp₁).2 ?_
    rw [e, ← one_div]
    nlinarith

theorem interA1_bounds (hp₀ : 0 < p₀) (hp : p₀ < p₁) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    p₀ < interA1 p₀ p₁ θ ∧ interA1 p₀ p₁ θ < p₁ := by
  have hp₁ : 0 < p₁ := hp₀.trans hp
  have hv : 1 / p₁ < 1 / p₀ := one_div_lt_one_div_of_lt hp₀ hp
  have e : ((1 - θ) / 2) / p₀ + ((1 + θ) / 2) / p₁ =
      ((1 - θ) / 2) * (1 / p₀) + ((1 + θ) / 2) * (1 / p₁) := by ring
  have hApos : 0 < ((1 - θ) / 2) / p₀ + ((1 + θ) / 2) / p₁ :=
    add_pos (div_pos (by linarith) hp₀) (div_pos (by linarith) hp₁)
  have hv0 : 0 < 1 / p₁ := by positivity
  unfold interA1
  constructor
  · refine (lt_inv_comm₀ hp₀ hApos).2 ?_
    rw [e, ← one_div]
    nlinarith
  · refine (inv_lt_comm₀ hApos hp₁).2 ?_
    rw [e, ← one_div]
    nlinarith

theorem interA_ne (hp₀ : 0 < p₀) (hp : p₀ < p₁) : interA0 p₀ p₁ θ ≠ interA1 p₀ p₁ θ := by
  have hp₁ : 0 < p₁ := hp₀.trans hp
  have hv : 1 / p₁ < 1 / p₀ := one_div_lt_one_div_of_lt hp₀ hp
  unfold interA0 interA1
  intro h
  have h2 := inv_injective h
  have : (1 - θ / 2) / p₀ + (θ / 2) / p₁ - (((1 - θ) / 2) / p₀ + ((1 + θ) / 2) / p₁) =
      (1 / 2) * (1 / p₀ - 1 / p₁) := by ring
  rw [h2, sub_self] at this
  linarith

/-- The interpolation parameter of `p` between `a₀` and `a₁` is `θ`:
`(1-θ)/a₀ + θ/a₁ = (1-θ)/p₀ + θ/p₁`. -/
theorem interA_combine : (1 - θ) / interA0 p₀ p₁ θ + θ / interA1 p₀ p₁ θ =
    (1 - θ) / p₀ + θ / p₁ := by
  unfold interA0 interA1
  rw [div_inv_eq_mul, div_inv_eq_mul]
  ring

end Exponents2

/-! ### The weak-type bound at an intermediate exponent -/

section StepA2

variable {α α' E₁ E₂ : Type*} [MeasurableSpace α] [MeasurableSpace α'] {μ : Measure α}
  {ν : Measure α'} [TopologicalSpace E₁] [ESeminormedAddMonoid E₁] [TopologicalSpace E₂]
  [ESeminormedAddMonoid E₂]

/-- An extended-real expression built from finite data, as the `ofReal` of a real expression. -/
theorem ennreal_term_eq {M : ℝ≥0} {N : ℝ≥0∞} (hN : N ≠ ⊤) {p γ q y : ℝ} (hp : 0 < p)
    (hγ : 0 < γ) (hq : 0 < q) (hy : 0 ≤ y) {τ : ℝ≥0} (hτ : 0 < τ) :
    ((M : ℝ≥0∞) * (ENNReal.ofReal p * (N ^ γ * ENNReal.ofReal y)) / (τ : ℝ≥0∞)) ^ q =
      ENNReal.ofReal (((M : ℝ) * (p * (N.toReal ^ γ * y)) / (τ : ℝ)) ^ q) := by
  have h1 : N ^ γ = ENNReal.ofReal (N.toReal ^ γ) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hγ.le, ENNReal.ofReal_toReal hN]
  have hτ' : (0 : ℝ) < τ := by exact_mod_cast hτ
  have hA : 0 ≤ N.toReal ^ γ := Real.rpow_nonneg ENNReal.toReal_nonneg _
  rw [h1, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hp.le,
    ← ENNReal.ofReal_coe_nnreal (p := M), ← ENNReal.ofReal_mul (NNReal.coe_nonneg M),
    ← ENNReal.ofReal_coe_nnreal (p := τ), ← ENNReal.ofReal_div_of_pos hτ',
    ENNReal.ofReal_rpow_of_nonneg (by positivity) hq.le]

/-- **Weak type at an intermediate exponent from restricted weak-type bounds at the endpoints**
(the Marcinkiewicz splitting argument, with the splitting height `s = λ τ` balancing the two
endpoints): if `M₀^{p₀} λ^{p₀} = M₁^{p₁} λ^{p₁}`, `0 < p₀ < a < p₁`, then for `f ∈ P ∩ L^a`,
`‖T f‖_{L^{a,∞}} ≤ 2 (K_a M₀^{p₀} λ^{p₀-a})^{1/a} ‖f‖_{L^a}`. -/
theorem wnorm_le_of_restricted (P : (α → E₁) → Prop)
    (hPt : ∀ f (s : ℝ≥0∞), P f → P (trunc f s))
    (hPc : ∀ f (s : ℝ≥0∞), P f → P (truncCompl f s))
    {p₀ p₁ a : ℝ} (hp₀ : 0 < p₀) (hp₀a : p₀ < a) (hap₁ : a < p₁) {M₀ M₁ : ℝ≥0}
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (T : (α → E₁) → α' → E₂) (hmeas : ∀ f, P f → AEStronglyMeasurable (T f) ν)
    (hsub : ∀ f g, P f → P g → ∀ᵐ x ∂ν, ‖T (f + g) x‖ₑ ≤ ‖T f x‖ₑ + ‖T g x‖ₑ)
    (h₀ : ∀ f, P f → MemLorentz f (ENNReal.ofReal p₀) 1 μ →
      wnorm (T f) (ENNReal.ofReal p₀) ν ≤ M₀ * eLorentzNorm f (ENNReal.ofReal p₀) 1 μ)
    (h₁ : ∀ f, P f → MemLorentz f (ENNReal.ofReal p₁) 1 μ →
      wnorm (T f) (ENNReal.ofReal p₁) ν ≤ M₁ * eLorentzNorm f (ENNReal.ofReal p₁) 1 μ)
    {l : ℝ≥0} (hl : 0 < l) (hbal : (M₀ : ℝ) ^ p₀ * (l : ℝ) ^ p₀ = (M₁ : ℝ) ^ p₁ * (l : ℝ) ^ p₁)
    {f : α → E₁} (hf : P f) (hfa : MemLp f (ENNReal.ofReal a) μ) :
    wnorm (T f) (ENNReal.ofReal a) ν ≤
      ENNReal.ofReal (2 * (restrictedK p₀ p₁ a * ((M₀ : ℝ) ^ p₀ * (l : ℝ) ^ (p₀ - a))) ^ a⁻¹) *
        eLpNorm f (ENNReal.ofReal a) μ := by
  have ha : 0 < a := hp₀.trans hp₀a
  have hp₁ : 0 < p₁ := ha.trans hap₁
  have hNt : eLpNorm f (ENNReal.ofReal a) μ ≠ ⊤ := hfa.eLpNorm_lt_top.ne
  set N := eLpNorm f (ENNReal.ofReal a) μ with hN
  have hKpos := restrictedK_pos hp₀ hp₀a hap₁
  have hk₀ := kAbove_pos hp₀ hp₀a
  have hk₁ := kBelow_pos ha hap₁
  have hRpos : 0 < (M₀ : ℝ) ^ p₀ * (l : ℝ) ^ (p₀ - a) :=
    mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast hM₀) _)
      (Real.rpow_pos_of_pos (by exact_mod_cast hl) _)
  rw [wnorm_eq_iSup_mul_distribution_rpow (hmeas f hf) (ENNReal.ofReal_pos.2 ha).ne'
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal ha.le]
  refine iSup_le fun t => ?_
  rcases eq_zero_or_pos t with rfl | ht
  · simp
  set τ : ℝ≥0 := t / 2 with hτ
  have hτpos : 0 < τ := by rw [hτ]; positivity
  have hτ' : (0 : ℝ) < τ := by exact_mod_cast hτpos
  have ht2 : (t : ℝ≥0∞) = (τ : ℝ≥0∞) + τ := by
    rw [← ENNReal.coe_add, hτ, add_halves]
  have hlτ : 0 < l * τ := mul_pos hl hτpos
  have h1 := distribution_le_of_restricted P hPt hPc hp₀ hp₀a hap₁ T hmeas hsub h₀ h₁ hf hfa
    hτpos hlτ
  rw [← ht2] at h1
  -- rewrite the two summands as `ofReal` of real expressions
  have hy₀ : 0 ≤ ((l * τ : ℝ≥0) : ℝ) ^ (1 - a / p₀) * kAbove p₀ a :=
    mul_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _) hk₀.le
  have hy₁ : 0 ≤ ((l * τ : ℝ≥0) : ℝ) ^ (1 - a / p₁) * kBelow p₁ a :=
    mul_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _) hk₁.le
  have e₀ := ennreal_term_eq (M := M₀) hNt hp₀ (div_pos ha hp₀) hp₀ hy₀ hτpos
  have e₁ := ennreal_term_eq (M := M₁) hNt hp₁ (div_pos ha hp₁) hp₁ hy₁ hτpos
  have hX : ((M₀ : ℝ) * (p₀ * (N.toReal ^ (a / p₀) *
        (((l * τ : ℝ≥0) : ℝ) ^ (1 - a / p₀) * kAbove p₀ a))) / (τ : ℝ)) ^ p₀ +
      ((M₁ : ℝ) * (p₁ * (N.toReal ^ (a / p₁) *
        (((l * τ : ℝ≥0) : ℝ) ^ (1 - a / p₁) * kBelow p₁ a))) / (τ : ℝ)) ^ p₁ =
      restrictedK p₀ p₁ a * ((M₀ : ℝ) ^ p₀ * (l : ℝ) ^ (p₀ - a)) * N.toReal ^ a *
        (τ : ℝ) ^ (-a) := by
    rw [NNReal.coe_mul]
    exact two_terms_eq hp₀ hp₀a hap₁ (by exact_mod_cast hM₀) (by exact_mod_cast hM₁)
      ENNReal.toReal_nonneg (by exact_mod_cast hl) hτ' hbal
  have hnn₀ : 0 ≤ ((M₀ : ℝ) * (p₀ * (N.toReal ^ (a / p₀) *
        (((l * τ : ℝ≥0) : ℝ) ^ (1 - a / p₀) * kAbove p₀ a))) / (τ : ℝ)) ^ p₀ := by
    have := hk₀
    exact Real.rpow_nonneg (by positivity) _
  have hnn₁ : 0 ≤ ((M₁ : ℝ) * (p₁ * (N.toReal ^ (a / p₁) *
        (((l * τ : ℝ≥0) : ℝ) ^ (1 - a / p₁) * kBelow p₁ a))) / (τ : ℝ)) ^ p₁ := by
    have := hk₁
    exact Real.rpow_nonneg (by positivity) _
  have h2 : distribution (T f) (t : ℝ≥0∞) ν ≤ ENNReal.ofReal (restrictedK p₀ p₁ a *
      ((M₀ : ℝ) ^ p₀ * (l : ℝ) ^ (p₀ - a)) * N.toReal ^ a * (τ : ℝ) ^ (-a)) := by
    refine h1.trans (le_of_eq ?_)
    rw [e₀, e₁, ← ENNReal.ofReal_add hnn₀ hnn₁, hX]
  have hKR : 0 ≤ restrictedK p₀ p₁ a * ((M₀ : ℝ) ^ p₀ * (l : ℝ) ^ (p₀ - a)) :=
    (mul_pos hKpos hRpos).le
  have hNr : 0 ≤ N.toReal := ENNReal.toReal_nonneg
  have htτ : (t : ℝ) = 2 * (τ : ℝ) := by rw [hτ]; push_cast; ring
  have hXpow : (restrictedK p₀ p₁ a * ((M₀ : ℝ) ^ p₀ * (l : ℝ) ^ (p₀ - a)) * N.toReal ^ a *
      (τ : ℝ) ^ (-a)) ^ a⁻¹ = (restrictedK p₀ p₁ a * ((M₀ : ℝ) ^ p₀ * (l : ℝ) ^ (p₀ - a))) ^ a⁻¹ *
        N.toReal * (τ : ℝ)⁻¹ := by
    rw [Real.mul_rpow (mul_nonneg hKR (Real.rpow_nonneg hNr _)) (Real.rpow_nonneg hτ'.le _),
      Real.mul_rpow hKR (Real.rpow_nonneg hNr _), Real.rpow_rpow_inv hNr ha.ne',
      ← Real.rpow_mul hτ'.le, show -a * a⁻¹ = -1 by field_simp, Real.rpow_neg_one]
  calc (t : ℝ≥0∞) * distribution (T f) t ν ^ a⁻¹
      ≤ (t : ℝ≥0∞) * (ENNReal.ofReal (restrictedK p₀ p₁ a *
          ((M₀ : ℝ) ^ p₀ * (l : ℝ) ^ (p₀ - a)) * N.toReal ^ a * (τ : ℝ) ^ (-a))) ^ a⁻¹ := by
        gcongr
    _ = ENNReal.ofReal ((t : ℝ) * (restrictedK p₀ p₁ a *
          ((M₀ : ℝ) ^ p₀ * (l : ℝ) ^ (p₀ - a)) * N.toReal ^ a * (τ : ℝ) ^ (-a)) ^ a⁻¹) := by
        rw [← ENNReal.ofReal_coe_nnreal (p := t), ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_mul (NNReal.coe_nonneg t),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (inv_nonneg.2 ha.le)]
        simp only [ENNReal.ofReal_coe_nnreal]
    _ = ENNReal.ofReal (2 * (restrictedK p₀ p₁ a * ((M₀ : ℝ) ^ p₀ * (l : ℝ) ^ (p₀ - a))) ^ a⁻¹) *
          N := by
        rw [hXpow, htτ, ← ENNReal.ofReal_toReal hNt, ← ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_toReal hNt]
        congr 1
        field_simp

end StepA2

/-! ### The interpolation theorem -/

section Main

variable {α α' E₁ E₂ : Type*} [MeasurableSpace α] [MeasurableSpace α'] {μ : Measure α}
  {ν : Measure α'} [TopologicalSpace E₁] [ESeminormedAddMonoid E₁] [TopologicalSpace E₂]
  [ESeminormedAddMonoid E₂]

/-- The constant of the Marcinkiewicz interpolation theorem from restricted weak-type bounds:
the constant `realInterpConst` of the vendored real interpolation theorem at the intermediate
exponents `a₀ < p < a₁`, times `2 K_{a₀}^{(1-θ)/a₀} K_{a₁}^{θ/a₁}`. It depends only on
`p₀, p₁, p, θ`. -/
def restrictedInterpConst (p₀ p₁ p θ : ℝ) : ℝ≥0∞ :=
  realInterpConst (ENNReal.ofReal (interA0 p₀ p₁ θ)) (ENNReal.ofReal (interA1 p₀ p₁ θ))
    (ENNReal.ofReal (interA0 p₀ p₁ θ)) (ENNReal.ofReal (interA1 p₀ p₁ θ)) (ENNReal.ofReal p)
    (ENNReal.ofReal θ) *
  ENNReal.ofReal (2 * restrictedK p₀ p₁ (interA0 p₀ p₁ θ) ^ ((1 - θ) / interA0 p₀ p₁ θ) *
    restrictedK p₀ p₁ (interA1 p₀ p₁ θ) ^ (θ / interA1 p₀ p₁ θ))

/-- **Marcinkiewicz interpolation from restricted weak-type bounds**.  Let `0 < p₀ < p₁ < ∞`,
`0 < θ < 1`, `1/p = (1-θ)/p₀ + θ/p₁`, and let `T` be subadditive on a class `P` of functions closed
under
`trunc` and `truncCompl` (e.g. all functions, the a.e. strongly measurable ones, the finitely
supported ones), with values a.e. strongly measurable, and of restricted weak types
`‖T f‖_{L^{p_i,∞}} ≤ M_i ‖f‖_{L^{p_i,1}}` (`i = 0, 1`, `M_i > 0`) for `f ∈ P ∩ L^{p_i,1}`.
Then for `f ∈ P ∩ L^p`, `‖T f‖_{L^p} ≤ C(p₀, p₁, p, θ) M₀^{1-θ} M₁^θ ‖f‖_{L^p}`. -/
theorem eLpNorm_le_interpolation_of_restricted (P : (α → E₁) → Prop)
    (hPt : ∀ f (s : ℝ≥0∞), P f → P (trunc f s))
    (hPc : ∀ f (s : ℝ≥0∞), P f → P (truncCompl f s))
    {p₀ p₁ p θ : ℝ} (hp₀ : 0 < p₀) (hp₀₁ : p₀ < p₁) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hp : 1 / p = (1 - θ) / p₀ + θ / p₁) {M₀ M₁ : ℝ≥0} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (T : (α → E₁) → α' → E₂) (hmeas : ∀ f, P f → AEStronglyMeasurable (T f) ν)
    (hsub : ∀ f g, P f → P g → ∀ᵐ x ∂ν, ‖T (f + g) x‖ₑ ≤ ‖T f x‖ₑ + ‖T g x‖ₑ)
    (h₀ : ∀ f, P f → MemLorentz f (ENNReal.ofReal p₀) 1 μ →
      wnorm (T f) (ENNReal.ofReal p₀) ν ≤ M₀ * eLorentzNorm f (ENNReal.ofReal p₀) 1 μ)
    (h₁ : ∀ f, P f → MemLorentz f (ENNReal.ofReal p₁) 1 μ →
      wnorm (T f) (ENNReal.ofReal p₁) ν ≤ M₁ * eLorentzNorm f (ENNReal.ofReal p₁) 1 μ)
    {f : α → E₁} (hf : P f) (hfp : MemLp f (ENNReal.ofReal p) μ) :
    eLpNorm (T f) (ENNReal.ofReal p) ν ≤ restrictedInterpConst p₀ p₁ p θ *
      (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * eLpNorm f (ENNReal.ofReal p) μ := by
  have hp₁ : 0 < p₁ := hp₀.trans hp₀₁
  have hpp : 0 < p := by
    have : 0 < 1 / p := by
      rw [hp]
      exact add_pos (div_pos (by linarith) hp₀) (div_pos hθ₀ hp₁)
    exact one_div_pos.1 this
  set a₀ := interA0 p₀ p₁ θ with ha₀def
  set a₁ := interA1 p₀ p₁ θ with ha₁def
  obtain ⟨ha₀l, ha₀u⟩ := interA0_bounds hp₀ hp₀₁ hθ₀ hθ₁
  obtain ⟨ha₁l, ha₁u⟩ := interA1_bounds hp₀ hp₀₁ hθ₀ hθ₁
  have ha₀ : 0 < a₀ := hp₀.trans ha₀l
  have ha₁ : 0 < a₁ := hp₀.trans ha₁l
  have hpa : 1 / p = (1 - θ) / a₀ + θ / a₁ := hp.trans interA_combine.symm
  have hM₀r : (0 : ℝ) < M₀ := by exact_mod_cast hM₀
  have hM₁r : (0 : ℝ) < M₁ := by exact_mod_cast hM₁
  -- the balancing height `λ`
  set lr : ℝ := ((M₀ : ℝ) ^ p₀ / (M₁ : ℝ) ^ p₁) ^ (1 / (p₁ - p₀)) with hlr
  have hlrpos : 0 < lr := Real.rpow_pos_of_pos (div_pos (Real.rpow_pos_of_pos hM₀r _)
    (Real.rpow_pos_of_pos hM₁r _)) _
  have hbal : (M₀ : ℝ) ^ p₀ * lr ^ p₀ = (M₁ : ℝ) ^ p₁ * lr ^ p₁ := by
    have h1 : lr ^ (p₁ - p₀) = (M₀ : ℝ) ^ p₀ / (M₁ : ℝ) ^ p₁ := by
      rw [hlr, ← Real.rpow_mul (div_pos (Real.rpow_pos_of_pos hM₀r _)
        (Real.rpow_pos_of_pos hM₁r _)).le, one_div_mul_cancel (by linarith), Real.rpow_one]
    have h2 : lr ^ p₁ = lr ^ p₀ * lr ^ (p₁ - p₀) := by
      rw [← Real.rpow_add hlrpos]; congr 1; ring
    rw [h2, h1]
    have : (M₁ : ℝ) ^ p₁ ≠ 0 := (Real.rpow_pos_of_pos hM₁r _).ne'
    field_simp
  have hlpos : 0 < lr.toNNReal := Real.toNNReal_pos.2 hlrpos
  have hlcoe : ((lr.toNNReal : ℝ≥0) : ℝ) = lr := Real.coe_toNNReal _ hlrpos.le
  have hbal' : (M₀ : ℝ) ^ p₀ * ((lr.toNNReal : ℝ≥0) : ℝ) ^ p₀ =
      (M₁ : ℝ) ^ p₁ * ((lr.toNNReal : ℝ≥0) : ℝ) ^ p₁ := by rw [hlcoe]; exact hbal
  -- the endpoint constants of the weak-type bounds at `a₀`, `a₁`
  set R₀ : ℝ := (M₀ : ℝ) ^ p₀ * lr ^ (p₀ - a₀) with hR₀
  set R₁ : ℝ := (M₀ : ℝ) ^ p₀ * lr ^ (p₀ - a₁) with hR₁
  have hR₀pos : 0 < R₀ := mul_pos (Real.rpow_pos_of_pos hM₀r _) (Real.rpow_pos_of_pos hlrpos _)
  have hR₁pos : 0 < R₁ := mul_pos (Real.rpow_pos_of_pos hM₀r _) (Real.rpow_pos_of_pos hlrpos _)
  have hK₀ := restrictedK_pos hp₀ ha₀l ha₀u
  have hK₁ := restrictedK_pos hp₀ ha₁l ha₁u
  set W₀ : ℝ := 2 * (restrictedK p₀ p₁ a₀ * R₀) ^ a₀⁻¹ with hW₀
  set W₁ : ℝ := 2 * (restrictedK p₀ p₁ a₁ * R₁) ^ a₁⁻¹ with hW₁
  have hW₀pos : 0 < W₀ := by
    have := mul_pos hK₀ hR₀pos
    positivity
  have hW₁pos : 0 < W₁ := by
    have := mul_pos hK₁ hR₁pos
    positivity
  have hw₀ : ∀ g, P g → MemLp g (ENNReal.ofReal a₀) μ →
      wnorm (T g) (ENNReal.ofReal a₀) ν ≤ ((W₀.toNNReal : ℝ≥0) : ℝ≥0∞) *
        eLpNorm g (ENNReal.ofReal a₀) μ := by
    intro g hg hgm
    have := wnorm_le_of_restricted P hPt hPc hp₀ ha₀l ha₀u hM₀ hM₁ T hmeas hsub h₀ h₁
      hlpos hbal' hg hgm
    rw [hlcoe] at this
    exact this
  have hw₁ : ∀ g, P g → MemLp g (ENNReal.ofReal a₁) μ →
      wnorm (T g) (ENNReal.ofReal a₁) ν ≤ ((W₁.toNNReal : ℝ≥0) : ℝ≥0∞) *
        eLpNorm g (ENNReal.ofReal a₁) μ := by
    intro g hg hgm
    have := wnorm_le_of_restricted P hPt hPc hp₀ ha₁l ha₁u hM₀ hM₁ T hmeas hsub h₀ h₁
      hlpos hbal' hg hgm
    rw [hlcoe] at this
    exact this
  -- Step B: the vendored Marcinkiewicz theorem at the exponents `a₀ < p < a₁`
  have hp₀m : ENNReal.ofReal a₀ ∈ Ioc 0 (ENNReal.ofReal a₀) :=
    ⟨ENNReal.ofReal_pos.2 ha₀, le_rfl⟩
  have hp₁m : ENNReal.ofReal a₁ ∈ Ioc 0 (ENNReal.ofReal a₁) :=
    ⟨ENNReal.ofReal_pos.2 ha₁, le_rfl⟩
  have hne : ENNReal.ofReal a₀ ≠ ENNReal.ofReal a₁ := fun h =>
    interA_ne hp₀ hp₀₁ ((ENNReal.ofReal_eq_ofReal_iff ha₀.le ha₁.le).1 h)
  have ht := ofReal_mem_Ioo_zero_one hθ₀ hθ₁
  have hpE : (ENNReal.ofReal p)⁻¹ = (1 - ENNReal.ofReal θ) / ENNReal.ofReal a₀ +
      ENNReal.ofReal θ / ENNReal.ofReal a₁ := by
    rw [← ENNReal.ofReal_inv_of_pos hpp, ← one_div, hpa,
      ENNReal.ofReal_add (div_nonneg (by linarith) ha₀.le) (div_nonneg hθ₀.le ha₁.le),
      ENNReal.ofReal_div_of_pos ha₀, ENNReal.ofReal_div_of_pos ha₁, one_sub_ofReal_eq hθ₀.le]
  have key := eLpNorm_le_interpolation_of_truncClosed (μ := μ) (ν := ν) P hPt hPc hp₀m hp₁m hne
    ht hpE hpE (M₀ := W₀.toNNReal) (M₁ := W₁.toNNReal) (Real.toNNReal_pos.2 hW₀pos)
    (Real.toNNReal_pos.2 hW₁pos) T hmeas hsub hw₀ hw₁ hf hfp
  rw [toReal_one_sub_ofReal hθ₀.le hθ₁.le, ENNReal.toReal_ofReal hθ₀.le] at key
  -- identify the constant
  have hWreal : W₀ ^ (1 - θ) * W₁ ^ θ =
      (2 * restrictedK p₀ p₁ a₀ ^ ((1 - θ) / a₀) * restrictedK p₀ p₁ a₁ ^ (θ / a₁)) *
        ((M₀ : ℝ) ^ (1 - θ) * (M₁ : ℝ) ^ θ) := by
    rw [hW₀, hW₁, W_product hK₀ hK₁ hR₀pos hR₁pos,
      balance_final hp₀ hp₁ ha₀ ha₁ hM₀r hM₁r hlrpos hp hpa hbal]
  have hW : ((W₀.toNNReal : ℝ≥0) : ℝ≥0∞) ^ (1 - θ) * ((W₁.toNNReal : ℝ≥0) : ℝ≥0∞) ^ θ =
      ENNReal.ofReal (2 * restrictedK p₀ p₁ a₀ ^ ((1 - θ) / a₀) *
        restrictedK p₀ p₁ a₁ ^ (θ / a₁)) * (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ := by
    have e₀ : ((W₀.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal W₀ := rfl
    have e₁ : ((W₁.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal W₁ := rfl
    have hc : 0 ≤ 2 * restrictedK p₀ p₁ a₀ ^ ((1 - θ) / a₀) * restrictedK p₀ p₁ a₁ ^ (θ / a₁) := by
      have := hK₀
      have := hK₁
      positivity
    rw [e₀, e₁, ← ENNReal.ofReal_coe_nnreal (p := M₀), ← ENNReal.ofReal_coe_nnreal (p := M₁),
      ENNReal.ofReal_rpow_of_nonneg hW₀pos.le (by linarith),
      ENNReal.ofReal_rpow_of_nonneg hW₁pos.le hθ₀.le,
      ENNReal.ofReal_rpow_of_nonneg hM₀r.le (by linarith),
      ENNReal.ofReal_rpow_of_nonneg hM₁r.le hθ₀.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hW₀pos.le _), ← ENNReal.ofReal_mul hc,
      ← ENNReal.ofReal_mul (mul_nonneg hc (Real.rpow_nonneg hM₀r.le _))]
    congr 1
    rw [hWreal]
    ring
  calc eLpNorm (T f) (ENNReal.ofReal p) ν
      ≤ realInterpConst (ENNReal.ofReal a₀) (ENNReal.ofReal a₁) (ENNReal.ofReal a₀)
          (ENNReal.ofReal a₁) (ENNReal.ofReal p) (ENNReal.ofReal θ) *
        ((W₀.toNNReal : ℝ≥0) : ℝ≥0∞) ^ (1 - θ) * ((W₁.toNNReal : ℝ≥0) : ℝ≥0∞) ^ θ *
        eLpNorm f (ENNReal.ofReal p) μ := key
    _ = _ := by
        unfold restrictedInterpConst
        rw [mul_assoc (realInterpConst _ _ _ _ _ _), hW]
        ring

/-- The constant `restrictedInterpConst` is finite. -/
theorem restrictedInterpConst_ne_top {p₀ p₁ p θ : ℝ} (hp₀ : 0 < p₀) (hp₀₁ : p₀ < p₁)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hp : 1 / p = (1 - θ) / p₀ + θ / p₁) :
    restrictedInterpConst p₀ p₁ p θ ≠ ⊤ := by
  have hp₁ : 0 < p₁ := hp₀.trans hp₀₁
  have hpp : 0 < p := by
    have : 0 < 1 / p := by
      rw [hp]
      exact add_pos (div_pos (by linarith) hp₀) (div_pos hθ₀ hp₁)
    exact one_div_pos.1 this
  obtain ⟨ha₀l, ha₀u⟩ := interA0_bounds hp₀ hp₀₁ hθ₀ hθ₁
  obtain ⟨ha₁l, ha₁u⟩ := interA1_bounds hp₀ hp₀₁ hθ₀ hθ₁
  have ha₀ : 0 < interA0 p₀ p₁ θ := hp₀.trans ha₀l
  have ha₁ : 0 < interA1 p₀ p₁ θ := hp₀.trans ha₁l
  have hpa : 1 / p = (1 - θ) / interA0 p₀ p₁ θ + θ / interA1 p₀ p₁ θ :=
    hp.trans interA_combine.symm
  unfold restrictedInterpConst
  refine ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top
  have hpE : (ENNReal.ofReal p)⁻¹ = (1 - ENNReal.ofReal θ) / ENNReal.ofReal (interA0 p₀ p₁ θ) +
      ENNReal.ofReal θ / ENNReal.ofReal (interA1 p₀ p₁ θ) := by
    rw [← ENNReal.ofReal_inv_of_pos hpp, ← one_div, hpa,
      ENNReal.ofReal_add (div_nonneg (by linarith) ha₀.le) (div_nonneg hθ₀.le ha₁.le),
      ENNReal.ofReal_div_of_pos ha₀, ENNReal.ofReal_div_of_pos ha₁, one_sub_ofReal_eq hθ₀.le]
  exact realInterpConst_ne_top ⟨ENNReal.ofReal_pos.2 ha₀, le_rfl⟩ ⟨ENNReal.ofReal_pos.2 ha₁, le_rfl⟩
    (fun h => interA_ne hp₀ hp₀₁ ((ENNReal.ofReal_eq_ofReal_iff ha₀.le ha₁.le).1 h))
    (ofReal_mem_Ioo_zero_one hθ₀ hθ₁) hpE

end Main

end PrimeCarleson.Proof.Common

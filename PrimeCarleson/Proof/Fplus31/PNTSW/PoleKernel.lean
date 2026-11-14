module

public import PrimeCarleson.Proof.Fplus31.PNTSW.Perron

/-!
# The pole term of `ζ` on a line `re s = σ`, `σ > 1`: Mellin inversion of `(1-u)²/(2u)`

Part of the prime number theorem in progressions on the classical zero-free region
(`PNTSW/Main.lean`). The pole kernel is evaluated on an arbitrary line `re s = σ` with `σ > 1`. The
function `V(u) = (max (1-u) 0)² / (2u)` has Mellin transform `1/((s-1) s (s+1))` for `re s > 1`, and
Mellin inversion on `re s = σ` returns `V`; hence the exact evaluation of the pole term (no residue
theorem):

`∫_ℝ y^{s+1} / ((s-1) s (s+1)) dt = 2π (y-1)²/2` on `re s = σ`, `y ≥ 1`
(`integral_poleKernel`).  Then `riesz_zeta_split`: the splitting of the Perron formula for `ζ` at
the pole, `L₁(s) = (s-1) ζ(s)` entire.
-/

@[expose] public noncomputable section

open MeasureTheory Set Complex Real ArithmeticFunction LSeries

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.PNTSW

/-- The kernel `V(u) = (max (1-u) 0)² / (2u)` of the pole term. -/
noncomputable def V (u : ℝ) : ℝ := (max (1 - u) 0) ^ 2 / (2 * u)

/-- `V(u) = (1-u)²/(2u)` for `u ≤ 1`. -/
lemma V_of_le {u : ℝ} (h : u ≤ 1) : V u = (1 - u) ^ 2 / (2 * u) := by
  unfold V; rw [max_eq_left (by linarith)]

/-- `V(u) = 0` for `u ≥ 1`. -/
lemma V_of_ge {u : ℝ} (h : 1 ≤ u) : V u = 0 := by
  unfold V; rw [max_eq_right (by linarith)]; simp

/-- The Mellin transform of `V` is `1/((s-1) s (s+1))` for `re s > 1`. -/
theorem mellin_V (s : ℂ) (hs : 1 < s.re) :
    mellin (fun u : ℝ => (V u : ℂ)) s = 1 / ((s - 1) * s * (s + 1)) := by
  have hmem : ∀ u ∈ Ioi (0 : ℝ), ((u : ℂ) ^ (s - 1)) • (V u : ℂ) =
      Set.indicator (Ioc (0 : ℝ) 1)
        (fun u : ℝ => ((u : ℂ) ^ (s - 2) - 2 * (u : ℂ) ^ (s - 1) + (u : ℂ) ^ s) / 2) u := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
    by_cases h1 : u ≤ 1
    · have hmu : u ∈ Ioc (0 : ℝ) 1 := ⟨hu0, h1⟩
      simp only [Set.indicator_of_mem hmu]
      rw [V_of_le h1, smul_eq_mul]
      have e1 : (u : ℂ) ^ (s - 1) = (u : ℂ) ^ (s - 2) * u := by
        calc (u : ℂ) ^ (s - 1) = (u : ℂ) ^ ((s - 2) + 1) := by ring_nf
          _ = (u : ℂ) ^ (s - 2) * (u : ℂ) ^ (1 : ℂ) := Complex.cpow_add _ _ hu'
          _ = (u : ℂ) ^ (s - 2) * u := by rw [Complex.cpow_one]
      have e2 : (u : ℂ) ^ s = (u : ℂ) ^ (s - 2) * u ^ 2 := by
        calc (u : ℂ) ^ s = (u : ℂ) ^ ((s - 2) + 2) := by ring_nf
          _ = (u : ℂ) ^ (s - 2) * (u : ℂ) ^ (2 : ℂ) := Complex.cpow_add _ _ hu'
          _ = (u : ℂ) ^ (s - 2) * u ^ 2 := by
            rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
      rw [e1, e2]; push_cast; field_simp; ring
    · have hnu : u ∉ Ioc (0 : ℝ) 1 := fun h => h1 h.2
      simp only [Set.indicator_of_notMem hnu]
      rw [V_of_ge (by linarith [not_le.mp h1])]; simp
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
  have hI : ∀ r : ℂ, 0 < r.re + 1 → IntegrableOn (fun u : ℝ => (u : ℂ) ^ r) (Ioc (0 : ℝ) 1) := by
    intro r hr
    have := intervalIntegral.intervalIntegrable_cpow' (a := (0:ℝ)) (b := 1) (r := r) (by linarith)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp this
  have h2 := hI (s - 2) (by simp; linarith)
  have h1 := hI (s - 1) (by simp; linarith)
  have h0 := hI s (by linarith)
  have hsub : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 2) - 2 * (u : ℂ) ^ (s - 1))
      (Ioc (0 : ℝ) 1) :=
    h2.sub (h1.const_mul 2)
  have e : ∫ u in Ioc (0 : ℝ) 1, ((u : ℂ) ^ (s - 2) - 2 * (u : ℂ) ^ (s - 1) + (u : ℂ) ^ s) =
      1 / (s - 1) - 2 * (1 / s) + 1 / (s + 1) := by
    rw [integral_add hsub h0, integral_sub h2 (h1.const_mul 2), integral_const_mul,
      hint (s - 2) (by simp; linarith), hint (s - 1) (by simp; linarith), hint s (by linarith),
      show s - 2 + 1 = s - 1 by ring, show s - 1 + 1 = s by ring]
  rw [integral_div, e]
  have hs0 : s ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs2 : s + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  field_simp
  ring


/-- `V` is continuous on `u > 0`. -/
lemma V_continuousAt {x : ℝ} (hx : 0 < x) : ContinuousAt (fun u : ℝ => (V u : ℂ)) x := by
  have h : ContinuousAt V x := by
    unfold V
    have h1 : ContinuousAt (fun u : ℝ => (max (1 - u) 0) ^ 2) x := by fun_prop
    exact h1.div (by fun_prop) (by positivity)
  exact Complex.continuous_ofReal.continuousAt.comp h

/-- The Mellin transform of `V` converges on `re s = σ > 1`. -/
theorem V_mellinConvergent_of {σ : ℝ} (hσ : 1 < σ) :
    MellinConvergent (fun u : ℝ => (V u : ℂ)) (σ : ℂ) := by
  have hcont : ContinuousOn (fun u : ℝ => (V u : ℂ)) (Ioi 0) :=
    fun x hx => (V_continuousAt hx).continuousWithinAt
  have htop : (fun u : ℝ => (V u : ℂ)) =O[Filter.atTop] (fun x : ℝ => x ^ (-(σ + 1 : ℝ))) := by
    refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    simp [V_of_ge hx]
  have hbot : (fun u : ℝ => (V u : ℂ)) =O[nhdsWithin 0 (Ioi 0)] (fun x : ℝ => x ^ (-(1 : ℝ))) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with x hx
    have hx0 : 0 < x := hx.1
    rw [V_of_le hx.2.le, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_neg_one,
      one_mul, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [hx.1, hx.2]
  exact mellinConvergent_of_isBigO_rpow (a := σ + 1) (b := 1)
    (hcont.locallyIntegrableOn measurableSet_Ioi) htop (by simp) hbot (by simpa using hσ)

/-- The Mellin transform of `V` is integrable on `re s = σ > 1`. -/
theorem V_verticalIntegrable_of {σ : ℝ} (hσ : 1 < σ) :
    Complex.VerticalIntegrable (mellin (fun u : ℝ => (V u : ℂ))) σ := by
  unfold Complex.VerticalIntegrable
  change MeasureTheory.Integrable
    (fun y : ℝ => mellin (fun u : ℝ => (V u : ℂ)) ((σ : ℂ) + y * Complex.I))
  have hform : (fun y : ℝ => mellin (fun u : ℝ => (V u : ℂ)) ((σ : ℂ) + y * Complex.I)) =
      fun y : ℝ => 1 / ((((σ : ℂ) + y * Complex.I) - 1) * ((σ : ℂ) + y * Complex.I) *
        (((σ : ℂ) + y * Complex.I) + 1)) := by
    funext y
    apply mellin_V
    simpa using hσ
  rw [hform]
  have hne : ∀ y : ℝ, ((((σ : ℂ) + y * Complex.I) - 1) * ((σ : ℂ) + y * Complex.I) *
        (((σ : ℂ) + y * Complex.I) + 1)) ≠ 0 := by
    intro y
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · intro h; have := congrArg Complex.re h; simp at this; linarith
    · intro h; have := congrArg Complex.re h; simp at this; linarith
    · intro h; have := congrArg Complex.re h; simp at this; linarith
  refine (integrable_inv_one_add_sq.const_mul (σ - 1)⁻¹).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    exact Continuous.div continuous_const (by fun_prop) hne
  · refine Filter.Eventually.of_forall (fun y => ?_)
    have n1 : σ - 1 ≤ ‖(σ : ℂ) + y * Complex.I - 1‖ := by
      have := Complex.re_le_norm ((σ : ℂ) + y * Complex.I - 1)
      simpa using this
    have n2 := one_add_sq_le_norm_mul_norm (σ := σ) hσ.le y
    rw [norm_div, norm_one, norm_mul, norm_mul]
    have hpos : 0 < 1 + y ^ 2 := by positivity
    have hε : 0 < σ - 1 := by linarith
    have hprod : (σ - 1) * (1 + y ^ 2) ≤ ‖(σ : ℂ) + y * Complex.I - 1‖ *
        (‖(σ : ℂ) + y * Complex.I‖ * ‖(σ : ℂ) + y * Complex.I + 1‖) :=
      mul_le_mul n1 n2 hpos.le (norm_nonneg _)
    calc 1 / (‖(σ : ℂ) + y * Complex.I - 1‖ * ‖(σ : ℂ) + y * Complex.I‖ *
          ‖(σ : ℂ) + y * Complex.I + 1‖) ≤ 1 / ((σ - 1) * (1 + y ^ 2)) := by
          apply one_div_le_one_div_of_le (by positivity)
          calc (σ - 1) * (1 + y ^ 2) ≤ _ := hprod
            _ = _ := by ring
      _ = (σ - 1)⁻¹ * (1 + y ^ 2)⁻¹ := by rw [one_div, mul_inv]

/-- Mellin inversion of `V` on `re s = σ > 1`. -/
theorem riesz_V_of {σ : ℝ} (hσ : 1 < σ) {x : ℝ} (hx : 0 < x) :
    mellinInv σ (fun s : ℂ => 1 / ((s - 1) * s * (s + 1))) x = (V x : ℂ) := by
  have h := mellinInv_mellin_eq σ (fun u : ℝ => (V u : ℂ)) hx (V_mellinConvergent_of hσ)
    (V_verticalIntegrable_of hσ) (V_continuousAt hx)
  rw [← h]
  unfold mellinInv
  congr 2
  funext y
  rw [mellin_V]
  simpa using hσ

/-- `y V(1/y) = (y-1)²/2` for `y ≥ 1`. -/
theorem y_mul_V_inv {y : ℝ} (hy : 1 ≤ y) : y * V (1 / y) = (y - 1) ^ 2 / 2 := by
  have hy0 : 0 < y := by linarith
  have h1 : 1 / y ≤ 1 := by rw [div_le_one hy0]; exact hy
  rw [V_of_le h1]; field_simp

/-- The pole term of `ζ` on the line `re s = σ`, `σ > 1`: `rieszKernel y s / (s - 1)`. -/
theorem integral_poleKernel {σ : ℝ} (hσ : 1 < σ) {y : ℝ} (hy : 1 ≤ y) :
    ∫ t : ℝ, rieszKernel y ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I - 1) =
      ((2 * π : ℝ) : ℂ) * (((y - 1) ^ 2 / 2 : ℝ) : ℂ) := by
  have hy0 : 0 < y := by linarith
  have hx : (0 : ℝ) < 1 / y := by positivity
  have hp := riesz_V_of hσ hx
  unfold mellinInv at hp
  rw [Complex.real_smul] at hp
  have hint : ∫ t : ℝ, (((1 / y : ℝ)) : ℂ) ^ (-((σ : ℂ) + t * I)) •
      (fun s : ℂ => 1 / ((s - 1) * s * (s + 1))) ((σ : ℂ) + t * I) =
      ((2 * π : ℝ) : ℂ) * (V (1 / y) : ℂ) := by
    rw [← hp, ← mul_assoc, ← Complex.ofReal_mul,
      mul_one_div_cancel (by positivity : (2 * π : ℝ) ≠ 0)]
    simp
  have hpt : ∀ t : ℝ, rieszKernel y ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I - 1) =
      (y : ℂ) * ((((1 / y : ℝ)) : ℂ) ^ (-((σ : ℂ) + t * I)) •
        (fun s : ℂ => 1 / ((s - 1) * s * (s + 1))) ((σ : ℂ) + t * I)) := by
    intro t
    unfold rieszKernel
    rw [smul_eq_mul]
    have := natCast_cpow_mul_ofReal_cpow (n := 1) one_ne_zero hy0 ((σ : ℂ) + t * I)
    simp only [Nat.cast_one, Complex.one_cpow, one_mul] at this
    rw [this]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, hint]
  have := y_mul_V_inv hy
  calc (y : ℂ) * (((2 * π : ℝ) : ℂ) * (V (1 / y) : ℂ))
      = ((2 * π : ℝ) : ℂ) * (((y * V (1 / y) : ℝ)) : ℂ) := by push_cast; ring
    _ = _ := by rw [this]

/-- `L₁(s) = (s-1) ζ(s)`, made entire by `L₁(1) = 1`. -/
abbrev zetaL1 : ℂ → ℂ := DirichletCharacter.LFunctionTrivChar₁ 1

/-- The `L`-function of the trivial character modulo `1` is `ζ`. -/
theorem LFunctionTrivChar_one_eq : DirichletCharacter.LFunctionTrivChar 1 = riemannZeta :=
  DirichletCharacter.LFunction_modOne_eq

/-- `L₁(s) = (s-1) ζ(s)` for `s ≠ 1`. -/
theorem zetaL1_apply {s : ℂ} (hs : s ≠ 1) : zetaL1 s = (s - 1) * riemannZeta s := by
  unfold zetaL1 DirichletCharacter.LFunctionTrivChar₁
  rw [Function.update_of_ne hs, LFunctionTrivChar_one_eq]

/-- The derivative of `L₁` away from the pole. -/
theorem deriv_zetaL1 {s : ℂ} (hs : s ≠ 1) :
    deriv zetaL1 s = (s - 1) * deriv riemannZeta s + riemannZeta s := by
  unfold zetaL1
  rw [DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one 1 hs, LFunctionTrivChar_one_eq]

/-- `L₁` is entire. -/
theorem differentiable_zetaL1 : Differentiable ℂ zetaL1 :=
  DirichletCharacter.differentiable_LFunctionTrivChar₁ 1

/-- `-ζ'/ζ = -L₁'/L₁ + 1/(s-1)` away from the pole and the zeros. -/
theorem neg_logDeriv_zeta_split {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    -(deriv riemannZeta s / riemannZeta s) =
      -(deriv zetaL1 s / zetaL1 s) + 1 / (s - 1) := by
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [deriv_zetaL1 hs, zetaL1_apply hs]
  field_simp
  ring

/-- The splitting of the integrand on the line `re s = σ`, `σ > 1`. -/
theorem rieszIntegrand_zeta_split {σ : ℝ} (hσ : 1 < σ) (y : ℝ) (t : ℝ) :
    rieszIntegrand riemannZeta y ((σ : ℂ) + t * I) =
      rieszIntegrand zetaL1 y ((σ : ℂ) + t * I) +
        rieszKernel y ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I - 1) := by
  have hs : ((σ : ℂ) + t * I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hz : riemannZeta ((σ : ℂ) + t * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ)
  unfold rieszIntegrand
  rw [neg_logDeriv_zeta_split hs hz]
  ring

/-- The character modulo `1` takes the value `1`. -/
theorem modOne_char_apply (χ : DirichletCharacter ℂ 1) (n : ℕ) : χ n = 1 := by
  have : χ = 1 := Subsingleton.elim _ _
  rw [this]
  exact MulChar.one_apply (isUnit_of_subsingleton _)

/-- The pole term is integrable on the line `re s = σ > 1`. -/
theorem integrable_poleKernel_line {σ : ℝ} (hσ : 1 < σ) {y : ℝ} (hy : 0 < y) :
    Integrable fun t : ℝ => rieszKernel y ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I - 1) := by
  have hne : ∀ t : ℝ, (σ : ℂ) + t * I - 1 ≠ 0 := fun t h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hcont : Continuous fun t : ℝ =>
      rieszKernel y ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I - 1) :=
    (continuous_rieszKernel (by linarith) hy).div (by fun_prop) hne
  refine (integrable_inv_one_add_sq.const_mul (y ^ (σ + 1) * (σ - 1)⁻¹)).mono'
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_div]
  have h1 : σ - 1 ≤ ‖(σ : ℂ) + t * I - 1‖ := by
    have := Complex.re_le_norm ((σ : ℂ) + t * I - 1)
    simpa using this
  have hε : 0 < σ - 1 := by linarith
  calc ‖rieszKernel y ((σ : ℂ) + t * I)‖ / ‖(σ : ℂ) + t * I - 1‖
      ≤ ‖rieszKernel y ((σ : ℂ) + t * I)‖ / (σ - 1) :=
        div_le_div_of_nonneg_left (norm_nonneg _) hε h1
    _ ≤ (y ^ (σ + 1) * (1 + t ^ 2)⁻¹) / (σ - 1) :=
        div_le_div_of_nonneg_right (norm_rieszKernel_le hσ.le hy t) hε.le
    _ = y ^ (σ + 1) * (σ - 1)⁻¹ * (1 + t ^ 2)⁻¹ := by rw [div_eq_mul_inv]; ring

/-- **The splitting at the pole of `ζ`.**  For `σ > 1` and `y ≥ 1`,
`2π (∑_{n ≤ y} Λ(n)(y - n) - (y-1)²/2) = ∫ -(L₁'/L₁)(σ+it) y^{σ+1+it}/((σ+it)(σ+1+it)) dt`. -/
theorem riesz_zeta_split {σ : ℝ} (hσ : 1 < σ) {y : ℝ} (hy : 1 ≤ y) :
    ((2 * π : ℝ) : ℂ) * (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (Λ n : ℂ) * ((y : ℂ) - n) -
        (((y - 1) ^ 2 / 2 : ℝ) : ℂ)) =
      ∫ t : ℝ, rieszIntegrand zetaL1 y ((σ : ℂ) + t * I) := by
  have hy0 : 0 < y := by linarith
  have hform := riesz_formula (1 : DirichletCharacter ℂ 1) hσ hy0
  simp only [modOne_char_apply, one_mul, DirichletCharacter.LFunction_modOne_eq] at hform
  have hZ := integrable_rieszIntegrand_line (1 : DirichletCharacter ℂ 1) hσ hy0
  simp only [DirichletCharacter.LFunction_modOne_eq] at hZ
  have hP := integrable_poleKernel_line hσ hy0
  have hL1 : Integrable fun t : ℝ => rieszIntegrand zetaL1 y ((σ : ℂ) + t * I) := by
    have := hZ.sub hP
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply]
    rw [rieszIntegrand_zeta_split hσ]
    ring
  have hsplit : ∫ t : ℝ, rieszIntegrand riemannZeta y ((σ : ℂ) + t * I) =
      (∫ t : ℝ, rieszIntegrand zetaL1 y ((σ : ℂ) + t * I)) +
        ∫ t : ℝ, rieszKernel y ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I - 1) := by
    rw [← integral_add hL1 hP]
    congr 1
    funext t
    exact rieszIntegrand_zeta_split hσ y t
  rw [integral_poleKernel hσ hy] at hsplit
  rw [← hform] at hsplit
  have : ((2 * π : ℝ) : ℂ) * (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (Λ n : ℂ) * ((y : ℂ) - n) -
        (((y - 1) ^ 2 / 2 : ℝ) : ℂ)) =
      ((2 * π : ℝ) : ℂ) * ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (Λ n : ℂ) * ((y : ℂ) - n) -
        ((2 * π : ℝ) : ℂ) * (((y - 1) ^ 2 / 2 : ℝ) : ℂ) := by ring
  rw [this, hsplit]
  ring

end PrimeCarleson.Proof.Fplus31.PNTSW

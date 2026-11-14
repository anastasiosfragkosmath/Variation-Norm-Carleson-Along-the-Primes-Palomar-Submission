module

public import PrimeCarleson.Proof.Oplus.Estimates.SchwartzEstimate

/-!
# Orthogonality of the wave packets with a common time interval ([O+] L1766-L1776, L2500-L2504)

[O+] L1766-L1776:
"`φ_{P'} = c exp(2πi (c(ω_u') - c(ω_u)) ·) φ_P` when `I = I'`. Thus if `𝒫(I_∘)` is a collection of
disjoint multitiles with common time interval `I_∘`, if `g` is supported on `C I_∘` and if
`P_{I_∘}` is any fixed multitile in `𝒫(I_∘)` then Bessel's inequality gives
`∑_{P ∈ 𝒫(I_∘)} |⟨g, φ_P⟩|² ≲ |I_∘| ∫ |g φ_{P_{I_∘}}|² dx`"; and L2500-L2504
("Using orthogonality"), with the dilation `C` appearing linearly. Source: [O+]
`energyincrementprop`, L1766–L1776; [O+] `tileslargemaxprop`, L2500–L2504 (the second is the form
with explicit dependence on `C`; the first is its consequence for a fixed `C`).

* `packetEnvelope χ I` and `wavePacketOf_eq_mul_packetEnvelope`: for every `J` with
  `|I||J| = 1/2`, `φ_{I×J}(x) = e(c(J)(x - c(I))) · env(x)`, the envelope depending only on
  `χ` and `I` (the packets of a common time interval are modulates of each other);
* `sum_norm_sq_integral_mul_e_le`: Bessel's inequality `∑_m |∫ u e(-m x/T)|² ≤ nT ∫ |u|²` for `u`
  supported in an interval of length `nT`, via the orthonormal system of exponentials in `L²`;
* `sum_norm_sq_pairing_le_of_commonInterval` and `Multitile.sum_norm_sq_coeff_le`: for `g ∈ L²`
  supported in `C I_0` (`C ≥ 1`, dilate with respect to the center),
  `∑_{P : I = I_0} |⟨g, φ_P⟩|² ≤ 2 C |I_0| ∫ |g φ_{P_0}|²`, for any multitile `P_0` with `I = I_0`;
* `Multitile.sqrt_sum_norm_sq_coeff_le`: the `ℓ²`-form of L2500-L2504,
  `(∑ |⟨g, φ_P⟩|²)^{1/2} ≤ √(2 C |I_0|) ‖g φ_{P_0}‖_{L²}`;
  `memLp_two_of_bounded_of_support_subset_dilate`: a bounded measurable function supported in
  `C I_0` is in `L²`, so the hypothesis `g ∈ L²` is automatic for the functions `1_K f''`, `1_F f`
  used in the later applications.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap ContDiff ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

/-! ### Bessel's inequality for the exponentials -/

/-- `∫_a^{a + nT} e(j x/T) dx = 0` for a nonzero integer `j`. -/
theorem integral_e_mul_div_Ico {T : ℝ} (hT : 0 < T) (n : ℕ) (a : ℝ) {j : ℤ} (hj : j ≠ 0) :
    ∫ x in Ico a (a + n * T), e (j * x / T) = 0 := by
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by
    have : (0 : ℝ) ≤ n * T := by positivity
    linarith)]
  have hc : (2 * Real.pi * Complex.I * (j : ℂ) / T : ℂ) ≠ 0 := by
    have : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have : (j : ℂ) ≠ 0 := by exact_mod_cast hj
    simp [Real.pi_ne_zero, *]
  have h1 : ∀ x : ℝ, e (j * x / T) = Complex.exp ((2 * Real.pi * Complex.I * (j : ℂ) / T) * x) := by
    intro x
    unfold e
    congr 1
    push_cast
    ring
  simp_rw [h1]
  rw [integral_exp_mul_complex hc]
  have h2 : Complex.exp ((2 * Real.pi * Complex.I * (j : ℂ) / T) * ((a + n * T : ℝ) : ℂ)) =
      Complex.exp ((2 * Real.pi * Complex.I * (j : ℂ) / T) * (a : ℂ)) := by
    have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have : (2 * Real.pi * Complex.I * (j : ℂ) / T) * ((a + n * T : ℝ) : ℂ) =
        (2 * Real.pi * Complex.I * (j : ℂ) / T) * (a : ℂ) +
          ((n * j : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      field_simp
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h2, sub_self, zero_div]


/-- **Bessel's inequality for the exponentials `e(m x/T)` on an interval of length `nT`**:
for `u ∈ L²` supported in `[a, a + nT)` and distinct integers `m ∈ M`,
`∑_m |∫ u(x) e(-m x/T) dx|² ≤ nT ∫ |u|²`. -/
theorem sum_norm_sq_integral_mul_e_le {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : 0 < n) (a : ℝ)
    {u : ℝ → ℂ} (hu : MemLp u 2 volume) (hsupp : Function.support u ⊆ Ico a (a + n * T))
    (M : Finset ℤ) :
    ∑ m ∈ M, ‖∫ x, u x * e (-(m * x / T))‖ ^ 2 ≤ n * T * ∫ x, ‖u x‖ ^ 2 := by
  set A := Ico a (a + n * T) with hA
  set μ : Measure ℝ := volume.restrict A with hμ
  set Lg : ℝ := n * T with hLg
  have hLg0 : 0 < Lg := by positivity
  have : IsFiniteMeasure μ := ⟨by
    rw [hμ, Measure.restrict_apply_univ, hA, Real.volume_Ico]; simp⟩
  set E : ℤ → ℝ → ℂ := fun m x => e (m * x / T) with hE
  have hEcont : ∀ m, Continuous (E m) := fun m => continuous_e.comp (by fun_prop)
  have hEmem : ∀ m, MemLp (E m) 2 μ := fun m =>
    MemLp.of_bound (hEcont m).aestronglyMeasurable 1
      (Eventually.of_forall fun x => by simp [E, norm_e])
  have hu' : MemLp u 2 μ := hu.restrict A
  -- the inner products of the exponentials
  have hinner : ∀ i j : ℤ, inner ℂ ((hEmem i).toLp (E i)) ((hEmem j).toLp (E j)) =
      if i = j then (Lg : ℂ) else 0 := by
    intro i j
    rw [MeasureTheory.L2.inner_def]
    have h1 : (fun a : ℝ => inner ℂ (((hEmem i).toLp (E i) : ℝ →₂[μ] ℂ) a)
        (((hEmem j).toLp (E j) : ℝ →₂[μ] ℂ) a)) =ᵐ[μ] fun x => e (((j - i : ℤ) : ℝ) * x / T) := by
      filter_upwards [(hEmem i).coeFn_toLp, (hEmem j).coeFn_toLp] with x hxi hxj
      rw [hxi, hxj, RCLike.inner_apply]
      simp only [E]
      rw [← e_neg, ← e_add]
      congr 1
      push_cast
      ring
    rw [integral_congr_ae h1]
    by_cases hij : i = j
    · subst hij
      simp only [sub_self, Int.cast_zero, zero_mul, zero_div, e_zero, ite_true, integral_const,
        hμ, Measure.restrict_apply_univ, hA, Real.volume_Ico, Measure.real]
      rw [ENNReal.toReal_ofReal (by linarith)]
      simp [Lg]
    · rw [ite_eq_right_iff.2 (fun h => absurd h hij)]
      have hj : (j - i : ℤ) ≠ 0 := sub_ne_zero.2 (Ne.symm hij)
      exact integral_e_mul_div_Ico hT n a hj
  set v : ℤ → (ℝ →₂[μ] ℂ) := fun m => (((Lg ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (hEmem m).toLp (E m)
    with hv
  have hLgpow : ((Lg ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((Lg ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (Lg : ℂ) = 1 := by
    have : Lg ^ (-(1 / 2 : ℝ)) * Lg ^ (-(1 / 2 : ℝ)) * Lg = 1 := by
      rw [← Real.rpow_add hLg0]
      norm_num
      rw [Real.rpow_neg_one]
      field_simp
    exact_mod_cast this
  have hort : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [hv, inner_smul_left, inner_smul_right, hinner]
    simp only [Complex.conj_ofReal]
    split_ifs
    · rw [← mul_assoc]; exact hLgpow
    · simp
  have hb := hort.sum_inner_products_le (hu'.toLp u) (s := M)
  have hzero : ∀ x ∉ A, u x = 0 := fun x hx => by
    by_contra h
    exact hx (hsupp (Function.mem_support.2 h))
  have hcm : ∀ m : ℤ, inner ℂ ((hEmem m).toLp (E m)) (hu'.toLp u) =
      ∫ x, u x * e (-(m * x / T)) := by
    intro m
    rw [MeasureTheory.L2.inner_def]
    have h1 : (fun a : ℝ => inner ℂ (((hEmem m).toLp (E m) : ℝ →₂[μ] ℂ) a)
        ((hu'.toLp u : ℝ →₂[μ] ℂ) a)) =ᵐ[μ] fun x => u x * e (-(m * x / T)) := by
      filter_upwards [(hEmem m).coeFn_toLp, hu'.coeFn_toLp] with x hxi hxj
      rw [hxi, hxj, RCLike.inner_apply]
      simp only [E]
      rw [← e_neg]
    rw [integral_congr_ae h1, hμ]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hzero x hx]
  have hnorm : ‖hu'.toLp u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
    have h1 : inner ℂ (hu'.toLp u) (hu'.toLp u) = ((‖hu'.toLp u‖ : ℝ) : ℂ) ^ 2 :=
      inner_self_eq_norm_sq_to_K _
    rw [MeasureTheory.L2.inner_def] at h1
    have h2 : (fun a : ℝ => inner ℂ ((hu'.toLp u : ℝ →₂[μ] ℂ) a) ((hu'.toLp u : ℝ →₂[μ] ℂ) a))
        =ᵐ[μ] fun x => (((‖u x‖ ^ 2 : ℝ)) : ℂ) := by
      filter_upwards [hu'.coeFn_toLp] with x hx
      rw [hx, inner_self_eq_norm_sq_to_K]
      push_cast; rfl
    have h3 : ∫ x, ‖u x‖ ^ 2 ∂μ = ∫ x, ‖u x‖ ^ 2 := by
      rw [hμ]
      exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hzero x hx]
    rw [integral_congr_ae h2, integral_complex_ofReal, h3] at h1
    exact_mod_cast h1.symm
  rw [hnorm] at hb
  have hterm : ∀ m : ℤ, ‖inner ℂ (v m) (hu'.toLp u)‖ ^ 2 =
      Lg⁻¹ * ‖∫ x, u x * e (-(m * x / T))‖ ^ 2 := by
    intro m
    simp only [hv, inner_smul_left, hcm, Complex.conj_ofReal, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hLg0 _), mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLg0.le]
    norm_num
    rw [Real.rpow_neg_one]
  simp_rw [hterm] at hb
  rw [← Finset.mul_sum] at hb
  rw [inv_mul_le_iff₀ hLg0] at hb
  exact hb


/-! ### The packets of one time interval are modulates of one another -/

/-- The envelope `√|I| (2|I|)⁻¹ 𝓕⁻[√χ]((x - c(I))/(2|I|))` of the wave packets with time interval
`I`: `φ_{I×J}(x) = e(c(J)(x - c(I))) env(x)` for every `J` with `|I||J| = 1/2`. -/
def packetEnvelope (χ : ℝ → ℝ) (I : Dyadic) (x : ℝ) : ℂ :=
  ((√I.length : ℝ) : ℂ) * (((2 * I.length)⁻¹ : ℝ) : ℂ) *
    𝓕⁻ (sqrtProfile χ) ((2 * I.length)⁻¹ * (x - I.center))

/-- `|J| = (2|I|)⁻¹` for `|I||J| = 1/2`. -/
theorem Dyadic.length_eq_inv_of_area {I J : Dyadic} (hk : I.k + J.k = -1) :
    J.length = (2 * I.length)⁻¹ := by
  have hI := I.length_pos
  have harea : I.length * J.length = 1 / 2 := (Dyadic.area_iff I J).1 hk
  field_simp
  linarith

/-- **The wave packets with a common time interval are modulates of one another**
([O+] L1766-L1768): `φ_{I×J}(x) = e(c(J)(x - c(I))) · env_χ,I(x)` for every `J` with
`|I||J| = 1/2`. -/
theorem wavePacketOf_eq_mul_packetEnvelope (χ : ℝ → ℝ) {I J : Dyadic} (hk : I.k + J.k = -1)
    (x : ℝ) :
    wavePacketOf χ I J x = e (J.center * (x - I.center)) * packetEnvelope χ I x := by
  have hL := Dyadic.length_eq_inv_of_area hk
  have h1 := modulated_wavePacketOf χ I J x
  have h2 : wavePacketOf χ I J x = e (J.center * x) * (e (-(J.center * x)) *
      wavePacketOf χ I J x) := by
    rw [← mul_assoc, ← e_add, add_neg_cancel, e_zero, one_mul]
  rw [h2, h1, hL]
  unfold packetEnvelope
  have h3 : e (J.center * x) * e (-(J.center * I.center)) = e (J.center * (x - I.center)) := by
    rw [← e_add]; congr 1; ring
  calc e (J.center * x) * (((√I.length : ℝ) : ℂ) * (((2 * I.length)⁻¹ : ℝ) : ℂ) *
        e (-(J.center * I.center)) * 𝓕⁻ (sqrtProfile χ) ((2 * I.length)⁻¹ * (x - I.center)))
      = (e (J.center * x) * e (-(J.center * I.center))) * (((√I.length : ℝ) : ℂ) *
        (((2 * I.length)⁻¹ : ℝ) : ℂ) * 𝓕⁻ (sqrtProfile χ) ((2 * I.length)⁻¹ * (x - I.center))) := by
        ring
    _ = _ := by rw [h3]

/-- The modulus of a packet is the modulus of the envelope: `|φ_{I×J}| = |env_{χ,I}|`. -/
theorem norm_wavePacketOf_eq_norm_packetEnvelope (χ : ℝ → ℝ) {I J : Dyadic}
    (hk : I.k + J.k = -1) (x : ℝ) :
    ‖wavePacketOf χ I J x‖ = ‖packetEnvelope χ I x‖ := by
  rw [wavePacketOf_eq_mul_packetEnvelope χ hk, norm_mul, norm_e, one_mul]

/-- The packets of a common time interval have the same modulus: `|φ_{I×J}| = |φ_{I×J'}|`. -/
theorem norm_wavePacketOf_eq_of_same_interval (χ : ℝ → ℝ) {I J J' : Dyadic}
    (hk : I.k + J.k = -1) (hk' : I.k + J'.k = -1) (x : ℝ) :
    ‖wavePacketOf χ I J x‖ = ‖wavePacketOf χ I J' x‖ := by
  rw [norm_wavePacketOf_eq_norm_packetEnvelope χ hk, norm_wavePacketOf_eq_norm_packetEnvelope χ hk']

/-! ### The orthogonality for packets with a common time interval -/

variable {χ : ℝ → ℝ}

/-- `⌈C/2⌉ ≤ C` for `C ≥ 1`. -/
theorem nat_ceil_half_le {C : ℝ} (hC : 1 ≤ C) : ((⌈C / 2⌉₊ : ℕ) : ℝ) ≤ C := by
  rcases le_total C 2 with h | h
  · have : ⌈C / 2⌉₊ ≤ 1 := Nat.ceil_le.2 (by simpa using (by linarith : C / 2 ≤ 1))
    have h1 : ((⌈C / 2⌉₊ : ℕ) : ℝ) ≤ 1 := by exact_mod_cast this
    linarith
  · have := Nat.ceil_lt_add_one (show 0 ≤ C / 2 by positivity)
    linarith

/-- **Same-interval orthogonality** ([O+] `tileslargemaxprop`, L2500-L2504, and, for a fixed
dilation, `energyincrementprop`, L1766-L1776): let
`I` be a dyadic interval, `Ω` a finite set of dyadic intervals `J` with `|I||J| = 1/2` (the
frequency intervals of the distinct tiles with time interval `I`), `J₀` any one such interval,
`C ≥ 1`, and `g ∈ L²` supported in `C I` (the dilate with respect to the centre). Then
`∑_{J ∈ Ω} |⟨g, φ_{I×J}⟩|² ≤ 2 C |I| ∫ |g|² |φ_{I×J₀}|²`. -/
theorem sum_norm_sq_pairing_le_of_commonInterval (hχ : IsProfile χ) (I : Dyadic)
    (Ω : Finset Dyadic) (hΩ : ∀ J ∈ Ω, I.k + J.k = -1) {J₀ : Dyadic} (hJ₀ : I.k + J₀.k = -1)
    {C : ℝ} (hC : 1 ≤ C) {g : ℝ → ℂ} (hg : MemLp g 2 volume)
    (hsupp : Function.support g ⊆ I.dilate C) :
    ∑ J ∈ Ω, ‖pairing g (wavePacketOf χ I J)‖ ^ 2 ≤
      2 * C * I.length * ∫ x, ‖g x‖ ^ 2 * ‖wavePacketOf χ I J₀ x‖ ^ 2 := by
  have hI := I.length_pos
  set T : ℝ := 2 * I.length with hT
  have hT0 : 0 < T := by positivity
  set n : ℕ := ⌈C / 2⌉₊ with hn
  have hn0 : 0 < n := Nat.ceil_pos.2 (by positivity)
  have hnC : (n : ℝ) ≤ C := nat_ceil_half_le hC
  have hCn : C / 2 ≤ n := Nat.le_ceil _
  set a : ℝ := I.center - C * I.length / 2 with ha
  set env : ℝ → ℂ := packetEnvelope χ I with henv
  have henv_eq : env = fun x => e (-(J₀.center * (x - I.center))) * wavePacketOf χ I J₀ x := by
    funext x
    rw [henv, wavePacketOf_eq_mul_packetEnvelope χ hJ₀, ← mul_assoc, ← e_add, neg_add_cancel,
      e_zero, one_mul]
  have henv_cont : Continuous env := by
    rw [henv_eq]
    exact (continuous_e.comp (by fun_prop)).mul (hχ.continuous_wavePacketOf I J₀)
  obtain ⟨A, hA0, hA⟩ := hχ.exists_norm_wavePacketOf_le 0
  have henv_bdd : ∀ x, ‖env x‖ ≤ A * (√I.length)⁻¹ := by
    intro x
    rw [henv, ← norm_wavePacketOf_eq_norm_packetEnvelope χ hJ₀]
    simpa using hA I J₀ hJ₀ x
  set u : ℝ → ℂ := fun x => g x * (starRingEnd ℂ) (env x) * e (-(x / (2 * T))) with hu
  have hu_norm : ∀ x, ‖u x‖ = ‖g x‖ * ‖env x‖ := by
    intro x
    simp [hu, norm_e]
  have hu_meas : AEStronglyMeasurable u volume :=
    (hg.aestronglyMeasurable.mul (Complex.continuous_conj.comp henv_cont).aestronglyMeasurable).mul
      (continuous_e.comp (by fun_prop)).aestronglyMeasurable
  have hu_mem : MemLp u 2 volume := by
    refine hg.of_le_mul (c := A * (√I.length)⁻¹) hu_meas (Eventually.of_forall fun x => ?_)
    rw [hu_norm, mul_comm]
    exact mul_le_mul_of_nonneg_right (henv_bdd x) (norm_nonneg _)
  have hu_supp : Function.support u ⊆ Ico a (a + n * T) := by
    intro x hx
    have hgx : g x ≠ 0 := by
      intro h; apply hx; simp [hu, h]
    have hx' := hsupp (Function.mem_support.2 hgx)
    obtain ⟨h1, h2⟩ := hx'
    constructor
    · exact h1
    · have : a + C * I.length = I.center + C * I.length / 2 := by rw [ha]; ring
      have h3 : C * I.length ≤ n * T := by rw [hT]; nlinarith
      linarith
  -- the pairing as a Fourier coefficient of `u`
  have hpair : ∀ J ∈ Ω, ‖pairing g (wavePacketOf χ I J)‖ =
      ‖∫ x, u x * e (-((J.m : ℝ) * x / T))‖ := by
    intro J hJ
    have hk := hΩ J hJ
    have hL := Dyadic.length_eq_inv_of_area hk
    have hcen : J.center = (J.m + 1 / 2) / T := by
      have : J.center = J.length * (J.m + 1 / 2) := by
        unfold Dyadic.center Dyadic.length; ring
      rw [this, hL, hT]; field_simp
    have h1 : ∀ x : ℝ, g x * (starRingEnd ℂ) (wavePacketOf χ I J x) =
        e (J.center * I.center) * (u x * e (-((J.m : ℝ) * x / T))) := by
      intro x
      rw [wavePacketOf_eq_mul_packetEnvelope χ hk, map_mul, ← e_neg]
      have h2 : e (-(J.center * (x - I.center))) =
          e (J.center * I.center) * e (-(x / (2 * T))) * e (-((J.m : ℝ) * x / T)) := by
        rw [← e_add, ← e_add]; congr 1; rw [hcen]; field_simp; ring
      rw [h2, hu]
      simp only [henv]
      ring
    unfold pairing
    simp_rw [h1]
    rw [integral_const_mul, norm_mul, norm_e, one_mul]
  -- injectivity of `J ↦ J.m` on `Ω`
  have hinj : Set.InjOn Dyadic.m (Ω : Set Dyadic) := by
    intro J hJ J' hJ' h
    have e1 := hΩ J hJ
    have e2 := hΩ J' hJ'
    exact Dyadic.ext (by omega) h
  have hsum : ∑ J ∈ Ω, ‖pairing g (wavePacketOf χ I J)‖ ^ 2 =
      ∑ m ∈ Ω.image Dyadic.m, ‖∫ x, u x * e (-((m : ℝ) * x / T))‖ ^ 2 := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun J hJ => by rw [hpair J hJ]
  rw [hsum]
  refine (sum_norm_sq_integral_mul_e_le hT0 hn0 a hu_mem hu_supp _).trans ?_
  have hint : ∫ x, ‖u x‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 * ‖wavePacketOf χ I J₀ x‖ ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [hu_norm, mul_pow, henv, norm_wavePacketOf_eq_norm_packetEnvelope χ hJ₀]
  rw [hint]
  have hnn : 0 ≤ ∫ x, ‖g x‖ ^ 2 * ‖wavePacketOf χ I J₀ x‖ ^ 2 :=
    integral_nonneg fun x => by positivity
  have : (n : ℝ) * T ≤ 2 * C * I.length := by rw [hT]; nlinarith
  exact mul_le_mul_of_nonneg_right this hnn

/-- **Same-interval orthogonality for `ρ`-multitiles**: let `S` be a finite set of `ρ`-multitiles
with the common time interval `I₀` (distinct multitiles have distinct `ω_u`), `P₀` any
multitile with `P₀.I = I₀`, `C ≥ 1` and `g ∈ L²` supported in `C I₀`. Then
`∑_{P ∈ S} |⟨g, φ_P⟩|² ≤ 2 C |I₀| ∫ |g|² |φ_{P₀}|²`, for every profile choice. -/
theorem Multitile.sum_norm_sq_coeff_le {ρ : Idx} (ch : ProfileChoice) (S : Finset (Multitile ρ))
    {I₀ : Dyadic} (hS : ∀ P ∈ S, P.I = I₀) {P₀ : Multitile ρ} (hP₀ : P₀.I = I₀) {C : ℝ}
    (hC : 1 ≤ C) {g : ℝ → ℂ} (hg : MemLp g 2 volume)
    (hsupp : Function.support g ⊆ I₀.dilate C) :
    ∑ P ∈ S, ‖P.coeff ch g‖ ^ 2 ≤
      2 * C * I₀.length * ∫ x, ‖g x‖ ^ 2 * ‖P₀.wavePacket ch x‖ ^ 2 := by
  classical
  have hinj : Set.InjOn Multitile.ωu (S : Set (Multitile ρ)) := by
    intro P hP P' hP' h
    exact Multitile.ext ((hS P hP).trans (hS P' hP').symm) h
  have hsum : ∑ P ∈ S, ‖P.coeff ch g‖ ^ 2 =
      ∑ J ∈ S.image Multitile.ωu, ‖pairing g (wavePacketOf ch.fn I₀ J)‖ ^ 2 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun P hP => ?_
    have := hS P hP
    unfold Multitile.coeff Multitile.wavePacket Multitile.packetOf
    rw [this]
  rw [hsum]
  have hΩ : ∀ J ∈ S.image Multitile.ωu, I₀.k + J.k = -1 := by
    intro J hJ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hJ
    have := P.area
    rw [hS P hP] at this
    exact this
  have hk₀ : I₀.k + P₀.ωu.k = -1 := by
    have := P₀.area
    rw [hP₀] at this
    exact this
  have h := sum_norm_sq_pairing_le_of_commonInterval ch.isProfile I₀ _ hΩ hk₀ hC hg hsupp
  refine h.trans (le_of_eq ?_)
  congr 2
  funext x
  unfold Multitile.wavePacket Multitile.packetOf
  rw [hP₀]

/-- The `ℓ²`-form of same-interval orthogonality, as written at L2500-L2504 of [O+]:
`(∑_{P : I = I₀} |⟨g, φ_P⟩|²)^{1/2} ≤ √(2 C |I₀|) ‖g φ_{P₀}‖_{L²}`. -/
theorem Multitile.sqrt_sum_norm_sq_coeff_le {ρ : Idx} (ch : ProfileChoice)
    (S : Finset (Multitile ρ)) {I₀ : Dyadic} (hS : ∀ P ∈ S, P.I = I₀) {P₀ : Multitile ρ}
    (hP₀ : P₀.I = I₀) {C : ℝ} (hC : 1 ≤ C) {g : ℝ → ℂ} (hg : MemLp g 2 volume)
    (hsupp : Function.support g ⊆ I₀.dilate C) :
    √(∑ P ∈ S, ‖P.coeff ch g‖ ^ 2) ≤
      √(2 * C * I₀.length) * √(∫ x, ‖g x‖ ^ 2 * ‖P₀.wavePacket ch x‖ ^ 2) := by
  rw [← Real.sqrt_mul (by have := I₀.length_pos; positivity)]
  exact Real.sqrt_le_sqrt (Multitile.sum_norm_sq_coeff_le ch S hS hP₀ hC hg hsupp)

/-- A (almost everywhere) bounded measurable function supported in a dilate of a dyadic interval
is in `L²`. -/
theorem memLp_two_of_bounded_of_support_subset_dilate {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g volume) {B : ℝ} (hB : ∀ᵐ x, ‖g x‖ ≤ B) {I : Dyadic} {C : ℝ}
    (hsupp : Function.support g ⊆ I.dilate C) : MemLp g 2 volume := by
  have hmeas : MeasurableSet (I.dilate C) := measurableSet_Ico
  have h1 : g = (I.dilate C).indicator g := by
    funext x
    by_cases hx : x ∈ I.dilate C
    · simp [hx]
    · have : g x = 0 := by
        by_contra h; exact hx (hsupp (Function.mem_support.2 h))
      simp [hx, this]
  rw [h1, memLp_indicator_iff_restrict hmeas.nullMeasurableSet]
  have : IsFiniteMeasure (volume.restrict (I.dilate C)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ico_lt_top⟩
  exact MemLp.of_bound (hg.restrict) B (ae_restrict_of_ae hB)

end PrimeCarleson.Proof.Oplus

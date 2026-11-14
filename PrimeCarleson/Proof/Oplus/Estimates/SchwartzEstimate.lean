module

public import PrimeCarleson.Proof.Oplus.Estimates.WavePacketBound

/-!
# Inner products of two wave packets ([O+] L1537-L1543)

[O+] L1537-L1543: "In both cases, we will use the estimate
`|⟨φ_P, φ_{P'}⟩| ≲ (|I|/|I'|)^{1/2} ⟨w_I, 1_{I'}⟩` which holds whenever `|I'| ≤ |I|`." Source: [O+]
`schwartzestimate`, L1537–L1543 (stated without proof). It is a consequence of the pointwise
bound `|φ_P(x)| ≲ |I|^{-1/2}(1 + |x - c(I)|/|I)^{-N}` of `wavepacketadaptedbound`
(`n = 0`) alone: no oscillation is used.

* `Dyadic.weight_le_mul_weight`: a Peetre-type inequality `w_I(x) ≤ (3/2)^N (1 + |x - c(I')|/|I'|)^N
  w_I(x')` for `x' ∈ I'`, `|I'| ≤ |I|`;
* `IsProfile.exists_norm_pairing_wavePacketOf_le`: the estimate for two (possibly different) fixed
  profiles, `‖⟨φ_{I×J}, φ_{I'×J'}⟩‖ ≤ C √(|I|/|I'|) ∫_{I'} w_I` with `C` depending only on the
  profiles and on `N`;
* `ProfileChoice.exists_norm_pairing_le`: the same constant for the six profile choices, stated for
  `ρ`-multitiles of every index (`Multitile.exists_norm_pairing_wavePacket_le`);
* `pairing_wavePacketOf_eq_zero_of_support`: `⟨φ_P, φ_{P'}⟩ = 0` if the Fourier supports of the two
  packets lie in disjoint sets (Plancherel); `norm_pairing_comm`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap ContDiff ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

/-! ### A Peetre-type inequality for the weights -/

/-- `w_I(x) = |I|⁻¹ ((1 + |x - c(I)|/|I|)^N)⁻¹`. -/
theorem Dyadic.weight_eq_inv (N : ℕ) (I : Dyadic) (x : ℝ) :
    I.weight N x = I.length⁻¹ * ((1 + |x - I.center| / I.length) ^ N)⁻¹ := by
  simp [weight, zpow_neg, zpow_natCast]

/-- A point of a dyadic interval is within `|I|/2` of its center. -/
theorem Dyadic.abs_sub_center_le {I : Dyadic} {x : ℝ} (hx : x ∈ I.toSet) :
    |x - I.center| ≤ I.length / 2 := by
  obtain ⟨h1, h2⟩ := hx
  rw [abs_le]
  have := I.right_eq
  have := I.center_eq
  constructor <;> linarith

/-- **Peetre's inequality for the weights**: for `|I'| ≤ |I|` and `x' ∈ I'`,
`w_I(x) ≤ (3/2)^N (1 + |x - c(I')|/|I'|)^N w_I(x')`. -/
theorem Dyadic.weight_le_mul_weight (N : ℕ) {I I' : Dyadic} (hle : I'.length ≤ I.length) (x : ℝ)
    {x' : ℝ} (hx' : x' ∈ I'.toSet) :
    I.weight N x ≤ (3 / 2) ^ N * (1 + |x - I'.center| / I'.length) ^ N * I.weight N x' := by
  have hI := I.length_pos
  have hI' := I'.length_pos
  set a := |x - I.center| / I.length with ha
  set a' := |x' - I.center| / I.length with ha'
  set t := |x - I'.center| / I'.length with ht
  have ha0 : 0 ≤ a := by positivity
  have ht0 : 0 ≤ t := by positivity
  have h1 : |x' - I.center| ≤ |x - I.center| + (|x - I'.center| + I'.length / 2) := by
    have e1 : |x' - I.center| ≤ |x - I.center| + |x - x'| := by
      calc |x' - I.center| = |(x - I.center) - (x - x')| := by congr 1; ring
        _ ≤ |x - I.center| + |x - x'| := by
          have := abs_sub (x - I.center) (x - x')
          exact this
    have e2 : |x - x'| ≤ |x - I'.center| + I'.length / 2 := by
      calc |x - x'| = |(x - I'.center) + (I'.center - x')| := by congr 1; ring
        _ ≤ |x - I'.center| + |I'.center - x'| := abs_add_le _ _
        _ ≤ _ := by
          rw [abs_sub_comm I'.center x']
          have := Dyadic.abs_sub_center_le hx'
          linarith
    linarith
  have h2 : a' ≤ a + (t + 1 / 2) := by
    have e3 : (|x - I'.center| + I'.length / 2) / I.length ≤ t + 1 / 2 := by
      calc (|x - I'.center| + I'.length / 2) / I.length
          ≤ (|x - I'.center| + I'.length / 2) / I'.length :=
            div_le_div_of_nonneg_left (by positivity) hI' hle
        _ = t + 1 / 2 := by rw [ht]; field_simp
    calc a' = |x' - I.center| / I.length := rfl
      _ ≤ (|x - I.center| + (|x - I'.center| + I'.length / 2)) / I.length :=
          div_le_div_of_nonneg_right h1 hI.le
      _ = a + (|x - I'.center| + I'.length / 2) / I.length := by rw [ha]; ring
      _ ≤ _ := by linarith
  have h3 : 1 + a' ≤ (1 + a) * ((3 / 2) * (1 + t)) := by nlinarith
  have h4 : (1 + a') ^ N ≤ (1 + a) ^ N * ((3 / 2) ^ N * (1 + t) ^ N) := by
    calc (1 + a') ^ N ≤ ((1 + a) * ((3 / 2) * (1 + t))) ^ N :=
          pow_le_pow_left₀ (by positivity) h3 N
      _ = _ := by rw [mul_pow, mul_pow]
  rw [Dyadic.weight_eq_inv, Dyadic.weight_eq_inv]
  have hpa : (0 : ℝ) < (1 + a) ^ N := by positivity
  have hpa' : (0 : ℝ) < (1 + a') ^ N := by positivity
  have h5 : ((1 + a) ^ N)⁻¹ ≤ (3 / 2) ^ N * (1 + t) ^ N * ((1 + a') ^ N)⁻¹ := by
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hpa hpa']
    nlinarith
  calc I.length⁻¹ * ((1 + a) ^ N)⁻¹
      ≤ I.length⁻¹ * ((3 / 2) ^ N * (1 + t) ^ N * ((1 + a') ^ N)⁻¹) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = _ := by ring

/-! ### The estimate `|⟨φ_P, φ_{P'}⟩| ≲ (|I|/|I'|)^{1/2} ⟨w_I, 1_{I'}⟩` -/

/-- The weight integrated against the shifted weight: for `|I'| ≤ |I|` and `N ≥ 0`,
`∫ w_I(x) (1 + |x - c(I')|/|I'|)^{-(N+2)} dx ≤ 2 (3/2)^N ∫_{I'} w_I`. -/
theorem Dyadic.integral_weight_mul_le (N : ℕ) {I I' : Dyadic} (hle : I'.length ≤ I.length) :
    ∫ x, I.weight N x * (1 + |x - I'.center| / I'.length) ^ (-((N + 2 : ℕ) : ℤ)) ≤
      2 * (3 / 2) ^ N * ∫ x in I'.toSet, I.weight N x := by
  have hI := I.length_pos
  have hI' := I'.length_pos
  set K := ∫ x in I'.toSet, I.weight N x with hK
  have hint : IntegrableOn (I.weight N) I'.toSet :=
    ((I.continuous_weight N).integrableOn_Icc (a := I'.left) (b := I'.right)).mono_set
      Ico_subset_Icc_self
  -- pointwise bound
  have hpt : ∀ x : ℝ, I.weight N x * (1 + |x - I'.center| / I'.length) ^ (-((N + 2 : ℕ) : ℤ)) ≤
      (3 / 2) ^ N * I'.length⁻¹ * K * (1 + |x - I'.center| / I'.length) ^ (-(2 : ℤ)) := by
    intro x
    set t := |x - I'.center| / I'.length with ht
    have ht0 : 0 ≤ t := by positivity
    have h1 : I'.length * I.weight N x ≤ (3 / 2) ^ N * (1 + t) ^ N * K := by
      have h2 : ∫ x' in I'.toSet, I.weight N x = I'.length * I.weight N x := by
        rw [setIntegral_const, smul_eq_mul]
        simp [Dyadic.volume_toSet, I'.length_pos.le, Measure.real]
      calc I'.length * I.weight N x = ∫ x' in I'.toSet, I.weight N x := h2.symm
        _ ≤ ∫ x' in I'.toSet, (3 / 2) ^ N * (1 + t) ^ N * I.weight N x' := by
            refine setIntegral_mono_on (integrableOn_const (by simp [Dyadic.volume_toSet]))
              (hint.const_mul _) I'.measurableSet_toSet fun x' hx' => ?_
            exact Dyadic.weight_le_mul_weight N hle x hx'
        _ = (3 / 2) ^ N * (1 + t) ^ N * K := by rw [integral_const_mul]
    have h3 : I.weight N x ≤ (3 / 2) ^ N * (1 + t) ^ N * I'.length⁻¹ * K := by
      calc I.weight N x ≤ (3 / 2) ^ N * (1 + t) ^ N * K / I'.length := by
            rw [le_div_iff₀' hI']; exact h1
        _ = _ := by ring
    have h4 : (1 + t) ^ (-((N + 2 : ℕ) : ℤ)) * (1 + t) ^ N = (1 + t) ^ (-(2 : ℤ)) := by
      rw [← zpow_natCast, ← zpow_add₀ (by positivity)]
      congr 1; push_cast; ring
    have h5 : 0 ≤ (1 + t) ^ (-((N + 2 : ℕ) : ℤ)) := by positivity
    calc I.weight N x * (1 + t) ^ (-((N + 2 : ℕ) : ℤ))
        ≤ ((3 / 2) ^ N * (1 + t) ^ N * I'.length⁻¹ * K) * (1 + t) ^ (-((N + 2 : ℕ) : ℤ)) :=
          mul_le_mul_of_nonneg_right h3 h5
      _ = (3 / 2) ^ N * I'.length⁻¹ * K * ((1 + t) ^ (-((N + 2 : ℕ) : ℤ)) * (1 + t) ^ N) := by
          ring
      _ = _ := by rw [h4]
  have hint2 : Integrable (fun x : ℝ => (3 / 2 : ℝ) ^ N * I'.length⁻¹ * K *
      (1 + |x - I'.center| / I'.length) ^ (-(2 : ℤ))) := by
    have := integrable_one_add_abs_div_zpow (N := 2) (le_refl 2) I'.center hI'
    simpa using this.const_mul ((3 / 2 : ℝ) ^ N * I'.length⁻¹ * K)
  have hmeas : Continuous (fun x : ℝ => I.weight N x *
      (1 + |x - I'.center| / I'.length) ^ (-((N + 2 : ℕ) : ℤ))) := by
    refine (I.continuous_weight N).mul (Continuous.zpow₀ (by fun_prop) _ fun x => Or.inl ?_)
    positivity
  calc ∫ x, I.weight N x * (1 + |x - I'.center| / I'.length) ^ (-((N + 2 : ℕ) : ℤ))
      ≤ ∫ x, (3 / 2 : ℝ) ^ N * I'.length⁻¹ * K *
        (1 + |x - I'.center| / I'.length) ^ (-(2 : ℤ)) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => ?_) hint2
          (Eventually.of_forall hpt)
        have := I.weight_nonneg N x
        positivity
    _ = 2 * (3 / 2) ^ N * K := by
        rw [integral_const_mul]
        have h := integral_one_add_abs_div_zpow (N := 2) (le_refl 2) I'.center hI'
        have h22 : (-((2 : ℕ) : ℤ)) = -(2 : ℤ) := by norm_num
        rw [h22] at h
        rw [h]
        norm_num
        field_simp

variable {χ χ' : ℝ → ℝ}

/-- **The estimate `|⟨φ_P, φ_{P'}⟩| ≲ (|I|/|I'|)^{1/2} ⟨w_I, 1_{I'}⟩` for `|I'| ≤ |I|`**
([O+] `schwartzestimate`, L1537-L1543) for two fixed profiles: for every `N` there is `C ≥ 0`,
depending only on `χ, χ', N`, such that for all tiles `I × J`, `I' × J'` with `|I'| ≤ |I|`,
`‖⟨φ_{I×J}, φ_{I'×J'}⟩‖ ≤ C √(|I|/|I'|) ∫_{I'} w_I`. -/
theorem IsProfile.exists_norm_pairing_wavePacketOf_le (hχ : IsProfile χ) (hχ' : IsProfile χ')
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ I J I' J' : Dyadic, I.k + J.k = -1 → I'.k + J'.k = -1 →
      I'.length ≤ I.length →
      ‖pairing (wavePacketOf χ I J) (wavePacketOf χ' I' J')‖ ≤
        C * √(I.length / I'.length) * ∫ x in I'.toSet, I.weight N x := by
  obtain ⟨A, hA0, hA⟩ := hχ.exists_norm_wavePacketOf_le N
  obtain ⟨A', hA'0, hA'⟩ := hχ'.exists_norm_wavePacketOf_le (N + 2)
  refine ⟨2 * A * A' * (3 / 2) ^ N, by positivity, fun I J I' J' hk hk' hle => ?_⟩
  have hI := I.length_pos
  have hI' := I'.length_pos
  set s := √I.length with hs
  set s' := √I'.length with hs'
  have hs0 : 0 < s := Real.sqrt_pos.2 hI
  have hs'0 : 0 < s' := Real.sqrt_pos.2 hI'
  set B : ℝ → ℝ := fun x => A * A' * (s * s'⁻¹) *
    (I.weight N x * (1 + |x - I'.center| / I'.length) ^ (-((N + 2 : ℕ) : ℤ))) with hB
  have hpt : ∀ x, ‖wavePacketOf χ I J x * (starRingEnd ℂ) (wavePacketOf χ' I' J' x)‖ ≤ B x := by
    intro x
    rw [norm_mul, Complex.norm_conj]
    have h1 := hA I J hk x
    have h2 := hA' I' J' hk' x
    have h1' : ‖wavePacketOf χ I J x‖ ≤ A * (s * I.weight N x) := by
      rw [hs, Dyadic.sqrt_length_mul_weight, ← mul_assoc]; exact h1
    have h3 := mul_le_mul h1' h2 (norm_nonneg _) (by have := I.weight_nonneg N x; positivity)
    refine h3.trans (le_of_eq ?_)
    rw [hB]
    simp only [hs, hs']
    ring
  have hcont : Continuous B := by
    refine continuous_const.mul ((I.continuous_weight N).mul
      (Continuous.zpow₀ (by fun_prop) _ fun x => Or.inl ?_))
    positivity
  have hBint : Integrable B := by
    have hdom : Integrable (fun x : ℝ => A * A' * (s * s'⁻¹) * I.length⁻¹ *
        (1 + |x - I'.center| / I'.length) ^ (-(2 : ℤ))) := by
      have := integrable_one_add_abs_div_zpow (N := 2) (le_refl 2) I'.center hI'
      simpa using this.const_mul (A * A' * (s * s'⁻¹) * I.length⁻¹)
    refine hdom.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    have ht : 1 ≤ 1 + |x - I'.center| / I'.length := by
      have : 0 ≤ |x - I'.center| / I'.length := by positivity
      linarith
    have hw : I.weight N x ≤ I.length⁻¹ := by
      rw [Dyadic.weight_eq_inv]
      refine mul_le_of_le_one_right (by positivity) ?_
      refine inv_le_one_of_one_le₀ ?_
      exact one_le_pow₀ (by have : 0 ≤ |x - I.center| / I.length := by positivity
                            linarith)
    have hz : (1 + |x - I'.center| / I'.length) ^ (-((N + 2 : ℕ) : ℤ)) ≤
        (1 + |x - I'.center| / I'.length) ^ (-(2 : ℤ)) := by
      apply zpow_le_zpow_right₀ ht
      push_cast; omega
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := I.weight_nonneg N x; positivity)]
    calc B x = A * A' * (s * s'⁻¹) * (I.weight N x *
          (1 + |x - I'.center| / I'.length) ^ (-((N + 2 : ℕ) : ℤ))) := rfl
      _ ≤ A * A' * (s * s'⁻¹) * (I.length⁻¹ *
          (1 + |x - I'.center| / I'.length) ^ (-(2 : ℤ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hw hz (by positivity) (by positivity)
      _ = _ := by ring
  have h1 : ‖pairing (wavePacketOf χ I J) (wavePacketOf χ' I' J')‖ ≤ ∫ x, B x :=
    norm_integral_le_of_norm_le hBint (Eventually.of_forall hpt)
  refine h1.trans ?_
  have h2 := Dyadic.integral_weight_mul_le N hle
  calc ∫ x, B x = A * A' * (s * s'⁻¹) * ∫ x, I.weight N x *
        (1 + |x - I'.center| / I'.length) ^ (-((N + 2 : ℕ) : ℤ)) := by
        rw [hB]; simp only; rw [integral_const_mul]
    _ ≤ A * A' * (s * s'⁻¹) * (2 * (3 / 2) ^ N * ∫ x in I'.toSet, I.weight N x) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by
        rw [Real.sqrt_div hI.le, hs, hs']
        ring

/-- **The estimate of `schwartzestimate`, uniform in the six profile choices** (`ν_i`,
`ν_i(-·)`, possibly different for the two packets): for every `N` there is `C ≥ 0` such that for all
tiles `I × J`, `I' × J'` with `|I'| ≤ |I|`,
`‖⟨φ_{I×J}, φ_{I'×J'}⟩‖ ≤ C √(|I|/|I'|) ∫_{I'} w_I`. -/
theorem ProfileChoice.exists_norm_pairing_le (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c c' : ProfileChoice) (I J I' J' : Dyadic), I.k + J.k = -1 →
      I'.k + J'.k = -1 → I'.length ≤ I.length →
      ‖pairing (wavePacketOf c.fn I J) (wavePacketOf c'.fn I' J')‖ ≤
        C * √(I.length / I'.length) * ∫ x in I'.toSet, I.weight N x := by
  have key : ∀ c c' : ProfileChoice, ∃ C : ℝ, 0 ≤ C ∧ ∀ I J I' J' : Dyadic, I.k + J.k = -1 →
      I'.k + J'.k = -1 → I'.length ≤ I.length →
      ‖pairing (wavePacketOf c.fn I J) (wavePacketOf c'.fn I' J')‖ ≤
        C * √(I.length / I'.length) * ∫ x in I'.toSet, I.weight N x :=
    fun c c' => c.isProfile.exists_norm_pairing_wavePacketOf_le c'.isProfile N
  have hnn : ∀ I I' : Dyadic, 0 ≤ √(I.length / I'.length) * ∫ x in I'.toSet, I.weight N x :=
    fun I I' => mul_nonneg (Real.sqrt_nonneg _) (setIntegral_nonneg I'.measurableSet_toSet
      fun x _ => I.weight_nonneg N x)
  obtain ⟨C, hC0, hC⟩ := exists_uniform_profileChoice
    (fun c C => ∀ c' : ProfileChoice, ∀ I J I' J' : Dyadic, I.k + J.k = -1 →
      I'.k + J'.k = -1 → I'.length ≤ I.length →
      ‖pairing (wavePacketOf c.fn I J) (wavePacketOf c'.fn I' J')‖ ≤
        C * √(I.length / I'.length) * ∫ x in I'.toSet, I.weight N x)
    (fun c C C' hCC' h c' I J I' J' hk hk' hle => by
      refine (h c' I J I' J' hk hk' hle).trans ?_
      have := hnn I I'
      nlinarith)
    (fun c => by
      obtain ⟨C, hC0, hC⟩ := exists_uniform_profileChoice
        (fun c' C => ∀ I J I' J' : Dyadic, I.k + J.k = -1 →
          I'.k + J'.k = -1 → I'.length ≤ I.length →
          ‖pairing (wavePacketOf c.fn I J) (wavePacketOf c'.fn I' J')‖ ≤
            C * √(I.length / I'.length) * ∫ x in I'.toSet, I.weight N x)
        (fun c' C C' hCC' h I J I' J' hk hk' hle => by
          refine (h I J I' J' hk hk' hle).trans ?_
          have := hnn I I'
          nlinarith)
        (fun c' => key c c')
      exact ⟨C, hC0, fun c' => hC c'⟩)
  exact ⟨C, hC0, fun c c' => hC c c'⟩

/-- **`schwartzestimate` for multitiles**: for every `N` there is `C ≥ 0`, independent of the
indices, the profile choices and the multitiles, with
`‖⟨φ_P, φ_{P'}⟩‖ ≤ C √(|I|/|I'|) ∫_{I'} w_I` whenever `|I'| ≤ |I|`. -/
theorem Multitile.exists_norm_pairing_wavePacket_le (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ ρ' : Idx) (ch ch' : ProfileChoice) (P : Multitile ρ)
      (P' : Multitile ρ'), P'.I.length ≤ P.I.length →
      ‖pairing (P.wavePacket ch) (P'.wavePacket ch')‖ ≤
        C * √(P.I.length / P'.I.length) * ∫ x in P'.I.toSet, P.I.weight N x := by
  obtain ⟨C, hC0, hC⟩ := ProfileChoice.exists_norm_pairing_le N
  exact ⟨C, hC0, fun ρ ρ' ch ch' P P' hle => hC ch ch' P.I P.ωu P'.I P'.ωu P.area P'.area hle⟩

/-! ### Packets with disjoint frequency supports are orthogonal -/

/-- `⟨g, f⟩` is the conjugate of `⟨f, g⟩`. -/
theorem pairing_comm_conj (f g : ℝ → ℂ) : pairing g f = (starRingEnd ℂ) (pairing f g) := by
  unfold pairing
  rw [← integral_conj]
  congr 1; funext x
  simp [mul_comm]

/-- `‖⟨g, f⟩‖ = ‖⟨f, g⟩‖`. -/
theorem norm_pairing_comm (f g : ℝ → ℂ) : ‖pairing g f‖ = ‖pairing f g‖ := by
  rw [pairing_comm_conj, Complex.norm_conj]

/-- **Orthogonality of packets with disjoint frequency supports**: if the supports of
`φ̂_{I×J}` and `φ̂_{I'×J'}` lie in disjoint sets `S`, `S'` then `⟨φ_{I×J}, φ_{I'×J'}⟩ = 0`
(Plancherel; [O+] L1549). -/
theorem pairing_wavePacketOf_eq_zero_of_support (hχ : IsProfile χ) (hχ' : IsProfile χ')
    (I J I' J' : Dyadic) {S S' : Set ℝ} (hS : Function.support (𝓕 (wavePacketOf χ I J)) ⊆ S)
    (hS' : Function.support (𝓕 (wavePacketOf χ' I' J')) ⊆ S') (h : Disjoint S S') :
    pairing (wavePacketOf χ I J) (wavePacketOf χ' I' J') = 0 := by
  set g := hχ.wavePacketSchwartz I J with hg
  set g' := hχ'.wavePacketSchwartz I' J' with hg'
  have hgf : (⇑g : ℝ → ℂ) = wavePacketOf χ I J := funext (hχ.wavePacketSchwartz_apply I J)
  have hgf' : (⇑g' : ℝ → ℂ) = wavePacketOf χ' I' J' := funext (hχ'.wavePacketSchwartz_apply I' J')
  have h1 := SchwartzMap.integral_inner_fourier_fourier g' g
  have h2 : ∀ ξ, inner ℂ ((𝓕 g' : 𝓢(ℝ, ℂ)) ξ) ((𝓕 g : 𝓢(ℝ, ℂ)) ξ) = 0 := by
    intro ξ
    have e1 : (⇑(𝓕 g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = 𝓕 (wavePacketOf χ I J) := by
      rw [SchwartzMap.fourier_coe, hgf]
    have e2 : (⇑(𝓕 g' : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = 𝓕 (wavePacketOf χ' I' J') := by
      rw [SchwartzMap.fourier_coe, hgf']
    rw [e1, e2, RCLike.inner_apply]
    by_cases hξ : ξ ∈ S
    · have : ξ ∉ S' := fun h' => Set.disjoint_left.1 h hξ h'
      have : 𝓕 (wavePacketOf χ' I' J') ξ = 0 := by
        by_contra hne
        exact this (hS' hne)
      simp [this]
    · have : 𝓕 (wavePacketOf χ I J) ξ = 0 := by
        by_contra hne
        exact hξ (hS hne)
      simp [this]
  simp_rw [h2] at h1
  simp only [integral_zero] at h1
  have h3 : ∀ x, inner ℂ (g' x) (g x) = g x * (starRingEnd ℂ) (g' x) := fun x => by
    simp [RCLike.inner_apply]
  simp_rw [h3] at h1
  unfold pairing
  rw [← hgf, ← hgf']
  exact h1.symm

end PrimeCarleson.Proof.Oplus

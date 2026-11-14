module

public import PrimeCarleson.Proof.Oplus.External.THAssembly
public import PrimeCarleson.Proof.Oplus.Estimates.All

/-!
# Modulated wave packets of a tree

Source: Grafakos–Tao–Terwilleger, L809–L812 and L885–L888.

For an `l`-overlapping tree `T` with top frequency `ξ_T`, the modulated packet
`ψ_P = e(-ξ_T ·) φ_P` satisfies (`exists_packetBounds_modulated`)
`|ψ_P| ≲ |I|^{-1/2} ω^{-4}` and `|ψ_P'| ≲ (1 + Λ) |I|^{-3/2} ω^{-4}` provided
`|ξ_T - c(ω_u)| ≤ Λ/(4|I|)` (for `P` in an `l`-overlapping tree `Λ = C₁`, since
`ξ_T ∈ C₂ ω_l ⊂ C₁ ω_u` and `|ω_u| = 1/(2|I|)`); `⟨f, φ_P⟩ = ⟨e(-ξ_T ·) f, ψ_P⟩`
(`pairing_modulate`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate FourierTransform SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-- `d/dy e(a y) = 2πi a e(a y)`. -/
theorem hasDerivAt_e_mul (a y : ℝ) :
    HasDerivAt (fun y : ℝ => e (a * y)) (2 * Real.pi * Complex.I * a * e (a * y)) y := by
  have h1 : HasDerivAt (fun y : ℝ => (2 * Real.pi * Complex.I * ((a * y : ℝ) : ℂ)))
      (2 * Real.pi * Complex.I * a) y := by
    have := ((hasDerivAt_id y).const_mul a).ofReal_comp
    have h2 := this.const_mul (2 * Real.pi * Complex.I)
    simpa using h2
  have h3 := h1.cexp
  unfold e
  convert h3 using 1
  ring

/-- `e(-ξ y) φ(y)` and `e(-ξ y) f(y)` have the same pairing as `φ`, `f`. -/
theorem pairing_modulate (f φ : ℝ → ℂ) (ξ : ℝ) :
    pairing (fun y => e (-(ξ * y)) * f y) (fun y => e (-(ξ * y)) * φ y) = pairing f φ := by
  unfold pairing
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [map_mul]
  have h : e (-(ξ * y)) * (starRingEnd ℂ) (e (-(ξ * y))) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_e]; simp
  calc e (-(ξ * y)) * f y * ((starRingEnd ℂ) (e (-(ξ * y))) * (starRingEnd ℂ) (φ y))
      = (e (-(ξ * y)) * (starRingEnd ℂ) (e (-(ξ * y)))) * (f y * (starRingEnd ℂ) (φ y)) := by
        ring
    _ = _ := by rw [h, one_mul]

/-- The Fourier-side transform of the pairing: `⟨g, e(-ξ ·) φ⟩ = ⟨e(ξ ·) g, φ⟩`; in particular
`|⟨g, ψ⟩|` is the pairing of `φ` with a function of the same `L²` norm. -/
theorem pairing_mul_e_eq (g φ : ℝ → ℂ) (ξ : ℝ) :
    pairing g (fun y => e (-(ξ * y)) * φ y) = pairing (fun y => e (ξ * y) * g y) φ := by
  unfold pairing
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [map_mul]
  have h : (starRingEnd ℂ) (e (-(ξ * y))) = e (ξ * y) := by
    rw [← e_neg]; simp
  rw [h]; ring

/-- A wave packet is differentiable. -/
theorem Multitile.differentiable_wavePacket {ρ : Idx} (ch : ProfileChoice) (P : Multitile ρ) :
    Differentiable ℝ (P.wavePacket ch) := by
  have : (P.wavePacket ch) = ⇑(ch.isProfile.wavePacketSchwartz P.I P.ωu) :=
    funext fun x => (ch.isProfile.wavePacketSchwartz_apply P.I P.ωu x).symm
  rw [this]
  exact (ch.isProfile.wavePacketSchwartz P.I P.ωu).differentiable

/-- `d/dy e(-(a y)) = -2πi a e(-(a y))`. -/
theorem hasDerivAt_e_neg_mul (a y : ℝ) :
    HasDerivAt (fun y : ℝ => e (-(a * y))) (-(2 * Real.pi * Complex.I * a) * e (-(a * y))) y := by
  have := hasDerivAt_e_mul (-a) y
  simp only [neg_mul] at this
  convert this using 1
  push_cast; ring

/-- The norm of the derivative of a modulated function. -/
theorem norm_deriv_aux (r t : ℝ) (z w : ℂ) :
    ‖-(2 * Real.pi * Complex.I * (r : ℂ)) * (e t * z) + e t * w‖ ≤
      2 * Real.pi * |r| * ‖z‖ + ‖w‖ := by
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖-(2 * Real.pi * Complex.I * (r : ℂ)) * (e t * z)‖ = 2 * Real.pi * |r| * ‖z‖ := by
    rw [norm_mul, norm_mul, norm_e, one_mul, norm_neg, norm_mul, norm_mul, norm_mul]
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  have h2 : ‖e t * w‖ = ‖w‖ := by rw [norm_mul, norm_e, one_mul]
  rw [h1, h2]

/-- **The modulated packets `e(-ξ ·) φ_P` are adapted to `I`**: there is `A₀` such that for every
multitile `P` (of every index, every profile choice) and every `ξ` with
`|ξ - c(ω_u)| ≤ Λ/(4|I|)`, `ψ = e(-ξ ·) φ_P` has the bounds of `PacketBounds (A₀ (1 + Λ)) I ψ`. -/
theorem exists_packetBounds_modulated :
    ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ (ρ : Idx) (ch : ProfileChoice) (P : Multitile ρ) (ξ Λ : ℝ), 0 ≤ Λ →
      |ξ - P.ωu.center| ≤ Λ / (4 * P.I.length) →
      PacketBounds (A₀ * (1 + Λ)) P.I (fun y => e (-(ξ * y)) * P.wavePacket ch y) := by
  obtain ⟨C₀, hC₀, h0⟩ := Multitile.exists_norm_wavePacket_le 4
  obtain ⟨C₁, hC₁, h1⟩ := Multitile.exists_adaptedBound 1 4
  refine ⟨3 * C₀ + C₁, by positivity, fun ρ ch P ξ Λ hΛ hξ => ?_⟩
  have hLpos : 0 < P.I.length := P.I.length_pos
  have hs : 0 < √P.I.length := Real.sqrt_pos.2 hLpos
  have hs2 : √P.I.length * √P.I.length = P.I.length := Real.mul_self_sqrt hLpos.le
  set cJ := P.ωu.center with hcJ
  set φ := P.wavePacket ch with hφ
  have hφd : Differentiable ℝ φ := P.differentiable_wavePacket ch
  set u : ℝ → ℂ := fun y => e (-(cJ * y)) * φ y with hu
  have hed : ∀ a : ℝ, Differentiable ℝ (fun y : ℝ => e (-(a * y))) := fun a y =>
    (hasDerivAt_e_neg_mul a y).differentiableAt
  have hud : Differentiable ℝ u := (hed cJ).mul hφd
  have hψeq : (fun y => e (-(ξ * y)) * φ y) = fun y => e (-((ξ - cJ) * y)) * u y := by
    funext y
    simp only [hu]
    rw [← mul_assoc, ← e_add]
    congr 2
    ring
  have hψd : Differentiable ℝ (fun y => e (-(ξ * y)) * φ y) := (hed ξ).mul hφd
  -- the pointwise bounds
  refine ⟨hψd, fun y => ?_, fun y => ?_⟩
  · rw [norm_mul, norm_e, one_mul]
    have := h0 ρ ch P y
    have hW : 0 ≤ (√P.I.length)⁻¹ * (1 + |y - P.I.center| / P.I.length) ^ (-4 : ℤ) := by positivity
    calc ‖φ y‖ ≤ C₀ * (√P.I.length)⁻¹ * (1 + |y - P.I.center| / P.I.length) ^ (-(4 : ℕ) : ℤ) :=
          this
      _ ≤ (3 * C₀ + C₁) * (1 + Λ) * (√P.I.length)⁻¹ *
            (1 + |y - P.I.center| / P.I.length) ^ (-4 : ℤ) := by
          have h4 : (-(4 : ℕ) : ℤ) = -4 := by norm_num
          rw [h4]
          have : C₀ ≤ (3 * C₀ + C₁) * (1 + Λ) := by
            linarith [mul_nonneg (by positivity : 0 ≤ 3 * C₀ + C₁) hΛ]
          linarith [mul_le_mul_of_nonneg_right this hW]
  · -- the derivative
    set W : ℝ := (1 + |y - P.I.center| / P.I.length) ^ (-4 : ℤ) with hW
    have hW0 : 0 ≤ W := by positivity
    have hder : deriv (fun y => e (-(ξ * y)) * φ y) y =
        -(2 * Real.pi * Complex.I * ((ξ - cJ : ℝ) : ℂ)) * (e (-((ξ - cJ) * y)) * u y) +
          e (-((ξ - cJ) * y)) * deriv u y := by
      rw [hψeq]
      have h1' := hasDerivAt_e_neg_mul (ξ - cJ) y
      have h2' := (hud y).hasDerivAt
      exact (h1'.mul h2').deriv.trans (by ring)
    rw [hder]
    have hu1 : ‖u y‖ ≤ C₀ * (√P.I.length)⁻¹ * W := by
      simp only [hu]
      rw [norm_mul, norm_e, one_mul]
      have := h0 ρ ch P y
      have h4 : (-(4 : ℕ) : ℤ) = -4 := by norm_num
      rw [h4] at this
      exact this
    have hu2 : ‖deriv u y‖ ≤ C₁ * (P.I.length * √P.I.length)⁻¹ * W := by
      have := h1 ρ ch P y
      rw [iteratedDeriv_one] at this
      have hw : P.I.weight 4 y = P.I.length⁻¹ * W := by
        simp only [Dyadic.weight, hW]
        norm_num
      rw [hw] at this
      refine this.trans (le_of_eq ?_)
      have : √P.I.length * (P.I.length ^ 1)⁻¹ * P.I.length⁻¹ = (P.I.length * √P.I.length)⁻¹ := by
        field_simp
        linarith [hs2]
      rw [← this]; ring
    have hξ' : |(ξ - cJ : ℝ)| ≤ Λ / (4 * P.I.length) := hξ
    calc ‖-(2 * Real.pi * Complex.I * ((ξ - cJ : ℝ) : ℂ)) * (e (-((ξ - cJ) * y)) * u y) +
          e (-((ξ - cJ) * y)) * deriv u y‖
        ≤ 2 * Real.pi * |ξ - cJ| * ‖u y‖ + ‖deriv u y‖ := norm_deriv_aux _ _ _ _
      _ ≤ 2 * Real.pi * (Λ / (4 * P.I.length)) * (C₀ * (√P.I.length)⁻¹ * W) +
            C₁ * (P.I.length * √P.I.length)⁻¹ * W := by
          gcongr
      _ = (Real.pi / 2 * Λ * C₀ + C₁) * ((P.I.length * √P.I.length)⁻¹ * W) := by
          field_simp
          linarith [hs2]
      _ ≤ (3 * C₀ + C₁) * (1 + Λ) * (P.I.length * √P.I.length)⁻¹ * W := by
          have hpos : 0 ≤ (P.I.length * √P.I.length)⁻¹ * W := by positivity
          have : Real.pi / 2 * Λ * C₀ + C₁ ≤ (3 * C₀ + C₁) * (1 + Λ) := by
            have h4 := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (mul_nonneg hΛ hC₀)
            linarith only [h4, mul_nonneg hΛ hC₀, mul_nonneg hΛ hC₁, hC₀, hC₁]
          linarith [mul_le_mul_of_nonneg_right this hpos]

end PrimeCarleson.Proof.Oplus

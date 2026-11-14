module

public import PrimeCarleson.Proof.Paper.P5.BV
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Decay of `ψ̂` and the moments of `λ̂`

Analytic inputs for the error multiplier of the `K_Q`-replacement (Source: main paper `p:red-var`,
L1480–L1483): "the rapid decay of the Fourier transforms of the kernels `ψ_k`".

* `exists_decay_pow`: a Schwartz function `g` has `|g(y)| ≤ C/(1 + |y|)^m` for every `m`;
* `exists_Spart_decay`: `|∑_{k ∈ [a, b)} ψ̂(2^k β)| ≤ C_m ((2^a |β|)⁻¹)^m`, uniformly in `b ≥ a`
  and `β ≠ 0`;
* `Mom ψ m = ∫ |u|^m |λ̂(u)| du < ∞` and `∫ |β|^m |G_k(β)| dβ = 2^{-km} Mom ψ m`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped FourierTransform SchwartzMap ContDiff Real

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper.P5

open PrimeCarleson PrimeCarleson.Proof.Paper PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

variable (ψ : PsiData)

/-- A Schwartz function decays faster than any power. -/
theorem exists_decay_pow (g : 𝓢(ℝ, ℂ)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, ‖g y‖ ≤ C / (1 + |y|) ^ m := by
  refine ⟨2 ^ m * (Finset.Iic ((m, 0) : ℕ × ℕ)).sup
    (fun p => SchwartzMap.seminorm ℝ p.1 p.2) g, by positivity, fun y => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((m, 0) : ℕ × ℕ))
    (k := m) (n := 0) le_rfl le_rfl g y
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  rw [le_div_iff₀ (by positivity), mul_comm]
  simpa [Real.norm_eq_abs] using h

/-- `ψ` as a Schwartz function. -/
def psiS : 𝓢(ℝ, ℂ) := (hasCompactSupport_psic ψ).toSchwartzMap (contDiff_psic ψ)

/-- `λ` as a Schwartz function. -/
def lamS : 𝓢(ℝ, ℂ) := (hasCompactSupport_lamC ψ).toSchwartzMap (contDiff_lamC ψ)

theorem psiHat_eq_schwartz (u : ℝ) : psiHat ψ u = (𝓕 (psiS ψ)) u := by
  rw [SchwartzMap.fourier_coe]
  rfl

theorem lamHat_eq_schwartz (u : ℝ) : lamHat ψ u = (𝓕 (lamS ψ)) u := by
  rw [SchwartzMap.fourier_coe]
  rfl

/-- `|ψ̂(u)| ≤ C_m / (1 + |u|)^m`. -/
theorem exists_psiHat_decay (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, ‖psiHat ψ u‖ ≤ C / (1 + |u|) ^ m := by
  obtain ⟨C, hC0, hC⟩ := exists_decay_pow (𝓕 (psiS ψ)) m
  exact ⟨C, hC0, fun u => by rw [psiHat_eq_schwartz]; exact hC u⟩

/-- **Rapid decay of the partial sums**: for `m ≥ 1` there is `C_m` with
`|∑_{k ∈ [a, b)} ψ̂(2^k β)| ≤ C_m ((2^a |β|)⁻¹)^m` for `β ≠ 0` and all `a ≤ b`. -/
theorem exists_Spart_decay {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℕ) (β : ℝ), β ≠ 0 →
      ‖Spart ψ a b β‖ ≤ C * (((2 : ℝ) ^ a * |β|)⁻¹) ^ m := by
  obtain ⟨C, hC0, hC⟩ := exists_psiHat_decay ψ m
  refine ⟨2 * C, by positivity, fun a b β hβ => ?_⟩
  have hβ0 : 0 < |β| := abs_pos.2 hβ
  set r : ℝ := ((2 : ℝ) ^ a * |β|)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hterm : ∀ i : ℕ, ‖psiHat ψ (2 ^ (a + i) * β)‖ ≤ C * r ^ m * ((1 / 2 : ℝ) ^ m) ^ i := by
    intro i
    refine (hC _).trans ?_
    have habs : |(2 : ℝ) ^ (a + i) * β| = (2 : ℝ) ^ (a + i) * |β| := by
      rw [abs_mul, abs_of_pos (pow_pos two_pos _)]
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (a + i) * |β| := by positivity
    calc C / (1 + |(2 : ℝ) ^ (a + i) * β|) ^ m ≤ C / ((2 : ℝ) ^ (a + i) * |β|) ^ m := by
          rw [habs]
          gcongr
          linarith
      _ = C * r ^ m * ((1 / 2 : ℝ) ^ m) ^ i := by
          have hq : ((1 / 2 : ℝ) ^ m) ^ i = (((2 : ℝ) ^ i)⁻¹) ^ m := by
            rw [← pow_mul, mul_comm, pow_mul, one_div, inv_pow]
          have h3 : (((2 : ℝ) ^ (a + i) * |β|)⁻¹) ^ m = r ^ m * (((2 : ℝ) ^ i)⁻¹) ^ m := by
            rw [← mul_pow, hr]
            congr 1
            rw [pow_add]
            field_simp
          rw [hq, mul_assoc, ← h3, div_eq_mul_inv, inv_pow]
  have hgeo : ∑ i ∈ Finset.range (b - a), ((1 / 2 : ℝ) ^ m) ^ i ≤ 2 := by
    have hq : (1 / 2 : ℝ) ^ m ≤ 1 / 2 := by
      calc (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ 1 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
        _ = 1 / 2 := pow_one _
    have hq0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ m := by positivity
    have hs := (summable_geometric_of_lt_one hq0 (by linarith)).sum_le_tsum (Finset.range (b - a))
      (fun i _ => by positivity)
    rw [tsum_geometric_of_lt_one hq0 (by linarith)] at hs
    refine hs.trans ?_
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  calc ‖Spart ψ a b β‖ ≤ ∑ k ∈ Finset.Ico a b, ‖psiHat ψ (2 ^ k * β)‖ := norm_sum_le _ _
    _ = ∑ i ∈ Finset.range (b - a), ‖psiHat ψ (2 ^ (a + i) * β)‖ :=
        Finset.sum_Ico_eq_sum_range (fun k => ‖psiHat ψ (2 ^ k * β)‖) a b
    _ ≤ ∑ i ∈ Finset.range (b - a), C * r ^ m * ((1 / 2 : ℝ) ^ m) ^ i :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = C * r ^ m * ∑ i ∈ Finset.range (b - a), ((1 / 2 : ℝ) ^ m) ^ i := by rw [Finset.mul_sum]
    _ ≤ C * r ^ m * 2 := mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = 2 * C * r ^ m := by ring

/-! ### The moments of `λ̂` -/

/-- `Mom ψ m = ∫ |u|^m |λ̂(u)| du`. -/
def Mom (m : ℕ) : ℝ := ∫ u, |u| ^ m * ‖lamHat ψ u‖

theorem integrable_mom (m : ℕ) : Integrable fun u : ℝ => |u| ^ m * ‖lamHat ψ u‖ := by
  have := SchwartzMap.integrable_pow_mul volume (𝓕 (lamS ψ)) m
  refine this.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [Real.norm_eq_abs, lamHat_eq_schwartz]

theorem Mom_nonneg (m : ℕ) : 0 ≤ Mom ψ m := integral_nonneg fun _ => by positivity

theorem integrable_mom_Gfun (m k : ℕ) : Integrable fun β : ℝ => |β| ^ m * ‖Gfun ψ k β‖ := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have h := (integrable_mom ψ m).comp_mul_left' (R := (2 : ℝ) ^ k) hp.ne'
  have h2 := h.const_mul (((2 : ℝ) ^ k) ^ (1 - (m : ℤ)))
  refine h2.congr (Filter.Eventually.of_forall fun β => ?_)
  simp only [Gfun, norm_mul, norm_pow, Complex.norm_ofNat, mul_pow, abs_mul,
    abs_of_pos hp]
  rw [zpow_sub₀ hp.ne', zpow_one, zpow_natCast]
  field_simp

/-- `∫ |β|^m |G_k(β)| dβ = 2^{-km} Mom ψ m`. -/
theorem integral_mom_Gfun (m k : ℕ) :
    ∫ β, |β| ^ m * ‖Gfun ψ k β‖ = (((2 : ℝ) ^ k)⁻¹) ^ m * Mom ψ m := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have h := Measure.integral_comp_mul_left (fun u : ℝ => |u| ^ m * ‖lamHat ψ u‖) ((2 : ℝ) ^ k)
  have hfun : ∀ β : ℝ, |β| ^ m * ‖Gfun ψ k β‖ =
      (((2 : ℝ) ^ k)⁻¹) ^ m * ((2 : ℝ) ^ k) *
        ((fun u : ℝ => |u| ^ m * ‖lamHat ψ u‖) ((2 : ℝ) ^ k * β)) := by
    intro β
    have hg : ‖Gfun ψ k β‖ = (2 : ℝ) ^ k * ‖lamHat ψ ((2 : ℝ) ^ k * β)‖ := by
      simp [Gfun]
    have habs : |(2 : ℝ) ^ k * β| = (2 : ℝ) ^ k * |β| := by rw [abs_mul, abs_of_pos hp]
    have hk : (((2 : ℝ) ^ k)⁻¹) ^ m * ((2 : ℝ) ^ k) ^ m = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hp.ne', one_pow]
    change |β| ^ m * ‖Gfun ψ k β‖ = (((2 : ℝ) ^ k)⁻¹) ^ m * ((2 : ℝ) ^ k) *
      (|(2 : ℝ) ^ k * β| ^ m * ‖lamHat ψ ((2 : ℝ) ^ k * β)‖)
    rw [hg, habs, mul_pow]
    linear_combination (-((2 : ℝ) ^ k * |β| ^ m * ‖lamHat ψ ((2 : ℝ) ^ k * β)‖)) * hk
  simp_rw [hfun]
  rw [integral_const_mul, h, abs_inv, abs_of_pos hp, smul_eq_mul, Mom]
  field_simp

end PrimeCarleson.Proof.Paper.P5

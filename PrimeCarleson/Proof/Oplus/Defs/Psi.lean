module

public import PrimeCarleson.Proof.Common.FourierR
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The Schwartz cutoff `ψ` of [O+] (L2295-L2300)

[O+] L2295-L2297: "Now let `ψ` be a Schwartz function with
`ψ̂(ξ) = 1` for `|ξ| ≤ C₁ + C₃` and `ψ̂(ξ) = 0` for `|ξ| ≥ 2C₁`. Define `ψ_ℓ = 2^{-ℓ}ψ(2^{-ℓ}·)`."
Source: [O+] `schwartzchoice`, L2295–L2300 (the paper asserts the existence without
argument). Following `MswTransference/Cutoff.lean`, `ψ` is *chosen* as the inverse Fourier
transform of a `ContDiffBump` (equal to `1` on `[-(C₁ + C₃), C₁ + C₃]`, supported in
`[-2C₁, 2C₁]`), so the existence is explicit, depending only on `C₁, C₃` (`0 < C₃ < C₁`):

* `IsPsiCutoff C₁ C₃ ψ`: the property list of L2295-L2297 (so statements can be proved for every
  `ψ` with it);
* `psi C₁ C₃ h₀ h₁ : 𝓢(ℝ, ℂ)` with `psi_fourier_eq_one`, `psi_fourier_eq_zero`, `integral_psi`
  (`isPsiCutoff_psi`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped FourierTransform SchwartzMap ContDiff

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- The real bump equal to `1` on `[-(C₁ + C₃), C₁ + C₃]` and supported in `[-2C₁, 2C₁]`. -/
def psiBump (C₁ C₃ : ℝ) (h₀ : 0 < C₃) (h₁ : C₃ < C₁) : ContDiffBump (0 : ℝ) :=
  ⟨C₁ + C₃, 2 * C₁, by linarith, by linarith⟩

/-- The complex bump has compact support. -/
theorem psiBump_compactSupport (C₁ C₃ : ℝ) (h₀ : 0 < C₃) (h₁ : C₃ < C₁) :
    HasCompactSupport (fun x : ℝ => ((psiBump C₁ C₃ h₀ h₁ x : ℝ) : ℂ)) :=
  (psiBump C₁ C₃ h₀ h₁).hasCompactSupport.comp_left Complex.ofReal_zero

/-- The complex bump is `C^∞`. -/
theorem psiBump_contDiff (C₁ C₃ : ℝ) (h₀ : 0 < C₃) (h₁ : C₃ < C₁) :
    ContDiff ℝ ∞ (fun x : ℝ => ((psiBump C₁ C₃ h₀ h₁ x : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (psiBump C₁ C₃ h₀ h₁).contDiff

/-- The complex-valued bump as a Schwartz function. -/
def psiBumpSchwartz (C₁ C₃ : ℝ) (h₀ : 0 < C₃) (h₁ : C₃ < C₁) : 𝓢(ℝ, ℂ) :=
  (psiBump_compactSupport C₁ C₃ h₀ h₁).toSchwartzMap (psiBump_contDiff C₁ C₃ h₀ h₁)

/-- The Schwartz function `ψ` of L2295-L2297 of [O+]: the inverse Fourier transform of the bump. -/
def psi (C₁ C₃ : ℝ) (h₀ : 0 < C₃) (h₁ : C₃ < C₁) : 𝓢(ℝ, ℂ) := 𝓕⁻ (psiBumpSchwartz C₁ C₃ h₀ h₁)

/-- `ψ̂` is the bump. -/
theorem fourier_psi (C₁ C₃ : ℝ) (h₀ : 0 < C₃) (h₁ : C₃ < C₁) :
    𝓕 (psi C₁ C₃ h₀ h₁) = psiBumpSchwartz C₁ C₃ h₀ h₁ :=
  FourierInvPair.fourier_fourierInv_eq _

/-- `ψ̂(ξ) = 1` for `|ξ| ≤ C₁ + C₃`. -/
theorem psi_fourier_eq_one (C₁ C₃ : ℝ) (h₀ : 0 < C₃) (h₁ : C₃ < C₁) {ξ : ℝ}
    (hξ : |ξ| ≤ C₁ + C₃) : 𝓕 (psi C₁ C₃ h₀ h₁) ξ = 1 := by
  rw [fourier_psi]
  change ((psiBump C₁ C₃ h₀ h₁ ξ : ℝ) : ℂ) = 1
  rw [(psiBump C₁ C₃ h₀ h₁).one_of_mem_closedBall]
  · simp
  · simpa [psiBump, Metric.mem_closedBall, Real.dist_eq] using hξ

/-- `ψ̂(ξ) = 0` for `|ξ| ≥ 2C₁`. -/
theorem psi_fourier_eq_zero (C₁ C₃ : ℝ) (h₀ : 0 < C₃) (h₁ : C₃ < C₁) {ξ : ℝ}
    (hξ : 2 * C₁ ≤ |ξ|) : 𝓕 (psi C₁ C₃ h₀ h₁) ξ = 0 := by
  rw [fourier_psi]
  change ((psiBump C₁ C₃ h₀ h₁ ξ : ℝ) : ℂ) = 0
  rw [(psiBump C₁ C₃ h₀ h₁).zero_of_le_dist]
  · simp
  · simpa [psiBump, Real.dist_eq] using hξ

/-- `∫ ψ = ψ̂(0) = 1`. -/
theorem integral_psi (C₁ C₃ : ℝ) (h₀ : 0 < C₃) (h₁ : C₃ < C₁) :
    ∫ x, psi C₁ C₃ h₀ h₁ x = 1 := by
  have h := psi_fourier_eq_one C₁ C₃ h₀ h₁ (ξ := 0) (by simp; linarith)
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq] at h
  simpa using h

/-- The property list of [O+] L2295-L2297: `ψ̂(ξ) = 1` for `|ξ| ≤ C₁ + C₃` and `ψ̂(ξ) = 0` for
`|ξ| ≥ 2C₁`. A statement may be proved for every `ψ` with `IsPsiCutoff C₁ C₃ ψ`; the explicit
`psi` is one such function. -/
structure IsPsiCutoff (C₁ C₃ : ℝ) (ψ : 𝓢(ℝ, ℂ)) : Prop where
  /-- `ψ̂ = 1` on `[-(C₁ + C₃), C₁ + C₃]`. -/
  fourier_eq_one : ∀ ξ : ℝ, |ξ| ≤ C₁ + C₃ → 𝓕 ψ ξ = 1
  /-- `ψ̂ = 0` outside `(-2C₁, 2C₁)`. -/
  fourier_eq_zero : ∀ ξ : ℝ, 2 * C₁ ≤ |ξ| → 𝓕 ψ ξ = 0

/-- The explicit `ψ` satisfies the property list of [O+] L2295-L2297. -/
theorem isPsiCutoff_psi (C₁ C₃ : ℝ) (h₀ : 0 < C₃) (h₁ : C₃ < C₁) :
    IsPsiCutoff C₁ C₃ (psi C₁ C₃ h₀ h₁) :=
  ⟨fun _ hξ => psi_fourier_eq_one C₁ C₃ h₀ h₁ hξ, fun _ hξ => psi_fourier_eq_zero C₁ C₃ h₀ h₁ hξ⟩

end PrimeCarleson.Proof.Oplus

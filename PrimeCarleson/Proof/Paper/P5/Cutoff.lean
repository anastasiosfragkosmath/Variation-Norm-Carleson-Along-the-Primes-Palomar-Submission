module

public import PrimeCarleson.Proof.MswTransference.Cutoff
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The cutoff `φ` of the kernel `K_Q`

Source: main paper `e:KQ`, L1193–L1203 (the choice of `φ` at L1199–L1201). The paper fixes "a
Schwartz function `φ` whose Fourier transform is supported in a sufficiently small fixed
neighborhood of the origin". The error estimate at L1480–L1483 also needs `φ̂ = 1` near `0`, which
this choice omits. Here `φ` is chosen to be Schwartz with `φ̂` smooth, supported in `[-δ, δ]` and
equal to `1` on `[-δ/2, δ/2]`, for a fixed `0 < δ ≤ δ₀`.

The cutoff is data, not a chosen function:

* `PhiData δ` is a Schwartz function `φ : 𝓢(ℝ, ℂ)` with `φ̂ = 1` on `[-δ/2, δ/2]` and `φ̂ = 0`
  outside `[-δ, δ]` (the Fourier transform of a Schwartz function is Schwartz, hence smooth);
* `PhiData.nonempty`: for every `δ > 0` there is such a `φ` (the inverse Fourier transform of a
  `ContDiffBump`, as in `MswTransference/Cutoff.lean`);
* consequences: `φ̂(0) = 1` (`PhiData.hat_zero`) and `∫ φ = φ̂(0) = 1` (`PhiData.integral_eq_one`).

The radius `δ₀` is fixed by the consumers in `P5/Support.lean`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform ContDiff

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

/-- The data of the cutoff `φ` of `K_Q` (L1199–L1201): a Schwartz function whose Fourier transform
is `1` on `[-δ/2, δ/2]` and `0` outside `[-δ, δ]`. -/
structure PhiData (δ : ℝ) where
  /-- The Schwartz function `φ`. -/
  toSchwartz : 𝓢(ℝ, ℂ)
  /-- `φ̂ = 1` on `[-δ/2, δ/2]`. -/
  fourier_eq_one : ∀ ξ : ℝ, |ξ| ≤ δ / 2 → 𝓕 toSchwartz ξ = 1
  /-- `φ̂ = 0` outside `[-δ, δ]`. -/
  fourier_eq_zero : ∀ ξ : ℝ, δ < |ξ| → 𝓕 toSchwartz ξ = 0

namespace PhiData

variable {δ : ℝ} (φ : PhiData δ)

/-- The Fourier transform `φ̂` as a function `ℝ → ℂ`. -/
def hat : ℝ → ℂ := fun ξ => 𝓕 φ.toSchwartz ξ

/-- `φ̂ = 1` on `[-δ/2, δ/2]`. -/
theorem hat_eq_one {ξ : ℝ} (h : |ξ| ≤ δ / 2) : φ.hat ξ = 1 := φ.fourier_eq_one ξ h

/-- `φ̂ = 0` outside `[-δ, δ]`. -/
theorem hat_eq_zero {ξ : ℝ} (h : δ < |ξ|) : φ.hat ξ = 0 := φ.fourier_eq_zero ξ h

/-- `φ̂(0) = 1`, i.e. `∫ φ = 1` (the normalization the error estimate at L1480-L1483 needs). -/
theorem hat_zero (hδ : 0 < δ) : φ.hat 0 = 1 :=
  φ.hat_eq_one (by rw [abs_zero]; linarith)

/-- `∫ φ = 1`. -/
theorem integral_eq_one (hδ : 0 < δ) : ∫ x, φ.toSchwartz x = 1 := by
  have h := φ.hat_zero hδ
  simp only [hat] at h
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq] at h
  simpa using h

/-- Every `δ > 0` has a cutoff (Source: main paper `e:KQ`, L1199–L1201). -/
theorem nonempty (hδ : 0 < δ) : Nonempty (PhiData δ) := by
  let bump : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, by positivity, by linarith⟩
  have hc : HasCompactSupport (fun x : ℝ => ((bump x : ℝ) : ℂ)) :=
    HasCompactSupport.comp_left (g := Complex.ofReal) (f := ⇑bump) bump.hasCompactSupport
      Complex.ofReal_zero
  have hd : ContDiff ℝ ∞ (fun x : ℝ => ((bump x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp bump.contDiff
  let S : 𝓢(ℝ, ℂ) := hc.toSchwartzMap hd
  have hS : ∀ x, S x = ((bump x : ℝ) : ℂ) := fun _ => rfl
  refine ⟨⟨𝓕⁻ S, fun ξ hξ => ?_, fun ξ hξ => ?_⟩⟩
  · rw [FourierInvPair.fourier_fourierInv_eq, hS, bump.one_of_mem_closedBall]
    · simp
    · simpa [Metric.mem_closedBall, Real.dist_eq] using hξ
  · rw [FourierInvPair.fourier_fourierInv_eq, hS, bump.zero_of_le_dist]
    · simp
    · simpa [Real.dist_eq] using hξ.le

end PhiData

end PrimeCarleson.Proof.Paper

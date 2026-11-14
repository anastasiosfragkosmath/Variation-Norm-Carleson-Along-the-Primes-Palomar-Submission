module

public import PrimeCarleson.Proof.Paper.P7.Hilbert
public import PrimeCarleson.Proof.Paper.P7.DiscSup

/-!
# `p:disc`: the discrete Carleson theorem in variation norm

`sources/Variational_Carleson.tex` L2939-L2944 (`p:disc`). For `r > 2`, `r' < p < ∞` and finitely
supported `f`,
`‖V^r(∑_{n ≠ 0} f(x - n) e(λ n)/n : λ ∈ 𝕋)‖_{ℓ^p} ≤ C_{p,r} ‖f‖_{ℓ^p}`
(`pdisc_of_oplus`, with the constant `C_{p,r}`). It is `c:disc` for the multiplier
`K̂_H` of the Hilbert kernel (`Hilbert.lean`: bounded variation `≤ 4π`, supported in `(-1/2, 1/2)`,
`∫ K̂_H e(n ·) = 1/n` for `n ≠ 0`, `0` for `n = 0`), with `Q = 1`.

The proof differs from the paper's: the paper reduces to the truncated kernels `∑_{k ≤ J} ψ_k`, a
Fejér decomposition of `f`, modulation and a splitting of the `λ`-range, and applies MSW
transference to the multipliers `M_v(β, λ)` with the cutoff `(1 - |β|)_+ η(2^{100} β)`. Here the
multiplier of `1/n` is the sawtooth `K̂_H`, of bounded variation, so `l:varcar` applies to it
directly on the fundamental domain and the transference is applied once, to the half-line
projections (`halfLine_variation`); no truncation in `J`, no Fejér decomposition and no splitting of
the range of `λ` is needed, and the single-`λ` endpoint terms are bounded in `DiscSup.lean`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.MswTransference
  PrimeCarleson.Proof.Goal0 Real

/-- The modulated sum of the discrete Hilbert kernel `∑_{n ≠ 0} f(x - n) e(λ n)/n` is the
modulated sum of the kernel `K(n) = ∫ K̂_H(ξ) e(nξ) dξ`. -/
theorem dilSum_hilbertMult (f : ℤ →₀ ℂ) (x : ℤ) (lam : ℝ) :
    dilSum hilbertMult 1 f x lam =
      ∑' n : ℤ, if n = 0 then 0 else f (x - n) * e (lam * (n : ℝ)) / (n : ℂ) := by
  unfold dilSum
  refine tsum_congr fun n => ?_
  rw [integral_hilbertMult_mul_e]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ↓reduceIte, one_mul]
    ring

/-- **`p:disc`** (conditional on `hO : OplusVariationBound`; L2939-L2944): for `r > 2` and
`r' < p < ∞` there is `C ≥ 0` such that for every finitely supported `f` and every `S ⊆ [0, 1)`
(in particular `S = 𝕋`, or any finite `T`),
`‖V^r(∑_{n ≠ 0} f(x - n) e(λ n)/n : λ ∈ S)‖_{ℓ^p(ℤ)} ≤ C ‖f‖_{ℓ^p}`.

Source: main paper `p:disc`, L2939–L2944. -/
theorem pdisc_of_oplus (hO : OplusVariationBound) {r p : ℝ} (hr : 2 < r) (hp : r / (r - 1) < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℤ →₀ ℂ) (S : Set ℝ), S ⊆ Set.Ico 0 1 →
      eLpNorm (fun x : ℤ => rVariationOn r S (fun lam =>
          ∑' n : ℤ, if n = 0 then 0 else f (x - n) * e (lam * (n : ℝ)) / (n : ℂ)))
          (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨C, hC0, hC⟩ := cdisc_one hO hr hp
  have hπ := Real.pi_pos
  refine ⟨C * (4 * π), by positivity, fun f S hS => ?_⟩
  have h := hC hilbertMult (4 * π) (by positivity) measurable_hilbertMult
    (fun ξ h => hilbertMult_support h) eVariationOn_hilbertMult_le f S hS
  simp_rw [dilSum_hilbertMult] at h
  exact h

end PrimeCarleson.Proof.Paper

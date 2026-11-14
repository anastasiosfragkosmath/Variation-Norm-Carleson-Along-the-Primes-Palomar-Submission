module

public import PrimeCarleson.Proof.Lepingle.Prob.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
# Martingale constructions

Bridges between the definitions and properties of Zorin-Kranich's notes (Source: Zorin-Kranich's
notes, 00-background.tex L3–L126; properties of conditional expectation) and Mathlib's
`MeasureTheory.Martingale`, and the constructions of martingales used by the proofs of Davis'
inequality and of the BDG inequality:

* `condExp_incr_eq_zero`, `integral_mul_incr_eq_zero`: the martingale differences are orthogonal to
  the past (`E(g df_n) = 0` for `g` `ℱ_{n-1}`-measurable, Zorin-Kranich's notes, (1.1));
* `martingale_partial_sum`: partial sums of martingale differences form a martingale;
* `martingale_indicator_incr`: for `C k ∈ ℱ k`, `∑_{k<n} 1_{C k} df_{k+1}` is a martingale (stopped
  martingales, `1_B (f - f^{(t)})`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Finset
open scoped ENNReal NNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Lepingle

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℕ → Ω → 𝕜}

theorem incr_eq_sub (f : ℕ → Ω → 𝕜) (k : ℕ) : incr f k = f (k + 1) - f k := rfl

/-- The increments of a martingale have conditional expectation zero: `E_k(f_{k+1} - f_k) = 0`. -/
theorem condExp_incr_eq_zero [IsFiniteMeasure μ] (hf : Martingale f ℱ μ) (k : ℕ) :
    μ[incr f k | ℱ k] =ᵐ[μ] 0 := by
  rw [incr_eq_sub]
  have h3 : μ[f k | ℱ k] = f k :=
    condExp_of_stronglyMeasurable (ℱ.le k) (hf.stronglyMeasurable k) (hf.integrable k)
  filter_upwards [condExp_sub (hf.integrable (k + 1)) (hf.integrable k) (ℱ k),
    hf.condExp_ae_eq (Nat.le_succ k)] with ω h1 h2
  simp only [Pi.sub_apply, Pi.zero_apply] at h1 ⊢
  rw [h1, h2, h3]
  simp

/-- **Orthogonality of the increments to the past** (Zorin-Kranich's notes, (1.1)):
`E(g df_{k+1}) = 0` for `g` `ℱ k`-measurable with `g df_{k+1}` integrable. -/
theorem integral_mul_incr_eq_zero [IsFiniteMeasure μ] (hf : Martingale f ℱ μ) (k : ℕ)
    {g : Ω → 𝕜} (hg : StronglyMeasurable[ℱ k] g)
    (hgd : Integrable (fun ω => g ω * incr f k ω) μ) :
    ∫ ω, g ω * incr f k ω ∂μ = 0 := by
  have hinc : Integrable (incr f k) μ := (hf.integrable (k + 1)).sub (hf.integrable k)
  have h1 := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ 𝕜) hg
    (by simpa using hgd) hinc
  have h2 := condExp_incr_eq_zero hf k
  rw [← integral_condExp (ℱ.le k)]
  have : μ[fun ω => g ω * incr f k ω | ℱ k] =ᵐ[μ] 0 := by
    filter_upwards [h1, h2] with ω h1 h2
    simp only [ContinuousLinearMap.mul_apply'] at h1
    rw [h1, h2]
    simp
  rw [integral_congr_ae this]
  simp

/-- Partial sums of martingale differences form a martingale: if `u k` is `ℱ (k+1)`-measurable,
integrable and `E_k u k = 0`, then `n ↦ ∑_{k<n} u k` is a martingale. -/
theorem martingale_partial_sum [IsFiniteMeasure μ] {u : ℕ → Ω → 𝕜}
    (hm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (u k)) (hi : ∀ k, Integrable (u k) μ)
    (h0 : ∀ k, μ[u k | ℱ k] =ᵐ[μ] 0) :
    Martingale (fun n ω => ∑ k ∈ range n, u k ω) ℱ μ := by
  refine martingale_of_condExp_sub_eq_zero_nat ?_ ?_ ?_
  · intro n
    exact Finset.stronglyMeasurable_fun_sum _ fun k hk =>
      (hm k).mono (ℱ.mono (Nat.succ_le_of_lt (Finset.mem_range.1 hk)))
  · intro n
    exact integrable_finsetSum _ fun k _ => hi k
  · intro n
    have : ((fun ω => ∑ k ∈ range (n + 1), u k ω) - fun ω => ∑ k ∈ range n, u k ω) = u n := by
      funext ω
      simp [Finset.sum_range_succ]
    rw [this]
    exact h0 n

/-- If `f` is a martingale and `C k ∈ ℱ k`, then `n ↦ ∑_{k<n} 1_{C k} (f_{k+1} - f_k)` is a
martingale (the martingale transform by the predictable `{0,1}`-valued process `1_{C k}`). -/
theorem martingale_indicator_incr [IsFiniteMeasure μ] (hf : Martingale f ℱ μ) {C : ℕ → Set Ω}
    (hC : ∀ k, MeasurableSet[ℱ k] (C k)) :
    Martingale (fun n ω => ∑ k ∈ range n, (C k).indicator (incr f k) ω) ℱ μ := by
  have hinc : ∀ k, Integrable (incr f k) μ := fun k =>
    (hf.integrable (k + 1)).sub (hf.integrable k)
  refine martingale_partial_sum ?_ ?_ ?_
  · intro k
    have : StronglyMeasurable[ℱ (k + 1)] (incr f k) :=
      (hf.stronglyMeasurable (k + 1)).sub ((hf.stronglyMeasurable k).mono (ℱ.mono k.le_succ))
    exact this.indicator (ℱ.mono k.le_succ _ (hC k))
  · intro k
    exact (hinc k).indicator (ℱ.le k _ (hC k))
  · intro k
    filter_upwards [condExp_indicator (hinc k) (hC k), condExp_incr_eq_zero hf k] with ω h1 h2
    rw [h1]
    simp [h2]

end RCLike

end PrimeCarleson.Proof.Lepingle

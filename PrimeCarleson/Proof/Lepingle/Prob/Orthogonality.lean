module

public import PrimeCarleson.Proof.Lepingle.Prob.Martingale
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Orthogonality of martingale increments: `‖f_n‖_2 = ‖S f_n‖_2`

Source: Zorin-Kranich's notes `eq:increment-orthogonal-to-past` (01-BDG.tex, L118–L142): display
(1.1) and the identity `‖f_n‖_2 = ‖Sf_n‖_2` for `f_0 = 0` (01-BDG.tex L118-L142).

* `integral_mul_incr_eq_zero` (in `Martingale.lean`): `E(g df_{k+1}) = 0` for `g` `ℱ k`-measurable;
* `integral_norm_sq_sub_zero_eq_sum`: for a martingale with `f_n ∈ L²`,
  `E ‖f_n - f_0‖² = ∑_{k<n} E ‖f_{k+1} - f_k‖²`;
* `lintegral_enorm_sq_sub_zero_eq_sum`: the same in `ℝ≥0∞`;
* `lintegral_sqUpTo_sq_eq`: `∫⁻ (S f_n)² = ∫⁻ ‖f_n - f_0‖²` (`S f_n = sqUpTo f n`), that is
  `‖f_n‖_2 = ‖S f_n‖_2` for `f_0 = 0`.

The hypothesis `f_n ∈ L²` (implicit in the source) is exactly what is needed; it implies
`f_k ∈ L²` for `k ≤ n` (`memLp_two_of_martingale`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Finset
open scoped ENNReal NNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Lepingle

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
  {𝕜 : Type*} [RCLike 𝕜] {f : ℕ → Ω → 𝕜}

/-- If `f_n ∈ L²` for a martingale, then `f_k ∈ L²` for `k ≤ n` (conditional expectation is an
`L²`-contraction). -/
theorem memLp_two_of_martingale [IsFiniteMeasure μ] (hf : Martingale f ℱ μ) {n : ℕ}
    (h : MemLp (f n) 2 μ) {k : ℕ} (hk : k ≤ n) : MemLp (f k) 2 μ :=
  MemLp.ae_eq (hf.condExp_ae_eq hk) (MemLp.condExp (by norm_num) h)

theorem memLp_conj {g : Ω → 𝕜} (hg : MemLp g 2 μ) : MemLp (fun ω => conj (g ω)) 2 μ :=
  hg.of_le (RCLike.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => by simp)

/-- For `g ∈ L²`, `∫⁻ ‖g‖ₑ² = ofReal (∫ ‖g‖²)`. -/
theorem lintegral_enorm_sq_eq_ofReal {g : Ω → 𝕜} (hg : MemLp g 2 μ) :
    ∫⁻ ω, ‖g ω‖ₑ ^ (2 : ℝ) ∂μ = ENNReal.ofReal (∫ ω, ‖g ω‖ ^ 2 ∂μ) := by
  have hint : Integrable (fun ω => ‖g ω‖ ^ 2) μ := by
    simpa using hg.integrable_norm_pow (p := 2) two_ne_zero
  rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ω => by positivity)]
  refine lintegral_congr fun ω => ?_
  rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- **Orthogonality of martingale increments in `L²`** (Zorin-Kranich's notes, (1.1)):
for a martingale with `f_n ∈ L²`,
`E ‖f_n - f_0‖² = ∑_{k<n} E ‖f_{k+1} - f_k‖²`. -/
theorem integral_norm_sq_sub_zero_eq_sum [IsFiniteMeasure μ] (hf : Martingale f ℱ μ) {n : ℕ}
    (h : MemLp (f n) 2 μ) :
    ∫ ω, ‖f n ω - f 0 ω‖ ^ 2 ∂μ = ∑ k ∈ range n, ∫ ω, ‖incr f k ω‖ ^ 2 ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hL : ∀ k ≤ n + 1, MemLp (f k) 2 μ := fun k hk => memLp_two_of_martingale hf h hk
    have hfn := hL n n.le_succ
    have hIH := ih hfn
    have ha : MemLp (fun ω => f n ω - f 0 ω) 2 μ := (hfn).sub (hL 0 (Nat.zero_le _))
    have hd : MemLp (incr f n) 2 μ := (hL (n + 1) le_rfl).sub hfn
    have hasm : StronglyMeasurable[ℱ n] (fun ω => conj (f n ω - f 0 ω)) := by
      have : StronglyMeasurable[ℱ n] (fun ω => f n ω - f 0 ω) :=
        (hf.stronglyMeasurable n).sub ((hf.stronglyMeasurable 0).mono (ℱ.mono (Nat.zero_le n)))
      exact RCLike.continuous_conj.comp_stronglyMeasurable this
    have hprod : Integrable (fun ω => conj (f n ω - f 0 ω) * incr f n ω) μ :=
      (memLp_conj ha).integrable_mul hd
    have hcross : ∫ ω, RCLike.re (incr f n ω * conj (f n ω - f 0 ω)) ∂μ = 0 := by
      have h0 := integral_mul_incr_eq_zero hf n hasm hprod
      have h1 : Integrable (fun ω => incr f n ω * conj (f n ω - f 0 ω)) μ := by
        simpa [mul_comm] using hprod
      rw [integral_re h1]
      have : (fun ω => incr f n ω * conj (f n ω - f 0 ω)) =
          fun ω => conj (f n ω - f 0 ω) * incr f n ω := funext fun ω => mul_comm _ _
      rw [this, h0]
      simp
    have hint1 : Integrable (fun ω => ‖f n ω - f 0 ω‖ ^ 2) μ := by
      simpa using ha.integrable_norm_pow (p := 2) two_ne_zero
    have hint2 : Integrable (fun ω => ‖incr f n ω‖ ^ 2) μ := by
      simpa using hd.integrable_norm_pow (p := 2) two_ne_zero
    have hint3 : Integrable (fun ω => RCLike.re (incr f n ω * conj (f n ω - f 0 ω))) μ := by
      have h1 : Integrable (fun ω => incr f n ω * conj (f n ω - f 0 ω)) μ := by
        simpa [mul_comm] using hprod
      exact h1.re
    have hpt : ∀ ω, ‖f (n + 1) ω - f 0 ω‖ ^ 2 = ‖incr f n ω‖ ^ 2 + ‖f n ω - f 0 ω‖ ^ 2 +
        2 * RCLike.re (incr f n ω * conj (f n ω - f 0 ω)) := by
      intro ω
      have : f (n + 1) ω - f 0 ω = incr f n ω + (f n ω - f 0 ω) := by
        simp [incr_apply]
      rw [this, ← RCLike.normSq_eq_def', RCLike.normSq_add, RCLike.normSq_eq_def',
        RCLike.normSq_eq_def']
    have hint12 : Integrable (fun ω => ‖incr f n ω‖ ^ 2 + ‖f n ω - f 0 ω‖ ^ 2) μ :=
      hint2.add hint1
    simp_rw [hpt]
    rw [integral_add hint12 (hint3.const_mul 2), integral_add hint2 hint1,
      integral_const_mul, hcross, Finset.sum_range_succ, ← hIH]
    ring

/-- `ℝ≥0∞` form of the orthogonality of increments:
`∫⁻ ‖f_n - f_0‖² = ∑_{k<n} ∫⁻ ‖f_{k+1} - f_k‖²` for a martingale with `f_n ∈ L²`. -/
theorem lintegral_enorm_sq_sub_zero_eq_sum [IsFiniteMeasure μ] (hf : Martingale f ℱ μ) {n : ℕ}
    (h : MemLp (f n) 2 μ) :
    ∫⁻ ω, ‖f n ω - f 0 ω‖ₑ ^ (2 : ℝ) ∂μ = ∑ k ∈ range n, ∫⁻ ω, ‖incr f k ω‖ₑ ^ (2 : ℝ) ∂μ := by
  have hL : ∀ k ≤ n, MemLp (f k) 2 μ := fun k hk => memLp_two_of_martingale hf h hk
  have hsub : MemLp (fun ω => f n ω - f 0 ω) 2 μ := (h).sub (hL 0 (Nat.zero_le _))
  rw [lintegral_enorm_sq_eq_ofReal hsub, integral_norm_sq_sub_zero_eq_sum hf h]
  rw [ENNReal.ofReal_sum_of_nonneg fun k _ => integral_nonneg fun ω => by positivity]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k + 1 ≤ n := Finset.mem_range.1 hk
  have hinc : MemLp (incr f k) 2 μ := (hL (k + 1) hk').sub (hL k (k.le_succ.trans hk'))
  rw [lintegral_enorm_sq_eq_ofReal hinc]

/-- The square function identity: `∫⁻ (S f_n)² = ∫⁻ ‖f_n - f_0‖²` for a martingale with
`f_n ∈ L²` (`S f_n = sqUpTo f n`). -/
theorem lintegral_sqUpTo_sq_eq [IsFiniteMeasure μ] (hf : Martingale f ℱ μ) {n : ℕ}
    (h : MemLp (f n) 2 μ) :
    ∫⁻ ω, sqUpTo f n ω ^ (2 : ℝ) ∂μ = ∫⁻ ω, ‖f n ω - f 0 ω‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [lintegral_enorm_sq_sub_zero_eq_sum hf h]
  have hm : ∀ k, Measurable (incr f k) := fun k =>
    measurable_incr (fun j => ((hf.stronglyMeasurable j).measurable.mono (ℱ.le j) le_rfl)) k
  have : ∀ ω, sqUpTo f n ω ^ (2 : ℝ) = ∑ k ∈ range n, ‖incr f k ω‖ₑ ^ (2 : ℝ) := by
    intro ω
    unfold sqUpTo
    rw [← ENNReal.rpow_mul]
    norm_num
  simp_rw [this]
  rw [lintegral_finsetSum _ fun k _ => (hm k).enorm.pow_const _]

end PrimeCarleson.Proof.Lepingle

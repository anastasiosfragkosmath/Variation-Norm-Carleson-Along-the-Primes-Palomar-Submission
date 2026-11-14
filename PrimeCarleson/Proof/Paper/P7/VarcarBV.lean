module

public import PrimeCarleson.Proof.Paper.P7.GridStep

/-!
# `l:varcar` for multipliers whose distribution function has bounded variation

Source: main paper `l:varcar`, L1784–L1805 (the statement L1784–L1790, the representation
L1792–L1795, the duality L1796–L1804).

**Statement.** Let `g ∈ L¹(ℝ)` (for `g(ξ) = f̂(ξ) e(xξ)` this is the pointwise-in-`x` reading of the
paper) and let `h` be the distribution function `m` of a finite measure `dm`, given as a function
of bounded variation vanishing off a compact interval (`‖dm‖_TV = eVariationOn h univ`). Then
for every set `S ⊆ ℝ` of parameters `λ`, every `1 ≤ r`,

`V^r((f̂(ξ) h(ξ - λ))^∨(x) : λ ∈ S) ≤ ‖dm‖_TV · V^r((f̂(ξ) 1_{(-∞,0]}(ξ - λ))^∨(x) : λ)`

(`varcar_bv`), with constant `1` as the proof of the paper gives.

**Proof** (a finite-dimensional version of the argument of the paper). For a *step* distribution
function `h = ∑ᵢ cᵢ 1_{[xᵢ, ∞)}` (`dm = ∑ᵢ cᵢ δ_{xᵢ}`) the multiplier output is
`∑ᵢ cᵢ (∫ g - Φ_g(xᵢ + λ))` (`mulInt_halfLineSum`, the finite case of the FTC representation), so
the triangle inequality for the `r`-variation gives the bound `∑ᵢ |cᵢ| V^r(Φ_g)`. A general `h` of
bounded variation is the pointwise limit, at its continuity points (all but countably many), of the
grid step functions `gridStep` whose total jump `∑ᵢ |cᵢ|` is at most the variation of `h`; the
outputs converge by dominated convergence, and the bound passes to the limit chain by chain.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.MswTransference

/-- A function vanishing off a compact interval and of variation `≤ B` is bounded by `B`. -/
theorem norm_le_of_eVariationOn {h : ℝ → ℂ} {u w : ℝ} (hsupp : ∀ s, s ∉ Set.Icc u w → h s = 0)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : eVariationOn h Set.univ ≤ ENNReal.ofReal B) (s : ℝ) :
    ‖h s‖ ≤ B := by
  have h0 : h (u - 1) = 0 := hsupp _ fun hmem => by
    have := hmem.1
    linarith
  have h1 := eVariationOn.edist_le h (Set.mem_univ s) (Set.mem_univ (u - 1))
  rw [h0, edist_zero_right] at h1
  have h3 : ENNReal.ofReal ‖h s‖ ≤ ENNReal.ofReal B := by
    rw [ofReal_norm]
    exact h1.trans hB
  exact (ENNReal.ofReal_le_ofReal_iff hB0).1 h3

/-- The grid step function is measurable. -/
theorem measurable_gridStep (h : ℝ → ℂ) (u δ : ℝ) (K : ℕ) : Measurable (gridStep h u δ K) := by
  unfold gridStep halfLineSum
  exact Finset.measurable_sum _ fun k _ =>
    measurable_const.mul (measurable_const.indicator measurableSet_Ici)

/-- The total jump of the grid step function is at most the variation of `h`. -/
theorem sum_enorm_jumps_le (h : ℝ → ℂ) (u : ℝ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∑ k ∈ Finset.range n, ‖h (u + k * δ) - h (u + ((k : ℝ) - 1) * δ)‖ₑ ≤
      eVariationOn h Set.univ := by
  have hu : Monotone fun k : ℕ => u + ((k : ℝ) - 1) * δ := by
    intro i j hij
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    have := mul_le_mul_of_nonneg_right (sub_le_sub_right this 1) hδ.le
    simp only
    linarith
  have h1 := eVariationOn.sum_le (f := h) (n := n) hu fun _ => Set.mem_univ _
  refine le_trans (le_of_eq ?_) h1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [edist_eq_enorm_sub]
  congr 3
  push_cast
  ring_nf

/-- **`l:varcar`** (Source: main paper `l:varcar`, L1784–L1805): the variation over `λ ∈ S` of the
multiplier
outputs
`(f̂(ξ) h(ξ - λ))^∨(x) = ∫ h(ξ - λ) g(ξ) dξ`, `g = f̂ e(x ·) ∈ L¹`, is at most `‖dm‖_TV` times the
variation of the half-line projections `Φ_g(λ) = ∫_{ξ ≤ λ} g`; here `h` is the distribution
function of `dm`, of total variation `eVariationOn h univ ≤ B`, vanishing off `[u, w]`.
Constant `1`; no condition on `r` beyond `1 ≤ r`.

Source: main paper `l:varcar`, L1784–L1790. -/
theorem varcar_bv {r : ℝ} (hr : 1 ≤ r) {g : ℝ → ℂ} (hg : Integrable g) {h : ℝ → ℂ} {u w : ℝ}
    (hsupp : ∀ s, s ∉ Set.Icc u w → h s = 0) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : eVariationOn h Set.univ ≤ ENNReal.ofReal B) (S : Set ℝ) :
    rVariationOn r S (mulInt h g) ≤ ENNReal.ofReal B * rVariationOn r Set.univ (partialInt g) := by
  have hr0 : 0 < r := by linarith
  -- enlarge the support interval so that `u ≤ w'`
  obtain ⟨w', hw'u, hsupp'⟩ : ∃ w', u ≤ w' ∧ ∀ s, s ∉ Set.Icc u w' → h s = 0 :=
    ⟨max w u, le_max_right _ _, fun s hs => hsupp s fun hmem =>
      hs ⟨hmem.1, hmem.2.trans (le_max_left _ _)⟩⟩
  have hnorm : ∀ s, ‖h s‖ ≤ B := norm_le_of_eVariationOn hsupp' hB0 hB
  set V := rVariationOn r Set.univ (partialInt g) with hV
  set G := ∫ ξ, g ξ with hG
  -- grid parameters
  set δ : ℕ → ℝ := fun M => (w' - u + 1) / ((M : ℝ) + 1) with hδdef
  have hδpos : ∀ M, 0 < δ M := fun M => by
    have : 0 < w' - u + 1 := by linarith
    positivity
  have hK : ∀ M : ℕ, w' < u + ((M + 1 : ℕ) : ℝ) * δ M := fun M => by
    have h1 : ((M + 1 : ℕ) : ℝ) * δ M = w' - u + 1 := by
      simp only [hδdef]
      push_cast
      field_simp
    rw [h1]
    linarith
  -- the step functions give the bound with the total jump
  have hbd : ∀ M : ℕ, rVariationOn r S (mulInt (gridStep h u (δ M) (M + 1)) g) ≤
      ENNReal.ofReal B * V := by
    intro M
    set c : ℕ → ℂ := fun k => h (u + k * δ M) - h (u + ((k : ℝ) - 1) * δ M) with hc
    have hfun : mulInt (gridStep h u (δ M) (M + 1)) g =
        ∑ k ∈ Finset.range (M + 1 + 1),
          c k • (fun lam => G - partialInt g (u + k * δ M + lam)) := by
      funext lam
      rw [gridStep, mulInt_halfLineSum _ _ _ hg lam, Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul, hc, hG]
    rw [hfun]
    refine (rVariationOn_sum_le _ hr S _).trans ?_
    calc ∑ k ∈ Finset.range (M + 1 + 1),
          rVariationOn r S (c k • (fun lam => G - partialInt g (u + k * δ M + lam)))
        = ∑ k ∈ Finset.range (M + 1 + 1),
          ‖c k‖ₑ * rVariationOn r S (fun lam => G - partialInt g (u + k * δ M + lam)) := by
          simp_rw [rVariationOn_const_smul hr0]
      _ ≤ ∑ k ∈ Finset.range (M + 1 + 1), ‖c k‖ₑ * V := by
          refine Finset.sum_le_sum fun k _ => ?_
          gcongr
          exact rVariationOn_const_sub_shift_le S G _ _
      _ = (∑ k ∈ Finset.range (M + 1 + 1), ‖c k‖ₑ) * V := by rw [Finset.sum_mul]
      _ ≤ ENNReal.ofReal B * V := by
          gcongr
          exact (sum_enorm_jumps_le h u (hδpos M) _).trans hB
  -- pointwise convergence of the multiplier outputs
  have hBV : BoundedVariationOn h Set.univ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hB
  have hdiff : ∀ᵐ s : ℝ, DifferentiableAt ℝ h s :=
    hBV.locallyBoundedVariationOn.ae_differentiableAt
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have h1 := (tendsto_const_div_atTop_nhds_zero_nat (w' - u + 1)).comp (tendsto_add_atTop_nat 1)
    refine h1.congr fun M => ?_
    simp [hδdef]
  have hconv : ∀ lam : ℝ, Tendsto (fun M : ℕ => mulInt (gridStep h u (δ M) (M + 1)) g lam) atTop
      (𝓝 (mulInt h g lam)) := by
    intro lam
    refine tendsto_integral_of_dominated_convergence (fun ξ => B * ‖g ξ‖) ?_ ?_ ?_ ?_
    · intro M
      exact (((measurable_gridStep h u (δ M) (M + 1)).comp
        (measurable_id.sub measurable_const)).aestronglyMeasurable).mul hg.aestronglyMeasurable
    · exact hg.norm.const_mul B
    · intro M
      filter_upwards with ξ
      rw [norm_mul, gridStep_eq (hδpos M) hsupp' (hK M)]
      exact mul_le_mul_of_nonneg_right (hnorm _) (norm_nonneg _)
    · have hae : ∀ᵐ ξ : ℝ, DifferentiableAt ℝ h (ξ - lam) :=
        (measurePreserving_sub_right volume lam).quasiMeasurePreserving.ae hdiff
      filter_upwards [hae] with ξ hξ
      refine Tendsto.mul_const _ ?_
      set s := ξ - lam with hs
      have hy : Tendsto (fun M : ℕ => u + ⌊(s - u) / δ M⌋ * δ M) atTop (𝓝 s) := by
        have hlo : ∀ M : ℕ, s - δ M ≤ u + ⌊(s - u) / δ M⌋ * δ M := fun M => by
          have h2 := (div_lt_iff₀ (hδpos M)).1 (Int.lt_floor_add_one ((s - u) / δ M))
          linarith
        have hhi : ∀ M : ℕ, u + ⌊(s - u) / δ M⌋ * δ M ≤ s := fun M => by
          have h1 := Int.floor_le ((s - u) / δ M)
          have h2 := (le_div_iff₀ (hδpos M)).1 h1
          linarith
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds hlo hhi
        simpa using (tendsto_const_nhds (x := s)).sub hδlim
      have hcont : ContinuousAt h s := hξ.continuousAt
      simp_rw [gridStep_eq (hδpos _) hsupp' (hK _)]
      exact hcont.tendsto.comp hy
  -- the bound passes to the limit chain by chain
  refine rVariationOn_le fun J t hm hS => ?_
  set L : ℕ → ℝ≥0∞ := fun M =>
    (∑ i : Fin J, ‖mulInt (gridStep h u (δ M) (M + 1)) g (t i.castSucc) -
      mulInt (gridStep h u (δ M) (M + 1)) g (t i.succ)‖ₑ ^ r) ^ (1 / r) with hL
  have hlim : Tendsto L atTop
      (𝓝 ((∑ i : Fin J, ‖mulInt h g (t i.castSucc) - mulInt h g (t i.succ)‖ₑ ^ r) ^ (1 / r))) := by
    refine (ENNReal.continuous_rpow_const.tendsto _).comp ?_
    refine tendsto_finsetSum _ fun i _ => ?_
    exact (ENNReal.continuous_rpow_const.tendsto _).comp
      (((hconv _).sub (hconv _)).enorm)
  exact le_of_tendsto' hlim fun M => (le_rVariationOn hm hS).trans (hbd M)

end PrimeCarleson.Proof.Paper

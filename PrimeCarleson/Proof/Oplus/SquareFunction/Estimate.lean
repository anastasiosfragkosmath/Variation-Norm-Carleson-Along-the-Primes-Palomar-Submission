module

public import PrimeCarleson.Proof.Oplus.SquareFunction.Scales

/-!
# The square-function estimate at `p = 2`

The square-function estimate of Jones–Kaufman–Rosenblatt–Wierdl at `p = 2` ([O+], L2019–L2022;
proved here): for a Schwartz function `ψ` with `∫ ψ = 1` and `f ∈ L²(ℝ)`,
`∑_{k ∈ ℤ} ‖A_k f - E_k f‖₂² ≤ C_ψ² ‖f‖₂²`,
equivalently `‖(∑_k |A_k f - E_k f|²)^{1/2}‖₂ ≤ C_ψ ‖f‖₂`.

Proof: `T_k = A_k - E_k`; the telescoping `f_J = E_{-J} f - E_J f = ∑_{-J<j≤J} D_j f`
and the per-scale bound `‖T_k D_j f‖₂ ≤ ρ(k - j) ‖D_j f‖₂` (`Scales.lean`) give
`‖T_k f_J‖₂ ≤ ∑_j ρ(k - j) ‖D_j f‖₂`; `f_J → f` in `L²` (`Convergence.lean`) lets `J → ∞`; and
Young's inequality on
`ℤ` together with Bessel's inequality `∑_j ‖D_j f‖₂² ≤ ‖f‖₂²` finish.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal SchwartzMap

open PrimeCarleson.Proof.Lepingle

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-! ### Linearity of `T_k` -/

theorem schwartzSqOp_add (ψ : 𝓢(ℝ, ℂ)) (k : ℤ) {g h : ℝ → ℂ} (hg : Measurable g)
    (hgL : MemLp g 2 volume) (hh : Measurable h) (hhL : MemLp h 2 volume) :
    schwartzSqOp ψ k (g + h) = schwartzSqOp ψ k g + schwartzSqOp ψ k h := by
  funext x
  simp only [schwartzSqOp, Pi.add_apply]
  rw [schwartzAvg_add ψ k hg (lintegral_sq_lt_top_of_memLp hgL) hh
    (lintegral_sq_lt_top_of_memLp hhL) x, dyadicAvg_add hgL hhL k x]
  ring

/-- `T_k 0 = 0`. -/
theorem schwartzSqOp_zero (ψ : 𝓢(ℝ, ℂ)) (k : ℤ) : schwartzSqOp ψ k 0 = 0 := by
  funext x
  simp [schwartzSqOp, schwartzAvg, dyadicAvg]

/-- `T_k g` is measurable for measurable `g`. -/
theorem measurable_schwartzSqOp (ψ : 𝓢(ℝ, ℂ)) (k : ℤ) {g : ℝ → ℂ} (hg : Measurable g) :
    Measurable (schwartzSqOp ψ k g) :=
  (measurable_schwartzAvg ψ k hg).sub (measurable_dyadicAvg g k)

/-- `T_k` is bounded on `L²`: `‖T_k g‖₂ ≤ (‖ψ‖₁ + 1) ‖g‖₂`. -/
theorem eLpNorm_schwartzSqOp_le (ψ : 𝓢(ℝ, ℂ)) (k : ℤ) {g : ℝ → ℂ} (hg : Measurable g)
    (hgL : MemLp g 2 volume) :
    eLpNorm (schwartzSqOp ψ k g) 2 volume ≤
      (ENNReal.ofReal (kappaPsi ψ) + 1) * eLpNorm g 2 volume := by
  have h1 : eLpNorm (schwartzAvg ψ k g) 2 volume ≤
      ENNReal.ofReal (kappaPsi ψ) * eLpNorm g 2 volume := by
    refine eLpNorm_le_of_sqn_le (measurable_schwartzAvg ψ k hg).aestronglyMeasurable
      hg.aestronglyMeasurable ?_
    rw [ofReal_kappaPsi]
    exact sqn_schwartzAvg_le ψ k hg
  have h2 : eLpNorm (dyadicAvg g k) 2 volume ≤ 1 * eLpNorm g 2 volume := by
    refine eLpNorm_le_of_sqn_le (measurable_dyadicAvg g k).aestronglyMeasurable
      hg.aestronglyMeasurable ?_
    rw [one_pow, one_mul]
    exact sqn_dyadicAvg_le hgL k
  calc eLpNorm (schwartzSqOp ψ k g) 2 volume
      = eLpNorm (schwartzAvg ψ k g - dyadicAvg g k) 2 volume := rfl
    _ ≤ eLpNorm (schwartzAvg ψ k g) 2 volume + eLpNorm (dyadicAvg g k) 2 volume :=
        eLpNorm_sub_le (by norm_num)
    _ ≤ ENNReal.ofReal (kappaPsi ψ) * eLpNorm g 2 volume + 1 * eLpNorm g 2 volume :=
        add_le_add h1 h2
    _ = (ENNReal.ofReal (kappaPsi ψ) + 1) * eLpNorm g 2 volume := by rw [add_mul]

/-! ### Finite telescoping -/

/-- `T_k (E_a f - E_{a+N} f) = ∑_{i<N} T_k D_{a+i+1} f` in `L²` norm (triangle inequality). -/
theorem eLpNorm_schwartzSqOp_telescope (ψ : 𝓢(ℝ, ℂ)) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (k a : ℤ) (N : ℕ) :
    eLpNorm (schwartzSqOp ψ k (dyadicAvg f a - dyadicAvg f (a + N))) 2 volume ≤
      ∑ i ∈ Finset.range N, eLpNorm (schwartzSqOp ψ k (dyadicDiff f (a + i + 1))) 2 volume := by
  induction N with
  | zero =>
    have : dyadicAvg f a - dyadicAvg f (a + ((0 : ℕ) : ℤ)) = 0 := by simp
    rw [this, schwartzSqOp_zero]
    simp
  | succ N ih =>
    have hgm : Measurable (dyadicAvg f a - dyadicAvg f (a + N)) :=
      (measurable_dyadicAvg f a).sub (measurable_dyadicAvg f _)
    have hgL : MemLp (dyadicAvg f a - dyadicAvg f (a + N)) 2 volume :=
      (memLp_dyadicAvg hf a).sub (memLp_dyadicAvg hf _)
    have hsplit : dyadicAvg f a - dyadicAvg f (a + ((N + 1 : ℕ) : ℤ)) =
        (dyadicAvg f a - dyadicAvg f (a + N)) + dyadicDiff f (a + N + 1) := by
      funext x
      have e1 : a + ((N + 1 : ℕ) : ℤ) = a + N + 1 := by push_cast; ring
      simp only [Pi.add_apply, Pi.sub_apply, dyadicDiff, e1, add_sub_cancel_right]
      ring
    rw [hsplit, schwartzSqOp_add ψ k hgm hgL (measurable_dyadicDiff f _) (memLp_dyadicDiff hf _),
      Finset.sum_range_succ]
    calc eLpNorm (schwartzSqOp ψ k (dyadicAvg f a - dyadicAvg f (a + N)) +
          schwartzSqOp ψ k (dyadicDiff f (a + N + 1))) 2 volume
        ≤ eLpNorm (schwartzSqOp ψ k (dyadicAvg f a - dyadicAvg f (a + N))) 2 volume +
          eLpNorm (schwartzSqOp ψ k (dyadicDiff f (a + N + 1))) 2 volume :=
          eLpNorm_add_le (by norm_num)
      _ ≤ _ := add_le_add ih le_rfl

/-! ### The limit `J → ∞` -/

theorem tendsto_eLpNorm_of_tendsto_sqn {g : ℕ → ℝ → ℂ}
    (hg : ∀ J, AEStronglyMeasurable (g J) volume)
    (h : Tendsto (fun J => ∫⁻ x, ‖g J x‖ₑ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun J => eLpNorm (g J) 2 volume) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero] at h ⊢
  intro ε hε
  filter_upwards [h (ε ^ 2) (ENNReal.pow_pos hε 2)] with J hJ
  rw [lintegral_sq_eq_eLpNorm_sq (hg J)] at hJ
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hJ

/-- A finite sum along an injective integer progression is bounded by the `tsum` over `ℤ`. -/
theorem sum_range_le_tsum_int (F : ℤ → ℝ≥0∞) (c : ℤ) (N : ℕ) :
    ∑ i ∈ Finset.range N, F (c + i + 1) ≤ ∑' j, F j := by
  have hinj : Function.Injective fun i : ℕ => c + (i : ℤ) + 1 := fun i i' h => by
    simp only at h
    omega
  calc ∑ i ∈ Finset.range N, F (c + i + 1)
      = ∑ j ∈ (Finset.range N).image (fun i : ℕ => c + (i : ℤ) + 1), F j :=
        (Finset.sum_image (fun i _ i' _ h => hinj h)).symm
    _ ≤ ∑' j, F j := ENNReal.sum_le_tsum _

/-- For every `k`: `‖T_k f‖₂ ≤ ∑_j ρ(k - j) ‖D_j f‖₂`. -/
theorem eLpNorm_schwartzSqOp_le_tsum (ψ : 𝓢(ℝ, ℂ)) (hψ : ∫ t, ψ t = 1) {C : ℝ}
    (hC : ∀ u : ℝ, (1 + |u|) ^ 2 * ‖deriv ψ u‖ ≤ C) {f : ℝ → ℂ} (hfm : Measurable f)
    (hf : MemLp f 2 volume) (k : ℤ) :
    eLpNorm (schwartzSqOp ψ k f) 2 volume ≤
      ∑' j : ℤ, ENNReal.ofReal (sqRate (thetaPsi C) (Real.sqrt (8 * kappaPsi ψ * muPsi ψ))
        (k - j)) * eLpNorm (dyadicDiff f j) 2 volume := by
  set S : ℝ≥0∞ := ∑' j : ℤ, ENNReal.ofReal (sqRate (thetaPsi C)
    (Real.sqrt (8 * kappaPsi ψ * muPsi ψ)) (k - j)) * eLpNorm (dyadicDiff f j) 2 volume with hS
  set b : ℕ → ℝ≥0∞ := fun J => eLpNorm (fun x => f x - dyadicAvg f (-(J : ℤ)) x) 2 volume with hb
  set c : ℕ → ℝ≥0∞ := fun J => eLpNorm (dyadicAvg f (J : ℤ)) 2 volume with hc
  set e : ℕ → ℝ≥0∞ := fun J => (ENNReal.ofReal (kappaPsi ψ) + 1) * (b J + c J) with he
  have hb0 : Tendsto b atTop (𝓝 0) :=
    tendsto_eLpNorm_of_tendsto_sqn (g := fun J x => f x - dyadicAvg f (-(J : ℤ)) x)
      (fun J => (hfm.sub (measurable_dyadicAvg f _)).aestronglyMeasurable)
      (tendsto_sqn_sub_dyadicAvg_atBot hfm hf)
  have hc0 : Tendsto c atTop (𝓝 0) :=
    tendsto_eLpNorm_of_tendsto_sqn (g := fun J => dyadicAvg f (J : ℤ))
      (fun J => (measurable_dyadicAvg f _).aestronglyMeasurable)
      (tendsto_sqn_dyadicAvg_atTop hfm hf)
  have he0 : Tendsto e atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (kappaPsi ψ) + 1) (hb0.add hc0)
      (Or.inr (by simp))
    simpa using this
  have key : ∀ J : ℕ, eLpNorm (schwartzSqOp ψ k f) 2 volume ≤ S + e J := by
    intro J
    set fJ : ℝ → ℂ := dyadicAvg f (-(J : ℤ)) - dyadicAvg f (-(J : ℤ) + ((2 * J : ℕ) : ℤ)) with hfJ
    have hJ : -(J : ℤ) + ((2 * J : ℕ) : ℤ) = (J : ℤ) := by push_cast; ring
    have hfJm : Measurable fJ := (measurable_dyadicAvg f _).sub (measurable_dyadicAvg f _)
    have hfJL : MemLp fJ 2 volume := (memLp_dyadicAvg hf _).sub (memLp_dyadicAvg hf _)
    have hsplit : f = fJ + (f - fJ) := by simp
    have h1 : eLpNorm (schwartzSqOp ψ k f) 2 volume ≤
        eLpNorm (schwartzSqOp ψ k fJ) 2 volume + eLpNorm (schwartzSqOp ψ k (f - fJ)) 2 volume := by
      conv_lhs => rw [hsplit]
      rw [schwartzSqOp_add ψ k hfJm hfJL (hfm.sub hfJm) (hf.sub hfJL)]
      exact eLpNorm_add_le (by norm_num)
    have h2 : eLpNorm (schwartzSqOp ψ k fJ) 2 volume ≤ S := by
      refine (eLpNorm_schwartzSqOp_telescope ψ hf k (-(J : ℤ)) (2 * J)).trans ?_
      refine le_trans (Finset.sum_le_sum fun i _ => ?_)
        (sum_range_le_tsum_int (fun j => ENNReal.ofReal (sqRate (thetaPsi C)
          (Real.sqrt (8 * kappaPsi ψ * muPsi ψ)) (k - j)) * eLpNorm (dyadicDiff f j) 2 volume)
          (-(J : ℤ)) (2 * J))
      exact eLpNorm_schwartzSqOp_dyadicDiff_le ψ hψ hC hf _ k
    have h3 : eLpNorm (schwartzSqOp ψ k (f - fJ)) 2 volume ≤ e J := by
      refine (eLpNorm_schwartzSqOp_le ψ k (hfm.sub hfJm) (hf.sub hfJL)).trans ?_
      refine mul_le_mul_right ?_ _
      have hrew : f - fJ = (fun x => f x - dyadicAvg f (-(J : ℤ)) x) + dyadicAvg f (J : ℤ) := by
        funext x
        simp only [hfJ, hJ, Pi.sub_apply, Pi.add_apply]
        ring
      rw [hrew]
      exact eLpNorm_add_le (by norm_num)
    calc eLpNorm (schwartzSqOp ψ k f) 2 volume ≤ _ := h1
      _ ≤ S + e J := add_le_add h2 h3
  have hlim : Tendsto (fun J => S + e J) atTop (𝓝 (S + 0)) := tendsto_const_nhds.add he0
  simpa using ge_of_tendsto' hlim key

/-! ### The estimate -/

/-- The constant `C_ψ = ∑_m ρ(m)` of the square-function estimate at `p = 2`. -/
def squareFunctionConst (ψ : 𝓢(ℝ, ℂ)) (C : ℝ) : ℝ≥0∞ :=
  ∑' m : ℤ, ENNReal.ofReal (sqRate (thetaPsi C) (Real.sqrt (8 * kappaPsi ψ * muPsi ψ)) m)

/-- The constant `C_ψ` is finite. -/
theorem squareFunctionConst_lt_top (ψ : 𝓢(ℝ, ℂ)) (C : ℝ) : squareFunctionConst ψ C < ∞ :=
  tsum_ofReal_sqRate_lt_top (thetaPsi_nonneg C) (Real.sqrt_nonneg _)

/-- `∑_k ‖A_k f - E_k f‖₂² ≤ C_ψ² ‖f‖₂²` for measurable `f ∈ L²`. -/
theorem tsum_eLpNorm_sq_schwartzSqOp_le (ψ : 𝓢(ℝ, ℂ)) (hψ : ∫ t, ψ t = 1) {C : ℝ}
    (hC : ∀ u : ℝ, (1 + |u|) ^ 2 * ‖deriv ψ u‖ ≤ C) {f : ℝ → ℂ} (hfm : Measurable f)
    (hf : MemLp f 2 volume) :
    ∑' k : ℤ, eLpNorm (schwartzSqOp ψ k f) 2 volume ^ 2 ≤
      squareFunctionConst ψ C ^ 2 * eLpNorm f 2 volume ^ 2 := by
  have h1 := tsum_sq_le_of_convolution_bound
    (ρ := fun m => ENNReal.ofReal (sqRate (thetaPsi C) (Real.sqrt (8 * kappaPsi ψ * muPsi ψ)) m))
    (a := fun j => eLpNorm (dyadicDiff f j) 2 volume)
    (S := fun k => eLpNorm (schwartzSqOp ψ k f) 2 volume)
    (fun k => eLpNorm_schwartzSqOp_le_tsum ψ hψ hC hfm hf k)
  refine h1.trans ?_
  refine mul_le_mul_right ?_ _
  have h2 := tsum_sqn_dyadicDiff_le hf
  rw [lintegral_sq_eq_eLpNorm_sq hfm.aestronglyMeasurable] at h2
  refine le_trans (le_of_eq ?_) h2
  refine tsum_congr fun j => ?_
  rw [lintegral_sq_eq_eLpNorm_sq (measurable_dyadicDiff f j).aestronglyMeasurable]

/-- **The square-function estimate at `p = 2`** (Jones–Kaufman–Rosenblatt–Wierdl),
pointwise form for measurable `f`:
`∫ ∑_k |A_k f - E_k f|² ≤ C_ψ² ∫ |f|²`. -/
theorem lintegral_tsum_schwartzSqOp_sq_le (ψ : 𝓢(ℝ, ℂ)) (hψ : ∫ t, ψ t = 1) {C : ℝ}
    (hC : ∀ u : ℝ, (1 + |u|) ^ 2 * ‖deriv ψ u‖ ≤ C) {f : ℝ → ℂ} (hfm : Measurable f)
    (hf : MemLp f 2 volume) :
    ∫⁻ x, ∑' k : ℤ, ‖schwartzSqOp ψ k f x‖ₑ ^ 2 ≤
      squareFunctionConst ψ C ^ 2 * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  rw [lintegral_tsum fun k => ((measurable_schwartzSqOp ψ k hfm).enorm.pow_const 2).aemeasurable,
    lintegral_sq_eq_eLpNorm_sq hfm.aestronglyMeasurable]
  have := tsum_eLpNorm_sq_schwartzSqOp_le ψ hψ hC hfm hf
  refine le_trans (le_of_eq ?_) this
  refine tsum_congr fun k => ?_
  rw [lintegral_sq_eq_eLpNorm_sq (measurable_schwartzSqOp ψ k hfm).aestronglyMeasurable]

end PrimeCarleson.Proof.Oplus

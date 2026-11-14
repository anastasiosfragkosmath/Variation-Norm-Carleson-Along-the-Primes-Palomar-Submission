module

public import PrimeCarleson.Proof.Paper.P6a.KQTile

/-!
# `l:varcarZ` for an integrable multiplier of bounded variation

`tile_varOp_bound`: if `m : ℝ → ℂ` is integrable with total variation `≤ c₀` and `‖m‖_{L¹} ≤ L`,
the kernel `g(n) = ∫ m(ξ) e(nξ) dξ` satisfies
`‖V^r(∑_n f(x-n) g(n) e(λ n) : λ)‖_{ℓ²} ≲_r (c₀ + L) ‖f‖_{ℓ²}`, by cutting `m` into the tiles
`hat t · m` (supported in intervals of length `1/10`, total variation `3 v_t + 80 H_t`) and applying
`VarCarZ` to each, `∑_t (3 v_t + 80 H_t) ≤ 6 c₀ + 80 L`. The shifted kernel `g(n) e(c n)` is the
kernel of the shifted multiplier `m(· - c)` (`tile_varOp_bound_shift`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common

/-- **`l:varcarZ` for an integrable multiplier of bounded variation**: there is `C` such that for
every integrable `m` with `V(m; ℝ) ≤ c₀`, `∫ |m| ≤ L`, and every finitely supported `f`,
`‖V^r(∑_n f(x-n) g(n) e(λ n) : λ)‖_{ℓ²} ≤ C (c₀ + L) ‖f‖_{ℓ²}`, `g(n) = ∫ m(ξ) e(nξ) dξ`. -/
theorem tile_varOp_bound {r : ℝ} (hr : 2 < r) (hV : VarCarZ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℝ → ℂ) (c₀ L : ℝ), 0 ≤ c₀ → 0 ≤ L → Integrable m →
      eVariationOn m univ ≤ ENNReal.ofReal c₀ → (∫ ξ, ‖m ξ‖) ≤ L → ∀ f : ℤ →₀ ℂ,
        eLpNorm (varOp r (fun n : ℤ => ∫ ξ : ℝ, m ξ * e ((n : ℝ) * ξ)) (⇑f))
            (ENNReal.ofReal 2) Measure.count ≤
          ENNReal.ofReal (C * (c₀ + L)) * eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by
  obtain ⟨C_V, hC_V0, hVC⟩ := hV
  have hr2 : 0 < r - 2 := by linarith
  set K₁ : ℝ := C_V * (r / (r - 2)) with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  refine ⟨80 * K₁, by positivity, fun m c₀ L hc₀ hL hm hTV hint f => ?_⟩
  -- the tile kernels
  set k : ℤ → ℤ → ℂ := fun t n => ∫ ξ : ℝ, tile m t ξ * e ((n : ℝ) * ξ) with hk
  set g : ℤ → ℂ := fun n => ∫ ξ : ℝ, m ξ * e ((n : ℝ) * ξ) with hg
  have hecont : ∀ n : ℤ, Continuous fun ξ : ℝ => e ((n : ℝ) * ξ) := fun n =>
    Common.continuous_e.comp (continuous_const.mul continuous_id)
  have hkern : ∀ n : ℤ, HasSum (fun t => k t n) (g n) := by
    intro n
    refine hasSum_integral_of_dominated_convergence (fun t ξ => hat t ξ * ‖m ξ‖)
      (fun t => ?_) (fun t => ae_of_all _ fun ξ => ?_)
      (ae_of_all _ fun ξ => ((hasSum_hat ξ).mul_right ‖m ξ‖).summable) ?_ ?_
    · exact (((Complex.continuous_ofReal.comp (continuous_hat t)).aestronglyMeasurable).mul
        hm.1).mul (hecont n).aestronglyMeasurable
    · simp [tile, Goal0.norm_e, abs_of_nonneg (hat_nonneg t ξ)]
    · refine hm.norm.congr (ae_of_all _ fun ξ => ?_)
      simpa using ((hasSum_hat ξ).mul_right ‖m ξ‖).tsum_eq.symm
    · refine ae_of_all _ fun ξ => ?_
      have h1 : HasSum (fun t : ℤ => ((hat t ξ : ℝ) : ℂ)) 1 := by
        simpa using Complex.hasSum_ofReal.2 (hasSum_hat ξ)
      have h2 := h1.mul_right (m ξ * e ((n : ℝ) * ξ))
      simpa [tile, mul_assoc] using h2
  -- the sum over tiles in the variation
  have hpt : ∀ x : ℤ, varOp r g (⇑f) x ≤ ∑' t : ℤ, varOp r (k t) (⇑f) x := by
    intro x
    unfold varOp pointwiseVariation
    rw [rVariation_eq_rVariationOn]
    simp only [rVariation_eq_rVariationOn]
    refine rVariationOn_tsum_le (by linarith) (Set.Ico 0 1)
      (fun t lam => weightedModSum (k t) (⇑f) lam x) (fun lam => weightedModSum g (⇑f) lam x)
      (fun lam => ?_)
    simp only [weightedModSum_eq_sum_of_finsupp]
    exact hasSum_sum fun n _ => by
      simpa [mul_assoc] using ((hkern n).mul_left (f (x - n) * 1)).mul_right (e (lam * n))
  -- each tile
  have hVfin : ∀ t : ℤ, eVariationOn m (Icc (tileL t) (tileR t)) ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((eVariationOn.mono m (subset_univ _)).trans hTV)
  have htile : ∀ t : ℤ, eLpNorm (varOp r (k t) (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
      ENNReal.ofReal (K₁ * (3 * (eVariationOn m (Icc (tileL t) (tileR t))).toReal +
        80 * ∫ η, hat t η * ‖m η‖)) * eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by
    intro t
    have hc : 0 ≤ 3 * (eVariationOn m (Icc (tileL t) (tileR t))).toReal +
        80 * ∫ η, hat t η * ‖m η‖ :=
      add_nonneg (by positivity) (mul_nonneg (by norm_num)
        (integral_nonneg fun η => mul_nonneg (hat_nonneg t η) (norm_nonneg _)))
    have hsupp : ∀ ξ : ℝ, tile m t ξ ≠ 0 → tileL t ≤ ξ ∧ ξ ≤ tileL t + 1 / 10 := by
      intro ξ hξ
      by_contra hcon
      apply hξ
      refine tile_eq_zero m t fun h => hcon ⟨h.1.le, ?_⟩
      have := h.2
      unfold tileL tileR at *
      linarith
    have := hVC (tile m t) (tileL t) hsupp _ hc (eVariationOn_tile_le hm t (hVfin t)) f
    refine this.trans (mul_le_mul' (le_of_eq ?_) le_rfl)
    congr 1
    rw [hK₁]; ring
  -- summation
  have hsumTV : ∑' t : ℤ, ENNReal.ofReal ((eVariationOn m (Icc (tileL t) (tileR t))).toReal) ≤
      2 * ENNReal.ofReal c₀ := by
    refine le_trans (le_of_eq (tsum_congr fun t => ENNReal.ofReal_toReal (hVfin t))) ?_
    exact (tsum_eVariationOn_tile_le m).trans (mul_le_mul' le_rfl hTV)
  have hH0 : ∀ t : ℤ, 0 ≤ ∫ η, hat t η * ‖m η‖ := fun t =>
    integral_nonneg fun η => mul_nonneg (hat_nonneg t η) (norm_nonneg _)
  have hsumH : ∑' t : ℤ, ENNReal.ofReal (∫ η, hat t η * ‖m η‖) ≤ ENNReal.ofReal L := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hH0 (hasSum_hat_integral hm).summable,
      (hasSum_hat_integral hm).tsum_eq]
    exact ENNReal.ofReal_le_ofReal hint
  -- conclusion
  calc eLpNorm (varOp r g (⇑f)) (ENNReal.ofReal 2) Measure.count
      ≤ eLpNorm (fun x => ∑' t : ℤ, varOp r (k t) (⇑f) x) (ENNReal.ofReal 2) Measure.count :=
        eLpNorm_count_mono_enn hpt _
    _ ≤ ∑' t : ℤ, eLpNorm (varOp r (k t) (⇑f)) (ENNReal.ofReal 2) Measure.count :=
        eLpNorm_count_tsum_le _ (by norm_num)
    _ ≤ ∑' t : ℤ, ENNReal.ofReal (K₁ * (3 * (eVariationOn m (Icc (tileL t) (tileR t))).toReal +
          80 * ∫ η, hat t η * ‖m η‖)) * eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count :=
        ENNReal.tsum_le_tsum htile
    _ = (∑' t : ℤ, ENNReal.ofReal (K₁ * (3 * (eVariationOn m (Icc (tileL t)
          (tileR t))).toReal + 80 * ∫ η, hat t η * ‖m η‖))) *
          eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by rw [ENNReal.tsum_mul_right]
    _ ≤ ENNReal.ofReal (80 * K₁ * (c₀ + L)) * eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by
        refine mul_le_mul' ?_ le_rfl
        have e1 : ∀ t : ℤ, ENNReal.ofReal (K₁ * (3 * (eVariationOn m (Icc (tileL t)
            (tileR t))).toReal + 80 * ∫ η, hat t η * ‖m η‖)) =
            ENNReal.ofReal (3 * K₁) * ENNReal.ofReal ((eVariationOn m (Icc (tileL t)
              (tileR t))).toReal) + ENNReal.ofReal (80 * K₁) *
              ENNReal.ofReal (∫ η, hat t η * ‖m η‖) := by
          intro t
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (mul_nonneg (by positivity) (hH0 t))]
          congr 1; ring
        simp_rw [e1]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
        calc ENNReal.ofReal (3 * K₁) * ∑' t : ℤ, ENNReal.ofReal ((eVariationOn m (Icc (tileL t)
              (tileR t))).toReal) + ENNReal.ofReal (80 * K₁) *
              ∑' t : ℤ, ENNReal.ofReal (∫ η, hat t η * ‖m η‖)
            ≤ ENNReal.ofReal (3 * K₁) * (2 * ENNReal.ofReal c₀) +
              ENNReal.ofReal (80 * K₁) * ENNReal.ofReal L :=
              add_le_add (mul_le_mul' le_rfl hsumTV) (mul_le_mul' le_rfl hsumH)
          _ = ENNReal.ofReal (6 * K₁ * c₀ + 80 * K₁ * L) := by
              rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity),
                ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
                ← ENNReal.ofReal_add (by positivity) (by positivity)]
              congr 1; ring
          _ ≤ ENNReal.ofReal (80 * K₁ * (c₀ + L)) := by
              refine ENNReal.ofReal_le_ofReal ?_
              nlinarith [mul_nonneg hK₁0 hc₀]

/-- **The shifted version** (`c ∈ ℝ`): the kernel `g(n) e(c n)` is the kernel of `m(· - c)`. -/
theorem tile_varOp_bound_shift {r : ℝ} (hr : 2 < r) (hV : VarCarZ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℝ → ℂ) (c₀ L : ℝ), 0 ≤ c₀ → 0 ≤ L → Integrable m →
      eVariationOn m univ ≤ ENNReal.ofReal c₀ → (∫ ξ, ‖m ξ‖) ≤ L → ∀ (c : ℝ) (f : ℤ →₀ ℂ),
        eLpNorm (varOp r (fun n : ℤ => (∫ ξ : ℝ, m ξ * e ((n : ℝ) * ξ)) * e (c * (n : ℝ)))
            (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
          ENNReal.ofReal (C * (c₀ + L)) * eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by
  obtain ⟨C, hC0, hC⟩ := tile_varOp_bound hr hV
  refine ⟨C, hC0, fun m c₀ L hc₀ hL hm hTV hint c f => ?_⟩
  set m' : ℝ → ℂ := fun ξ => m (ξ - c) with hm'
  have hTV' : eVariationOn m' univ ≤ ENNReal.ofReal c₀ := by
    have h := eVariationOn.comp_eq_of_monotoneOn m (fun ξ : ℝ => ξ - c) (t := univ)
      (fun a _ b _ hab => by simpa using hab)
    have himg : (fun ξ : ℝ => ξ - c) '' univ = univ := by
      ext y; simp only [image_univ, mem_range, mem_univ, iff_true]; exact ⟨y + c, by ring⟩
    rw [himg] at h
    exact h.le.trans hTV
  have hint' : (∫ ξ, ‖m' ξ‖) ≤ L := by
    have := integral_sub_right_eq_self (μ := volume) (fun ξ : ℝ => ‖m ξ‖) c
    simpa [hm'] using this.le.trans hint
  have hker : ∀ n : ℤ, (∫ ξ : ℝ, m' ξ * e ((n : ℝ) * ξ)) =
      (∫ ξ : ℝ, m ξ * e ((n : ℝ) * ξ)) * e (c * (n : ℝ)) := by
    intro n
    have h := integral_sub_right_eq_self (μ := volume) (fun ξ : ℝ => m ξ * e ((n : ℝ) * (ξ + c))) c
    simp only [sub_add_cancel] at h
    simp only [hm']
    rw [h, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [mul_add, Goal0.e_add]
    rw [mul_comm (n : ℝ) c]
    ring
  have := hC m' c₀ L hc₀ hL (hm.comp_sub_right c) hTV' hint' f
  simpa only [hker] using this

end PrimeCarleson.Proof.Paper

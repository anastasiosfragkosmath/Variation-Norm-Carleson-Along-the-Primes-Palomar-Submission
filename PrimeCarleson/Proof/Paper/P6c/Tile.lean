module

public import PrimeCarleson.Proof.Paper.P6c.Basic
public import PrimeCarleson.Proof.Paper.P6a.KQTile2
public import PrimeCarleson.Proof.Paper.P6b.Adapter
public import PrimeCarleson.Proof.Paper.P6b.Crude
public import PrimeCarleson.Proof.Paper.P7.DiscSup

/-!
# The maximal estimate for a multiplier of bounded variation

Source: main paper `s:red`, L1527–L1528 ("the replacement of `∑ ψ_k` by `K_Q` is identical"; the
variational error bounds control `V^r` of the error, but the supremum over `λ` needs the pointwise
maximal operator, which the paper does not prove and which is proved here). The maximal counterpart
of `tile_varOp_bound` of `P6a/KQTile2.lean`:

* `sup_tile_kernel`: for `m` vanishing off an interval of length `≤ 1/10` and of total variation
  `≤ c₀` the kernel `g(n) = ∫ m(ξ) e(nξ) dξ` has
  `‖sup_λ|∑_n f(x-n) g(n) e(λ n)|‖_{ℓ^p} ≤ C c₀ ‖f‖_{ℓ^p}` for every `1 < p < ∞`
  (`sup_modulated_one` of `P7/DiscSup.lean`: the supremum is bounded directly, so no `ℓ²`-endpoint,
  no `p > r'` and no interpolation is needed);
* `tile_sup_bound`: the same for an integrable `m` of bounded variation, with `c₀ + ∫|m|`, by the
  tiles `hat t · m` of `P6a/KQTile.lean`.

Conditional on `hO : OplusVariationBound`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-- The kernel of the translated multiplier:
`∫ m(ξ - c) e(nξ) dξ = e(c n) ∫ m(ξ) e(nξ) dξ`. -/
theorem integral_shift_kernel (m : ℝ → ℂ) (c : ℝ) (n : ℤ) :
    (∫ ξ : ℝ, m (ξ - c) * e ((n : ℝ) * ξ)) =
      (∫ ξ : ℝ, m ξ * e ((n : ℝ) * ξ)) * e (c * (n : ℝ)) := by
  have h := integral_sub_right_eq_self (μ := volume)
    (fun ξ : ℝ => m ξ * e ((n : ℝ) * (ξ + c))) c
  simp only [sub_add_cancel] at h
  rw [h, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [mul_add, e_add]
  rw [mul_comm (n : ℝ) c]
  ring

/-- **`l:varcarZ` for the supremum** (conditional on `hO`): for `1 < p < ∞` there is `C` such that
for every `m : ℝ → ℂ` vanishing off `[a, a + 1/10]` with total variation `≤ c₀`, the kernel
`g(n) = ∫ m(ξ) e(nξ) dξ` satisfies `‖sup_λ|∑_n f(x-n) g(n) e(λ n)|‖_{ℓ^p} ≤ C c₀ ‖f‖_{ℓ^p}`. -/
theorem sup_tile_kernel (hO : OplusVariationBound) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℝ → ℂ) (a : ℝ), (∀ ξ, m ξ ≠ 0 → a ≤ ξ ∧ ξ ≤ a + 1 / 10) →
      ∀ c₀ : ℝ, 0 ≤ c₀ → eVariationOn m univ ≤ ENNReal.ofReal c₀ → ∀ f : ℤ →₀ ℂ,
        eLpNorm (supOp (fun n : ℤ => ∫ ξ : ℝ, m ξ * e ((n : ℝ) * ξ)) (⇑f))
            (ENNReal.ofReal p) Measure.count ≤
          ENNReal.ofReal (C * c₀) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨r, hr, hrp⟩ := exists_exponent_gt hp
  obtain ⟨C, hC0, hC⟩ := sup_modulated_one hO hr hrp
  refine ⟨C, hC0, fun m a hsupp c₀ hc₀ hvar f => ?_⟩
  set c : ℝ := a + 1 / 20 with hc
  set m' : ℝ → ℂ := fun ξ => m (ξ - -c) with hm'
  have hfin : BoundedVariationOn m univ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvar
  have hmeas : Measurable m' := hfin.measurable.comp (measurable_id.sub_const _)
  have hTV' : eVariationOn m' univ ≤ ENNReal.ofReal c₀ := by
    have h := eVariationOn.comp_eq_of_monotoneOn m (fun ξ : ℝ => ξ - -c) (t := univ)
      (fun a _ b _ hab => by simpa using hab)
    have himg : (fun ξ : ℝ => ξ - -c) '' univ = univ := by
      ext y; simp only [image_univ, mem_range, mem_univ, iff_true]; exact ⟨y - c, by ring⟩
    rw [himg] at h
    exact h.le.trans hvar
  have hsupp' : ∀ ξ, m' ξ ≠ 0 → ξ ∈ Ioc (-1 / 2 : ℝ) (1 / 2) := by
    intro ξ hξ
    have := hsupp (ξ - -c) hξ
    rw [hc] at this
    constructor <;> linarith [this.1, this.2]
  have hker : (fun n : ℤ => ∫ ξ : ℝ, m' ξ * e ((n : ℝ) * ξ)) =
      fun n : ℤ => (∫ ξ : ℝ, m ξ * e ((n : ℝ) * ξ)) * e (-c * (n : ℝ)) := by
    funext n
    exact integral_shift_kernel m (-c) n
  have hpt : ∀ x : ℤ, supOp (fun n : ℤ => ∫ ξ : ℝ, m ξ * e ((n : ℝ) * ξ)) (⇑f) x =
      ⨆ lam ∈ Ico (0 : ℝ) 1, ‖dilSum m' 1 f x lam‖ₑ := by
    intro x
    rw [← supOp_mul_e (fun n : ℤ => ∫ ξ : ℝ, m ξ * e ((n : ℝ) * ξ)) (⇑f) (-c) x, ← hker]
    unfold supOp
    refine iSup_congr fun lam => iSup_congr fun _ => ?_
    rw [weightedModSum_eq_dilSum_one]
  have h := hC m' c₀ hc₀ hmeas hsupp' hTV' f (Ico 0 1) le_rfl
  have hfun : supOp (fun n : ℤ => ∫ ξ : ℝ, m ξ * e ((n : ℝ) * ξ)) (⇑f) =
      fun x : ℤ => ⨆ lam ∈ Ico (0 : ℝ) 1, ‖dilSum m' 1 f x lam‖ₑ := funext hpt
  rw [hfun]
  exact h

/-- **The maximal estimate for an integrable multiplier of bounded variation**: for `1 < p < ∞`
there is `C` such that for every integrable `m` with `V(m; ℝ) ≤ c₀`, `∫ |m| ≤ L`, and every
finitely supported `f`,
`‖sup_λ|∑_n f(x-n) g(n) e(λ n)|‖_{ℓ^p} ≤ C (c₀ + L) ‖f‖_{ℓ^p}`, `g(n) = ∫ m(ξ) e(nξ) dξ`
(the tiles of `P6a/KQTile.lean` and `sup_tile_kernel`). -/
theorem tile_sup_bound (hO : OplusVariationBound) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℝ → ℂ) (c₀ L : ℝ), 0 ≤ c₀ → 0 ≤ L → Integrable m →
      eVariationOn m univ ≤ ENNReal.ofReal c₀ → (∫ ξ, ‖m ξ‖) ≤ L → ∀ f : ℤ →₀ ℂ,
        eLpNorm (supOp (fun n : ℤ => ∫ ξ : ℝ, m ξ * e ((n : ℝ) * ξ)) (⇑f))
            (ENNReal.ofReal p) Measure.count ≤
          ENNReal.ofReal (C * (c₀ + L)) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨K₁, hK₁0, hVC⟩ := sup_tile_kernel hO hp
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
  -- the sum over tiles
  have hpt : ∀ x : ℤ, supOp g (⇑f) x ≤ ∑' t : ℤ, supOp (k t) (⇑f) x := by
    intro x
    refine supOp_le fun lam hlam => ?_
    have hs : HasSum (fun t => weightedModSum (k t) (⇑f) lam x) (weightedModSum g (⇑f) lam x) := by
      simp only [weightedModSum_eq_sum_of_finsupp]
      exact hasSum_sum fun n _ => by
        simpa [mul_assoc] using ((hkern n).mul_left (f (x - n) * 1)).mul_right (e (lam * n))
    rw [← hs.tsum_eq]
    exact enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun t =>
      enorm_weightedModSum_le_supOp _ _ hlam x)
  -- each tile
  have hVfin : ∀ t : ℤ, eVariationOn m (Icc (tileL t) (tileR t)) ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((eVariationOn.mono m (subset_univ _)).trans hTV)
  have htile : ∀ t : ℤ, eLpNorm (supOp (k t) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal (K₁ * (3 * (eVariationOn m (Icc (tileL t) (tileR t))).toReal +
        80 * ∫ η, hat t η * ‖m η‖)) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
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
    exact hVC (tile m t) (tileL t) hsupp _ hc (eVariationOn_tile_le hm t (hVfin t)) f
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
  calc eLpNorm (supOp g (⇑f)) (ENNReal.ofReal p) Measure.count
      ≤ eLpNorm (fun x => ∑' t : ℤ, supOp (k t) (⇑f) x) (ENNReal.ofReal p) Measure.count :=
        eLpNorm_count_mono_enn hpt _
    _ ≤ ∑' t : ℤ, eLpNorm (supOp (k t) (⇑f)) (ENNReal.ofReal p) Measure.count :=
        eLpNorm_count_tsum_le _ hp.le
    _ ≤ ∑' t : ℤ, ENNReal.ofReal (K₁ * (3 * (eVariationOn m (Icc (tileL t) (tileR t))).toReal +
          80 * ∫ η, hat t η * ‖m η‖)) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count :=
        ENNReal.tsum_le_tsum htile
    _ = (∑' t : ℤ, ENNReal.ofReal (K₁ * (3 * (eVariationOn m (Icc (tileL t)
          (tileR t))).toReal + 80 * ∫ η, hat t η * ‖m η‖))) *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by rw [ENNReal.tsum_mul_right]
    _ ≤ ENNReal.ofReal (80 * K₁ * (c₀ + L)) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
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

end PrimeCarleson.Proof.Paper

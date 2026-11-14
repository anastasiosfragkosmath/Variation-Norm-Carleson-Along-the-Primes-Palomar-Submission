module

public import PrimeCarleson.Proof.Lepingle.Prob.DoobWeak
public import PrimeCarleson.Proof.Lepingle.Prob.GarsiaNeveu

/-!
# Doob's maximal inequality in `L^p`

Source: Zorin-Kranich's notes `thm:Doob-Lp` (01-BDG.tex, L82–L90): Theorem 1.5 (L82-L108): for a
submartingale `f ≥ 0` and `p ∈ (1, ∞)`,
`‖Mf‖_p ≤ p' ‖f‖_p` with `p' = p/(p-1)` and `‖f‖_p = sup_n ‖f_n‖_p`.

* `lintegral_rpow_le_of_weak`: the layer-cake step: `∫ X^p ≤ p' ∫ Z X^{p-1}` if
  `t μ{X > t} ≤ ∫_{X>t} Z` for all `t > 0` (the paper's chain `∫ (Mf_n)^p = ∫ p λ^{p-1}
  μ(Mf_n > λ) dλ ≤ ∫ p λ^{p-2} ∫_{Mf_n>λ} f_n dλ = p' ∫ f_n (Mf_n)^{p-1}`);
* `doob_lp_aux`: the finite-time bound `‖Mf_n‖_p ≤ p' ‖f_n‖_p` (Hölder and cancellation), in `ℝ≥0∞`
  and `lintegral` form; only this finite-time form is proved here.

No hypothesis beyond `f` being a nonnegative submartingale on a finite measure space with
`f_n ∈ L^p`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal NNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Lepingle

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- From a weak-type bound to the `L^p` bound by the layer-cake formula: if
`t μ{X > t} ≤ ∫_{X > t} Z` for all `t > 0` and `p > 1`, then `∫ X^p ≤ p' ∫ Z X^{p-1}`. -/
theorem lintegral_rpow_le_of_weak [SFinite μ] {X : Ω → ℝ} (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) {Z : Ω → ℝ≥0∞} (hZ : Measurable Z)
    (h : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {ω | t < X ω} ≤ ∫⁻ ω in {ω | t < X ω}, Z ω ∂μ)
    {p : ℝ} (hp : 1 < p) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ p) ∂μ ≤
      ENNReal.ofReal (p / (p - 1)) * ∫⁻ ω, Z ω * ENNReal.ofReal (X ω ^ (p - 1)) ∂μ := by
  have hp1 : 0 < p - 1 := by linarith
  have hF : ∀ ω, ENNReal.ofReal (X ω ^ p) =
      ENNReal.ofReal p * ∫⁻ t in Ioo 0 (X ω), ENNReal.ofReal (t ^ (p - 1)) := by
    intro ω
    rw [lintegral_Ioo_rpow (by linarith) (hX0 ω), ← ENNReal.ofReal_mul (by linarith)]
    congr 1
    have e : p - 1 + 1 = p := by ring
    rw [e]
    field_simp
  have hH1 : Measurable (Function.uncurry fun (t : ℝ) (_ : Ω) =>
      ENNReal.ofReal (t ^ (p - 1))) :=
    (measurable_fst.pow_const _).ennreal_ofReal
  have hH2 : Measurable (Function.uncurry fun (t : ℝ) (ω : Ω) =>
      ENNReal.ofReal (t ^ (p - 2)) * Z ω) :=
    (measurable_fst.pow_const _).ennreal_ofReal.mul (hZ.comp measurable_snd)
  have hstep : ∀ t : ℝ, 0 < t → ∫⁻ ω in {ω | t < X ω}, ENNReal.ofReal (t ^ (p - 1)) ∂μ ≤
      ∫⁻ ω in {ω | t < X ω}, ENNReal.ofReal (t ^ (p - 2)) * Z ω ∂μ := by
    intro t ht
    have hsplit : ENNReal.ofReal (t ^ (p - 1)) =
        ENNReal.ofReal (t ^ (p - 2)) * ENNReal.ofReal t := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), show p - 1 = (p - 2) + 1 by ring,
        Real.rpow_add_one ht.ne']
    rw [setLIntegral_const, lintegral_const_mul _ hZ, hsplit, mul_assoc]
    exact mul_le_mul_right (h t ht) _
  calc ∫⁻ ω, ENNReal.ofReal (X ω ^ p) ∂μ
      = ENNReal.ofReal p * ∫⁻ ω, (∫⁻ t in Ioo 0 (X ω), ENNReal.ofReal (t ^ (p - 1))) ∂μ := by
        simp_rw [hF]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal p * ∫⁻ t in Ioi 0, (∫⁻ ω in {ω | t < X ω},
          ENNReal.ofReal (t ^ (p - 1)) ∂μ) := by
        rw [lintegral_lintegral_Ioo_swap hX hH1]
    _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi 0, (∫⁻ ω in {ω | t < X ω},
          ENNReal.ofReal (t ^ (p - 2)) * Z ω ∂μ) :=
        mul_le_mul_right (setLIntegral_mono' measurableSet_Ioi fun t ht => hstep t ht) _
    _ = ENNReal.ofReal p * ∫⁻ ω, (∫⁻ t in Ioo 0 (X ω), ENNReal.ofReal (t ^ (p - 2)) * Z ω) ∂μ := by
        rw [lintegral_lintegral_Ioo_swap hX hH2]
    _ = ENNReal.ofReal p * ∫⁻ ω, Z ω * ENNReal.ofReal (X ω ^ (p - 1) / (p - 1)) ∂μ := by
        congr 1
        refine lintegral_congr fun ω => ?_
        rw [lintegral_mul_const _ (by fun_prop : Measurable fun t : ℝ =>
          ENNReal.ofReal (t ^ (p - 2))),
          lintegral_Ioo_rpow (by linarith) (hX0 ω), mul_comm]
        have e : p - 2 + 1 = p - 1 := by ring
        rw [e]
    _ = ENNReal.ofReal (p / (p - 1)) * ∫⁻ ω, Z ω * ENNReal.ofReal (X ω ^ (p - 1)) ∂μ := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun ω => ?_
        calc ENNReal.ofReal p * (Z ω * ENNReal.ofReal (X ω ^ (p - 1) / (p - 1)))
            = Z ω * (ENNReal.ofReal p * ENNReal.ofReal (X ω ^ (p - 1) / (p - 1))) := by ring
          _ = Z ω * ENNReal.ofReal (p * (X ω ^ (p - 1) / (p - 1))) := by
              rw [ENNReal.ofReal_mul (by linarith)]
          _ = Z ω * (ENNReal.ofReal (p / (p - 1)) * ENNReal.ofReal (X ω ^ (p - 1))) := by
              congr 1
              rw [← ENNReal.ofReal_mul (by positivity)]
              congr 1
              ring
          _ = ENNReal.ofReal (p / (p - 1)) * (Z ω * ENNReal.ofReal (X ω ^ (p - 1))) := by ring

section Doob

variable {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}

theorem measurable_of_submartingale (hf : Submartingale f ℱ μ) (k : ℕ) : Measurable (f k) :=
  (hf.stronglyMeasurable k).measurable.mono (ℱ.le k) le_rfl

theorem maxUpTo_lt_top (n : ℕ) (ω : Ω) : maxUpTo f n ω < ∞ := by
  unfold maxUpTo
  rw [Finset.sup_lt_iff (by simp)]
  intro k _
  exact ENNReal.coe_lt_top

/-- `‖g‖_p^p = ∫ ‖g‖ₑ^p` in terms of `eLpNorm` (for `p > 0` real). -/
theorem lintegral_enorm_rpow_eq {E : Type*} [NormedAddCommGroup E] {g : Ω → E}
    (hg : AEStronglyMeasurable g μ) {p : ℝ} (hp : 0 < p) :
    ∫⁻ ω, ‖g ω‖ₑ ^ p ∂μ = eLpNorm g (ENNReal.ofReal p) μ ^ p := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top hg,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

/-- `L^p` norms of a nonnegative submartingale increase with time (the unproved remark of
Zorin-Kranich's notes, L29-L32, in the form needed for Doob). -/
theorem eLpNorm_le_of_submartingale [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hnn : ∀ n ω, 0 ≤ f n ω) {p : ℝ≥0∞} (hp : 1 ≤ p) {k n : ℕ} (hkn : k ≤ n) :
    eLpNorm (f k) p μ ≤ eLpNorm (f n) p μ := by
  refine (eLpNorm_mono_ae (g := μ[f n | ℱ k]) (hf.stronglyMeasurable k |>.mono (ℱ.le k)
    |>.aestronglyMeasurable) ?_).trans (eLpNorm_condExp_le_eLpNorm _ hp)
  filter_upwards [hf.ae_le_condExp hkn] with ω hω
  rw [Real.norm_of_nonneg (hnn k ω)]
  exact hω.trans (le_abs_self _)

/-- Finite-time Doob inequality: `‖Mf_n‖_p ≤ p' ‖f_n‖_p` when `f_n ∈ L^p`. -/
theorem doob_lp_aux [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ) (hnn : ∀ n ω, 0 ≤ f n ω)
    {p : ℝ} (hp : 1 < p) (n : ℕ) (hfin : ∫⁻ ω, ‖f n ω‖ₑ ^ p ∂μ ≠ ∞) :
    (∫⁻ ω, maxUpTo f n ω ^ p ∂μ) ^ (1 / p) ≤
      ENNReal.ofReal (p / (p - 1)) * (∫⁻ ω, ‖f n ω‖ₑ ^ p ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hmf := measurable_of_submartingale hf
  have hW : Measurable (maxUpTo f n) := measurable_maxUpTo fun k _ => hmf k
  have hWfin : ∀ ω, maxUpTo f n ω ≠ ∞ := fun ω => (maxUpTo_lt_top n ω).ne
  have hWX : ∀ ω, maxUpTo f n ω = ENNReal.ofReal ((maxUpTo f n ω).toReal) := fun ω =>
    (ENNReal.ofReal_toReal (hWfin ω)).symm
  have hXm : Measurable fun ω => (maxUpTo f n ω).toReal := hW.ennreal_toReal
  have hfn : ∀ ω, ‖f n ω‖ₑ = ENNReal.ofReal (f n ω) := fun ω =>
    enorm_eq_ofReal_of_nonneg (hnn n ω)
  have hZ : Measurable fun ω => ‖f n ω‖ₑ := (hmf n).enorm
  have hpow : ∀ ω, maxUpTo f n ω ^ p = ENNReal.ofReal ((maxUpTo f n ω).toReal ^ p) := fun ω => by
    conv_lhs => rw [hWX ω]
    exact ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp0.le
  have hpow' : ∀ ω, maxUpTo f n ω ^ (p - 1) =
      ENNReal.ofReal ((maxUpTo f n ω).toReal ^ (p - 1)) := fun ω => by
    conv_lhs => rw [hWX ω]
    exact ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by linarith)
  -- the weak-type hypothesis from Doob's weak inequality
  have hweak : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {ω | t < (maxUpTo f n ω).toReal} ≤
      ∫⁻ ω in {ω | t < (maxUpTo f n ω).toReal}, ‖f n ω‖ₑ ∂μ := by
    intro t ht
    have hset : {ω | t < (maxUpTo f n ω).toReal} = {ω | ENNReal.ofReal t < maxUpTo f n ω} := by
      ext ω
      simp only [mem_ofPred_eq]
      exact (ENNReal.ofReal_lt_iff_lt_toReal ht.le (hWfin ω)).symm
    rw [hset]
    simp_rw [hfn]
    exact doob_weak hf hnn ht n
  have haux := lintegral_rpow_le_of_weak hXm (fun ω => ENNReal.toReal_nonneg) hZ hweak hp
  simp_rw [← hpow, ← hpow'] at haux
  -- finiteness of `∫ (Mf_n)^p`
  have hk_fin : ∀ k ≤ n, ∫⁻ ω, ‖f k ω‖ₑ ^ p ∂μ ≠ ∞ := by
    intro k hk
    rw [lintegral_enorm_rpow_eq (hmf k).aestronglyMeasurable hp0]
    rw [lintegral_enorm_rpow_eq (hmf n).aestronglyMeasurable hp0] at hfin
    have h1 := eLpNorm_le_of_submartingale hf hnn (p := ENNReal.ofReal p)
      (by simpa using hp.le) hk
    have hfn_ne : eLpNorm (f n) (ENNReal.ofReal p) μ ≠ ∞ := by
      intro h
      apply hfin
      rw [h, ENNReal.top_rpow_of_pos hp0]
    exact ENNReal.rpow_ne_top_of_nonneg hp0.le (ne_top_of_le_ne_top hfn_ne h1)
  have hsum : ∀ ω, maxUpTo f n ω ^ p ≤ ∑ k ∈ range (n + 1), ‖f k ω‖ₑ ^ p := by
    intro ω
    obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup (range (n + 1)) (by simp)
      (fun k => ‖f k ω‖ₑ)
    have : maxUpTo f n ω = ‖f k ω‖ₑ := hkeq
    rw [this]
    exact Finset.single_le_sum (f := fun k => ‖f k ω‖ₑ ^ p) (fun _ _ => zero_le) hk
  have ha_top : ∫⁻ ω, maxUpTo f n ω ^ p ∂μ ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∑ k ∈ range (n + 1), ∫⁻ ω, ‖f k ω‖ₑ ^ p ∂μ) ?_ ?_
    · exact ENNReal.sum_ne_top.2 fun k hk =>
        hk_fin k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
    · calc ∫⁻ ω, maxUpTo f n ω ^ p ∂μ ≤ ∫⁻ ω, ∑ k ∈ range (n + 1), ‖f k ω‖ₑ ^ p ∂μ :=
          lintegral_mono hsum
        _ = ∑ k ∈ range (n + 1), ∫⁻ ω, ‖f k ω‖ₑ ^ p ∂μ :=
          lintegral_finsetSum _ fun k _ => ((hmf k).enorm).pow_const _
  exact lintegral_rpow_root_le_of_le hW hZ hp ha_top haux

end Doob

end PrimeCarleson.Proof.Lepingle

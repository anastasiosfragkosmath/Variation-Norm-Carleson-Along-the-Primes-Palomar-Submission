module

public import PrimeCarleson.Proof.Lepingle.Prob.LayerCake
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# The Garsia-Neveu lemma

Source: Zorin-Kranich's notes `lem:Garsia-Neveu` (01-BDG.tex, L373–L384): Lemma 1.11
(L373-L411): for positive random variables `W, Z` with
`E(1_{W>λ}(W-λ)) ≤ E(1_{W>λ} Z)` for every `λ > 0`, one has `‖W‖_p ≤ p ‖Z‖_p` for `p ≥ 1`.

* `garsia_neveu_aux`: the core inequality `E W^p ≤ p E(Z W^{p-1})` for `p > 1` and real `W`
  (the layer-cake identity `t^p = p(p-1) ∫_0^t (t-λ) λ^{p-2} dλ` and two Tonelli swaps);
* `garsia_neveu_bdd`: the cancellation step for bounded `W` (Hölder);
* `garsia_neveu`: the lemma for `ℝ≥0∞`-valued measurable `W, Z` on a finite measure space
  (truncation `min(W, Λ)` and monotone convergence; `p = 1` by `λ → 0`).

No integrability hypothesis is needed: `W` and `Z` take values in `ℝ≥0∞`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Lepingle

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

section Aux

/-- Core of the Garsia-Neveu lemma: for a nonnegative measurable real `X` and `p > 1`,
`∫ X^p ≤ p ∫ Z X^{p-1}` provided `∫_{X>t} (X - t) ≤ ∫_{X>t} Z` for all `t > 0`. -/
theorem garsia_neveu_aux [SFinite μ] {X : Ω → ℝ} (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    {Z : Ω → ℝ≥0∞} (hZ : Measurable Z)
    (h : ∀ t : ℝ, 0 < t →
      ∫⁻ ω in {ω | t < X ω}, ENNReal.ofReal (X ω - t) ∂μ ≤ ∫⁻ ω in {ω | t < X ω}, Z ω ∂μ)
    {p : ℝ} (hp : 1 < p) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ p) ∂μ ≤
      ENNReal.ofReal p * ∫⁻ ω, Z ω * ENNReal.ofReal (X ω ^ (p - 1)) ∂μ := by
  have hpp : 0 < p * (p - 1) := by nlinarith
  have hF1 : ∀ ω, ENNReal.ofReal (X ω ^ p) = ENNReal.ofReal (p * (p - 1)) *
      ∫⁻ t in Ioo 0 (X ω), ENNReal.ofReal ((X ω - t) * t ^ (p - 2)) := by
    intro ω
    rw [lintegral_Ioo_sub_mul_rpow hp (hX0 ω), ← ENNReal.ofReal_mul hpp.le]
    congr 1
    field_simp
  have hH1 : Measurable (Function.uncurry fun (t : ℝ) (ω : Ω) =>
      ENNReal.ofReal ((X ω - t) * t ^ (p - 2))) := by
    have h1 : Measurable fun q : ℝ × Ω => (X q.2 - q.1) * q.1 ^ (p - 2) := by
      have : Measurable fun q : ℝ × Ω => X q.2 - q.1 := (hX.comp measurable_snd).sub measurable_fst
      exact this.mul (measurable_fst.pow_const _)
    exact h1.ennreal_ofReal
  have hH2 : Measurable (Function.uncurry fun (t : ℝ) (ω : Ω) =>
      ENNReal.ofReal (t ^ (p - 2)) * Z ω) := by
    have h1 : Measurable fun q : ℝ × Ω => q.1 ^ (p - 2) := measurable_fst.pow_const _
    exact h1.ennreal_ofReal.mul (hZ.comp measurable_snd)
  have hstep : ∀ t : ℝ, 0 < t →
      ∫⁻ ω in {ω | t < X ω}, ENNReal.ofReal ((X ω - t) * t ^ (p - 2)) ∂μ ≤
        ∫⁻ ω in {ω | t < X ω}, ENNReal.ofReal (t ^ (p - 2)) * Z ω ∂μ := by
    intro t ht
    calc ∫⁻ ω in {ω | t < X ω}, ENNReal.ofReal ((X ω - t) * t ^ (p - 2)) ∂μ
        = ∫⁻ ω in {ω | t < X ω}, ENNReal.ofReal (t ^ (p - 2)) * ENNReal.ofReal (X ω - t) ∂μ := by
          refine lintegral_congr fun ω => ?_
          rw [mul_comm, ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
      _ = ENNReal.ofReal (t ^ (p - 2)) * ∫⁻ ω in {ω | t < X ω}, ENNReal.ofReal (X ω - t) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (t ^ (p - 2)) * ∫⁻ ω in {ω | t < X ω}, Z ω ∂μ :=
          mul_le_mul_right (h t ht) _
      _ = ∫⁻ ω in {ω | t < X ω}, ENNReal.ofReal (t ^ (p - 2)) * Z ω ∂μ :=
          (lintegral_const_mul _ hZ).symm
  calc ∫⁻ ω, ENNReal.ofReal (X ω ^ p) ∂μ
      = ENNReal.ofReal (p * (p - 1)) * ∫⁻ ω, (∫⁻ t in Ioo 0 (X ω),
          ENNReal.ofReal ((X ω - t) * t ^ (p - 2))) ∂μ := by
        simp_rw [hF1]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (p * (p - 1)) * ∫⁻ t in Ioi 0, (∫⁻ ω in {ω | t < X ω},
          ENNReal.ofReal ((X ω - t) * t ^ (p - 2)) ∂μ) := by
        rw [lintegral_lintegral_Ioo_swap hX hH1]
    _ ≤ ENNReal.ofReal (p * (p - 1)) * ∫⁻ t in Ioi 0, (∫⁻ ω in {ω | t < X ω},
          ENNReal.ofReal (t ^ (p - 2)) * Z ω ∂μ) := by
        exact mul_le_mul_right (setLIntegral_mono' measurableSet_Ioi fun t ht => hstep t ht) _
    _ = ENNReal.ofReal (p * (p - 1)) * ∫⁻ ω, (∫⁻ t in Ioo 0 (X ω),
          ENNReal.ofReal (t ^ (p - 2)) * Z ω) ∂μ := by
        rw [lintegral_lintegral_Ioo_swap hX hH2]
    _ = ENNReal.ofReal (p * (p - 1)) * ∫⁻ ω, Z ω * ENNReal.ofReal (X ω ^ (p - 1) / (p - 1)) ∂μ := by
        congr 1
        refine lintegral_congr fun ω => ?_
        rw [lintegral_mul_const _ (by fun_prop : Measurable fun t : ℝ =>
          ENNReal.ofReal (t ^ (p - 2))),
          lintegral_Ioo_rpow (by linarith) (hX0 ω), mul_comm]
        have e : p - 2 + 1 = p - 1 := by ring
        rw [e]
    _ = ENNReal.ofReal p * ∫⁻ ω, Z ω * ENNReal.ofReal (X ω ^ (p - 1)) ∂μ := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun ω => ?_
        have hp1 : 0 < p - 1 := by linarith
        calc ENNReal.ofReal (p * (p - 1)) * (Z ω * ENNReal.ofReal (X ω ^ (p - 1) / (p - 1)))
            = Z ω * (ENNReal.ofReal (p * (p - 1)) *
                ENNReal.ofReal (X ω ^ (p - 1) / (p - 1))) := by ring
          _ = Z ω * ENNReal.ofReal (p * (p - 1) * (X ω ^ (p - 1) / (p - 1))) := by
              rw [ENNReal.ofReal_mul hpp.le]
          _ = Z ω * (ENNReal.ofReal p * ENNReal.ofReal (X ω ^ (p - 1))) := by
              congr 1
              rw [← ENNReal.ofReal_mul (by linarith)]
              congr 1
              field_simp
          _ = ENNReal.ofReal p * (Z ω * ENNReal.ofReal (X ω ^ (p - 1))) := by ring

end Aux

section Bounded

/-- Conversion of the Garsia-Neveu hypothesis from `ℝ≥0∞`-valued finite `W` to the real
function `X = W.toReal`. -/
theorem garsia_neveu_hyp_real {W Z : Ω → ℝ≥0∞} (hWfin : ∀ ω, W ω ≠ ∞)
    (h : ∀ t : ℝ, 0 < t → ∫⁻ ω in {ω | ENNReal.ofReal t < W ω}, (W ω - ENNReal.ofReal t) ∂μ ≤
      ∫⁻ ω in {ω | ENNReal.ofReal t < W ω}, Z ω ∂μ) (t : ℝ) (ht : 0 < t) :
    ∫⁻ ω in {ω | t < (W ω).toReal}, ENNReal.ofReal ((W ω).toReal - t) ∂μ ≤
      ∫⁻ ω in {ω | t < (W ω).toReal}, Z ω ∂μ := by
  have hset : {ω | t < (W ω).toReal} = {ω | ENNReal.ofReal t < W ω} := by
    ext ω
    simp only [mem_ofPred_eq]
    exact (ENNReal.ofReal_lt_iff_lt_toReal ht.le (hWfin ω)).symm
  rw [hset]
  have : ∀ ω, ENNReal.ofReal ((W ω).toReal - t) = W ω - ENNReal.ofReal t := by
    intro ω
    rw [ENNReal.ofReal_sub _ ht.le, ENNReal.ofReal_toReal (hWfin ω)]
  simp_rw [this]
  exact h t ht

/-- Hölder and cancellation: if `∫ W^p < ∞` and `∫ W^p ≤ c ∫ Z W^{p-1}` for `p > 1`, then
`(∫ W^p)^{1/p} ≤ c (∫ Z^p)^{1/p}` (the last step of the proofs of Doob's `L^p` inequality and of
the Garsia-Neveu lemma, Zorin-Kranich's notes, L102-L108 and L405-L410). -/
theorem lintegral_rpow_root_le_of_le {W Z : Ω → ℝ≥0∞} (hW : Measurable W) (hZ : Measurable Z)
    {p : ℝ} (hp : 1 < p) {c : ℝ≥0∞} (ha_top : ∫⁻ ω, W ω ^ p ∂μ ≠ ∞)
    (hmain : ∫⁻ ω, W ω ^ p ∂μ ≤ c * ∫⁻ ω, Z ω * W ω ^ (p - 1) ∂μ) :
    (∫⁻ ω, W ω ^ p ∂μ) ^ (1 / p) ≤ c * (∫⁻ ω, Z ω ^ p ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hq : p.HolderConjugate (Real.conjExponent p) := .conjExponent hp
  set q := Real.conjExponent p with hqdef
  have hqpos : 0 < q := hq.symm.pos
  have hpq : 1 / p + 1 / q = 1 := by
    have := hq.inv_add_inv_eq_one
    simpa [one_div] using this
  have hpq' : (p - 1) * q = p := by
    rw [hqdef, Real.conjExponent]
    field_simp
  set a := ∫⁻ ω, W ω ^ p ∂μ with ha
  have hHolder : ∫⁻ ω, Z ω * W ω ^ (p - 1) ∂μ ≤ (∫⁻ ω, Z ω ^ p ∂μ) ^ (1 / p) * a ^ (1 / q) := by
    have := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hq (f := Z) (g := fun ω => W ω ^ (p - 1))
      hZ.aemeasurable (hW.pow_const _).aemeasurable
    refine this.trans (le_of_eq ?_)
    congr 2
    refine lintegral_congr fun ω => ?_
    rw [← ENNReal.rpow_mul, hpq']
  have hmain' : a ≤ c * ((∫⁻ ω, Z ω ^ p ∂μ) ^ (1 / p) * a ^ (1 / q)) :=
    hmain.trans (mul_le_mul_right hHolder _)
  rcases eq_or_ne a 0 with ha0 | ha0
  · rw [ha0, ENNReal.zero_rpow_of_pos (by positivity : 0 < 1 / p)]
    exact zero_le
  · have hc0 : a ^ (1 / q) ≠ 0 := by
      intro h0
      rw [ENNReal.rpow_eq_zero_iff] at h0
      rcases h0 with ⟨h0, _⟩ | ⟨_, h0⟩
      · exact ha0 h0
      · have : 0 < 1 / q := by positivity
        linarith
    have hctop : a ^ (1 / q) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) ha_top
    have hsplit : a = a ^ (1 / p) * a ^ (1 / q) := by
      rw [← ENNReal.rpow_add _ _ ha0 ha_top, hpq, ENNReal.rpow_one]
    have h2 : a ^ (1 / p) * a ^ (1 / q) ≤ (c * (∫⁻ ω, Z ω ^ p ∂μ) ^ (1 / p)) * a ^ (1 / q) := by
      calc a ^ (1 / p) * a ^ (1 / q) = a := hsplit.symm
        _ ≤ _ := hmain'
        _ = _ := by ring
    exact (ENNReal.mul_le_mul_iff_left hc0 hctop).1 h2

/-- Garsia-Neveu for bounded `W` and `p > 1`. -/
theorem garsia_neveu_bdd [IsFiniteMeasure μ] {W Z : Ω → ℝ≥0∞} (hW : Measurable W)
    (hZ : Measurable Z) {Λ : ℝ} (hΛ : ∀ ω, W ω ≤ ENNReal.ofReal Λ)
    (h : ∀ t : ℝ, 0 < t → ∫⁻ ω in {ω | ENNReal.ofReal t < W ω}, (W ω - ENNReal.ofReal t) ∂μ ≤
      ∫⁻ ω in {ω | ENNReal.ofReal t < W ω}, Z ω ∂μ)
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ ω, W ω ^ p ∂μ) ^ (1 / p) ≤ ENNReal.ofReal p * (∫⁻ ω, Z ω ^ p ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hWfin : ∀ ω, W ω ≠ ∞ := fun ω => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hΛ ω)
  have hXm : Measurable fun ω => (W ω).toReal := hW.ennreal_toReal
  have hWX : ∀ ω, W ω = ENNReal.ofReal ((W ω).toReal) := fun ω =>
    (ENNReal.ofReal_toReal (hWfin ω)).symm
  have hpow : ∀ ω, W ω ^ p = ENNReal.ofReal ((W ω).toReal ^ p) := fun ω => by
    conv_lhs => rw [hWX ω]
    exact ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp0.le
  have hpow' : ∀ ω, W ω ^ (p - 1) = ENNReal.ofReal ((W ω).toReal ^ (p - 1)) := fun ω => by
    conv_lhs => rw [hWX ω]
    exact ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by linarith)
  have haux := garsia_neveu_aux hXm (fun ω => ENNReal.toReal_nonneg) hZ
    (garsia_neveu_hyp_real hWfin h) hp
  simp_rw [← hpow, ← hpow'] at haux
  have ha_top : ∫⁻ ω, W ω ^ p ∂μ ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _ : Ω, ENNReal.ofReal Λ ^ p ∂μ) ?_ ?_
    · rw [lintegral_const]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)
        (measure_ne_top _ _)
    · exact lintegral_mono fun ω => ENNReal.rpow_le_rpow (hΛ ω) hp0.le
  exact lintegral_rpow_root_le_of_le hW hZ hp ha_top haux

end Bounded

section Final

/-- Garsia-Neveu for `p = 1`: `E W ≤ E Z`, by letting `λ → 0`. -/
theorem lintegral_le_of_garsia_neveu_hyp {W Z : Ω → ℝ≥0∞} (hW : Measurable W)
    (h : ∀ t : ℝ, 0 < t → ∫⁻ ω in {ω | ENNReal.ofReal t < W ω}, (W ω - ENNReal.ofReal t) ∂μ ≤
      ∫⁻ ω in {ω | ENNReal.ofReal t < W ω}, Z ω ∂μ) :
    ∫⁻ ω, W ω ∂μ ≤ ∫⁻ ω, Z ω ∂μ := by
  set t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with ht
  have htpos : ∀ n, 0 < t n := fun n => by positivity
  have hlim : Filter.Tendsto (fun n : ℕ => ∫⁻ ω, (W ω - ENNReal.ofReal (t n)) ∂μ)
      Filter.atTop (nhds (∫⁻ ω, W ω ∂μ)) := by
    have := lintegral_tendsto_of_tendsto_of_monotone
      (f := fun n ω => W ω - ENNReal.ofReal (t n)) (F := W) (μ := μ)
      (fun n => (hW.sub measurable_const).aemeasurable)
      (Filter.Eventually.of_forall fun ω n m hnm =>
        tsub_le_tsub_left (ENNReal.ofReal_le_ofReal (by
          simp only [ht]
          gcongr)) _)
      (Filter.Eventually.of_forall fun ω => by
        have h0 : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (t n)) Filter.atTop
            (nhds (ENNReal.ofReal 0)) :=
          ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
        have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := W ω)) h0
          (Or.inr (by simp))
        simpa using this)
    exact this
  refine le_of_tendsto' hlim fun n => ?_
  have hset : ∫⁻ ω, (W ω - ENNReal.ofReal (t n)) ∂μ =
      ∫⁻ ω in {ω | ENNReal.ofReal (t n) < W ω}, (W ω - ENNReal.ofReal (t n)) ∂μ := by
    rw [← lintegral_indicator (measurableSet_lt measurable_const hW)]
    refine lintegral_congr fun ω => ?_
    by_cases hω : ENNReal.ofReal (t n) < W ω
    · simp [hω]
    · simp [Set.indicator, hω, tsub_eq_zero_of_le (not_lt.1 hω)]
  rw [hset]
  exact (h (t n) (htpos n)).trans (setLIntegral_le_lintegral _ _)

/-- **Garsia-Neveu lemma** (Zorin-Kranich's notes, Lemma 1.11): if `W, Z ≥ 0` satisfy
`E(1_{W>λ}(W-λ)) ≤ E(1_{W>λ} Z)` for all `λ > 0`, then `‖W‖_p ≤ p ‖Z‖_p` for `p ≥ 1`
(constant exactly `p`). -/
theorem garsia_neveu [IsFiniteMeasure μ] {W Z : Ω → ℝ≥0∞} (hW : Measurable W)
    (hZ : Measurable Z)
    (h : ∀ t : ℝ, 0 < t → ∫⁻ ω in {ω | ENNReal.ofReal t < W ω}, (W ω - ENNReal.ofReal t) ∂μ ≤
      ∫⁻ ω in {ω | ENNReal.ofReal t < W ω}, Z ω ∂μ)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ ω, W ω ^ p ∂μ) ^ (1 / p) ≤ ENNReal.ofReal p * (∫⁻ ω, Z ω ^ p ∂μ) ^ (1 / p) := by
  rcases eq_or_lt_of_le hp with rfl | hp1
  · simpa using lintegral_le_of_garsia_neveu_hyp hW h
  have hp0 : 0 < p := by linarith
  set C := ENNReal.ofReal p * (∫⁻ ω, Z ω ^ p ∂μ) ^ (1 / p) with hC
  have hn : ∀ n : ℕ, ∫⁻ ω, (min (W ω) n) ^ p ∂μ ≤ C ^ p := by
    intro n
    have hWn : Measurable fun ω => min (W ω) n := hW.min measurable_const
    have hΛ : ∀ ω, min (W ω) n ≤ ENNReal.ofReal (n : ℝ) := fun ω =>
      (min_le_right _ _).trans (by simp)
    have hyp : ∀ t : ℝ, 0 < t →
        ∫⁻ ω in {ω | ENNReal.ofReal t < min (W ω) n}, (min (W ω) n - ENNReal.ofReal t) ∂μ ≤
        ∫⁻ ω in {ω | ENNReal.ofReal t < min (W ω) n}, Z ω ∂μ := by
      intro t ht
      by_cases htn : ENNReal.ofReal t < n
      · have hset : {ω | ENNReal.ofReal t < min (W ω) n} = {ω | ENNReal.ofReal t < W ω} := by
          ext ω
          simp only [mem_ofPred_eq, lt_min_iff]
          exact ⟨fun h => h.1, fun h => ⟨h, htn⟩⟩
        rw [hset]
        exact (setLIntegral_mono' (hW (measurableSet_Ioi (a := ENNReal.ofReal t)) |>.congr rfl)
          fun ω _ => tsub_le_tsub_right (min_le_left _ _) _).trans (h t ht)
      · have hset : {ω | ENNReal.ofReal t < min (W ω) n} = ∅ := by
          ext ω
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
          exact (min_le_right _ _).trans (not_lt.1 htn)
        rw [hset]
        simp
    have := garsia_neveu_bdd (W := fun ω => min (W ω) n) hWn hZ hΛ hyp hp1
    have h2 := ENNReal.rpow_le_rpow this hp0.le
    have h3 : ((∫⁻ ω, (min (W ω) n) ^ p ∂μ) ^ (1 / p)) ^ p = ∫⁻ ω, (min (W ω) n) ^ p ∂μ := by
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
    rw [← h3]
    exact h2
  have hsup : ∫⁻ ω, W ω ^ p ∂μ = ⨆ n : ℕ, ∫⁻ ω, (min (W ω) n) ^ p ∂μ := by
    rw [← lintegral_iSup]
    · refine lintegral_congr fun ω => ?_
      have hmin : ⨆ n : ℕ, min (W ω) (n : ℝ≥0∞) = W ω := by
        refine le_antisymm (iSup_le fun n => min_le_left _ _) ?_
        by_cases hw : W ω = ∞
        · rw [hw]
          have : ∀ n : ℕ, min (∞ : ℝ≥0∞) n = n := fun n => min_eq_right le_top
          simp only [this]
          exact le_of_eq ENNReal.iSup_natCast.symm
        · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hw
          exact le_iSup_of_le n (le_min le_rfl hn.le)
      calc W ω ^ p = (⨆ n : ℕ, min (W ω) (n : ℝ≥0∞)) ^ p := by rw [hmin]
        _ = ⨆ n : ℕ, (min (W ω) (n : ℝ≥0∞)) ^ p :=
          Monotone.map_iSup_of_continuousAt (f := fun x : ℝ≥0∞ => x ^ p)
            (g := fun n : ℕ => min (W ω) (n : ℝ≥0∞))
            ENNReal.continuous_rpow_const.continuousAt
            (fun a b hab => ENNReal.rpow_le_rpow hab hp0.le) (ENNReal.zero_rpow_of_pos hp0)
    · exact fun n => (hW.min measurable_const).pow_const _
    · intro n m hnm ω
      exact ENNReal.rpow_le_rpow (min_le_min le_rfl (by exact_mod_cast hnm)) hp0.le
  have : (∫⁻ ω, W ω ^ p ∂μ) ≤ C ^ p := by
    rw [hsup]
    exact iSup_le hn
  calc (∫⁻ ω, W ω ^ p ∂μ) ^ (1 / p) ≤ (C ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow this (by positivity)
    _ = C := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

end Final

end PrimeCarleson.Proof.Lepingle

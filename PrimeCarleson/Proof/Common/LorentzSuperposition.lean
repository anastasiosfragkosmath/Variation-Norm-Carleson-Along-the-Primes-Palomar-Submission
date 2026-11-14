module

public import Carleson.ToMathlib.LorentzType
public import PrimeCarleson.Proof.Common.MarcinkiewiczRestricted

/-!
# Restricted weak type implies `L^{p,1} → L^{p,∞}`

Source: [O+] `csrhobound`, L1131–L1137: "by the usual characterization of `L^{p,1}` as
superpositions of functions bounded by characteristic functions it suffices to show" the bound for
`|f| ≤ 1_F`.  It is used for the estimate of `S^ρ` for 1- and 2-indices (`csrhobound`), where the
level-set estimate supplies `|{|S^ρ f| > λ}| ≤ C^p λ^{-p} |F|`.

The vendored Lean Carleson project proves the superposition argument as
`HasRestrictedWeakType.hasLorentzType` (`Carleson.ToMathlib.LorentzType`), for the restricted
weak-type notion `‖T 1_F‖_{L¹(G)} ≤ c μ(F)^{1/p} ν(G)^{1/p'}`, under measurability, subadditivity,
homogeneity and a weak-continuity hypothesis. This file is the bridge to the form of the paper:

* `lintegral_enorm_restrict_le`: the duality estimate `∫_G ‖g‖ₑ ≤ (p/(p-1)) X ν(G)^{1-1/p}` for
  `‖g‖_{L^{p,∞}} ≤ X`, `p > 1`, which turns the weak `L^p` bound on `T 1_F` into the hypothesis
  `HasRestrictedWeakType` (`hasRestrictedWeakType_of_wnorm`);
* `wnorm_le_of_distribution_le`: the level-set bound `d_g(t) ≤ (X/t)^p` of the paper gives
  `‖g‖_{L^{p,∞}} ≤ X`;
* `eLpNorm_le_limsup_of_ae_tendsto`: the weak-continuity hypothesis from a.e. convergence
  `T (f_n) → T f` under monotone pointwise approximation, by Fatou;
* `wnorm_le_of_restricted_weak`: the abstract form, with conclusion
  `‖T f‖_{L^{p,∞}} ≤ (4/(p-1)) M ‖f‖_{L^{p,1}}` (the constant of the vendored theorem
  `4 c / p` with `c = p' M`);
* `finSumOp`, `wnorm_finSumOp_le`: the operators the [O+] argument applies it to, finite sums
  `f ↦ ∑_{j ∈ J} (∫ f k_j) ψ_j` of bounded functionals (`k_j ∈ L^{p'}`) times fixed measurable
  functions, for which all the hypotheses except the restricted weak-type bound
  `‖T 1_F‖_{L^{p,∞}} ≤ M μ(F)^{1/p}` hold automatically (Hölder and dominated convergence).

Only the indicators `1_F` are used in the restricted weak-type hypothesis (the paper states it for
all `|g| ≤ 1_F`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Common

section Duality

variable {α' ε' : Type*} [MeasurableSpace α'] {ν : Measure α'} [TopologicalSpace ε']
  [ESeminormedAddMonoid ε']

/-- **Duality estimate for weak `L^p`** (`p > 1`): if `‖g‖_{L^{p,∞}} ≤ X` then for every set `G`,
`∫_G ‖g‖ₑ ≤ (p/(p-1)) X ν(G)^{1-1/p}`. -/
theorem lintegral_enorm_restrict_le {g : α' → ε'} (hg : AEStronglyMeasurable g ν) {p : ℝ}
    (hp : 1 < p) {X : ℝ≥0} (hX : 0 < X) (h : wnorm g (ENNReal.ofReal p) ν ≤ X) (G : Set α') :
    ∫⁻ x in G, ‖g x‖ₑ ∂ν ≤ ENNReal.ofReal (p / (p - 1)) * X * ν G ^ (1 - 1 / p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hexp : 0 < 1 - 1 / p := by
    rw [sub_pos, div_lt_one hp0]; exact hp
  rcases eq_or_ne (ν G) 0 with hm0 | hm0
  · rw [Measure.restrict_eq_zero.2 hm0, lintegral_zero_measure]
    exact zero_le
  rcases eq_or_ne (ν G) ⊤ with hmt | hmt
  · rw [hmt, ENNReal.top_rpow_of_pos hexp, ENNReal.mul_top]
    · exact le_top
    · refine mul_ne_zero ?_ (by simpa using hX.ne')
      exact (ENNReal.ofReal_pos.2 (div_pos hp0 hp1)).ne'
  have hmrpos : 0 < (ν G).toReal := ENNReal.toReal_pos hm0 hmt
  set mr : ℝ := (ν G).toReal with hmr
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  set t₀r : ℝ := X * mr ^ (-(1 / p)) with ht₀r
  have ht₀pos : 0 < t₀r := mul_pos hXr (Real.rpow_pos_of_pos hmrpos _)
  set t₀ : ℝ≥0 := t₀r.toNNReal with ht₀
  have ht₀pos' : 0 < t₀ := Real.toNNReal_pos.2 ht₀pos
  have ht₀coe : (t₀ : ℝ) = t₀r := Real.coe_toNNReal _ ht₀pos.le
  have hXE : (X : ℝ≥0∞) = ENNReal.ofReal X := (ENNReal.ofReal_coe_nnreal).symm
  -- the value of the plateau
  have hplateau : (X : ℝ≥0∞) ^ p * ((t₀ : ℝ≥0∞)⁻¹) ^ p = ν G := by
    have e1 : (t₀ : ℝ≥0∞) = ENNReal.ofReal t₀r := by rw [← ht₀coe, ENNReal.ofReal_coe_nnreal]
    rw [e1, hXE, ← ENNReal.ofReal_inv_of_pos ht₀pos,
      ENNReal.ofReal_rpow_of_nonneg hXr.le hp0.le,
      ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 ht₀pos.le) hp0.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hXr.le _)]
    have e2 : X ^ p * (t₀r⁻¹) ^ p = mr := by
      rw [← Real.mul_rpow hXr.le (inv_nonneg.2 ht₀pos.le), ht₀r, Real.rpow_neg hmrpos.le]
      have : (X : ℝ) * (X * (mr ^ (1 / p))⁻¹)⁻¹ = mr ^ (1 / p) := by
        have : mr ^ (1 / p) ≠ 0 := (Real.rpow_pos_of_pos hmrpos _).ne'
        field_simp
      rw [this, ← Real.rpow_mul hmrpos.le, one_div_mul_cancel hp0.ne', Real.rpow_one]
    rw [e2, hmr, ENNReal.ofReal_toReal hmt]
  -- pointwise bound for the distribution function of `‖g‖ₑ` on `G`
  have hd : ∀ t : ℝ≥0, 0 < t → distribution (fun x => ‖g x‖ₑ) t (ν.restrict G) ≤
      (X : ℝ≥0∞) ^ p * ((max (t₀ : ℝ≥0∞) t)⁻¹) ^ p := by
    intro t ht
    have hset : {x | (t : ℝ≥0∞) < ‖(fun x => ‖g x‖ₑ) x‖ₑ} = {x | (t : ℝ≥0∞) < ‖g x‖ₑ} := by
      ext x; simp
    have hd1 : distribution (fun x => ‖g x‖ₑ) t (ν.restrict G) ≤ ν G :=
      (measure_mono (subset_univ _)).trans (by rw [Measure.restrict_apply_univ])
    have hd2 : distribution (fun x => ‖g x‖ₑ) t (ν.restrict G) ≤ distribution g t ν := by
      unfold distribution
      rw [hset]
      exact Measure.le_iff'.1 Measure.restrict_le_self _
    rcases le_or_gt t t₀ with hle | hlt
    · have : max (t₀ : ℝ≥0∞) t = t₀ := max_eq_left (by exact_mod_cast hle)
      rw [this, hplateau]
      exact hd1
    · have : max (t₀ : ℝ≥0∞) t = t := max_eq_right (by exact_mod_cast hlt.le)
      rw [this]
      refine hd2.trans ((distribution_le_of_wnorm_le hg hp0 h ht).trans ?_)
      rw [ENNReal.div_rpow_of_nonneg _ _ hp0.le, div_eq_mul_inv, ENNReal.inv_rpow]
  -- integrate
  have hint : ∫⁻ x in G, ‖g x‖ₑ ∂ν ≤ (X : ℝ≥0∞) ^ p *
      ENNReal.ofReal (t₀r ^ (1 - p) * (p / (p - 1))) := by
    have h1 := lintegral_eq_lintegral_distribution (ν.restrict G) (f := fun x => ‖g x‖ₑ)
      hg.enorm.restrict
    rw [h1, lintegral_ennreal_eq_lintegral_of_nnreal (f := fun t =>
      distribution (fun x => ‖g x‖ₑ) t (ν.restrict G))]
    calc ∫⁻ t : ℝ≥0, distribution (fun x => ‖g x‖ₑ) t (ν.restrict G)
        ≤ ∫⁻ t : ℝ≥0, (X : ℝ≥0∞) ^ p * ((max (t₀ : ℝ≥0∞) t)⁻¹) ^ p := by
          rw [lintegral_nnreal_eq_lintegral_toNNReal_Ioi,
            lintegral_nnreal_eq_lintegral_toNNReal_Ioi
              (fun t => (X : ℝ≥0∞) ^ p * ((max (t₀ : ℝ≥0∞) t)⁻¹) ^ p)]
          exact setLIntegral_mono' measurableSet_Ioi fun x hx => hd _ (Real.toNNReal_pos.2 hx)
      _ = (X : ℝ≥0∞) ^ p * ∫⁻ t : ℝ≥0, ((max (t₀ : ℝ≥0∞) t)⁻¹) ^ p := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le (by simp))]
      _ = _ := by
          rw [lintegral_nnreal_max_inv_rpow hp ht₀pos', ht₀coe]
  refine hint.trans (le_of_eq ?_)
  -- the real identity
  have e3 : (X : ℝ) ^ p * (t₀r ^ (1 - p) * (p / (p - 1))) =
      p / (p - 1) * X * mr ^ (1 - 1 / p) := by
    have h2 : t₀r ^ (1 - p) = (X : ℝ) ^ (1 - p) * mr ^ (1 - 1 / p) := by
      rw [ht₀r, Real.mul_rpow hXr.le (Real.rpow_nonneg hmrpos.le _), ← Real.rpow_mul hmrpos.le]
      congr 2
      field_simp
      ring
    have h3 : (X : ℝ) ^ p * (X : ℝ) ^ (1 - p) = X := by
      rw [← Real.rpow_add hXr]; simp
    calc (X : ℝ) ^ p * (t₀r ^ (1 - p) * (p / (p - 1)))
        = ((X : ℝ) ^ p * (X : ℝ) ^ (1 - p)) * mr ^ (1 - 1 / p) * (p / (p - 1)) := by rw [h2]; ring
      _ = _ := by rw [h3]; ring
  rw [hXE, ENNReal.ofReal_rpow_of_nonneg hXr.le hp0.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hXr.le _), e3]
  have e4 : ν G ^ (1 - 1 / p) = ENNReal.ofReal (mr ^ (1 - 1 / p)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hmrpos.le hexp.le, hmr, ENNReal.ofReal_toReal hmt]
  rw [e4, ← ENNReal.ofReal_mul (div_pos hp0 hp1).le,
    ← ENNReal.ofReal_mul (mul_pos (div_pos hp0 hp1) hXr).le]

/-- Converse of `distribution_le_of_wnorm_le`: a level-set bound `d_g(t) ≤ (X / t)^p` for all
`t > 0` (the form of L1131-L1137 of `osttw0710.tex`: `|{|S^ρ f| > λ}| ≤ C^p λ^{-p} |F|`, with
`X = C |F|^{1/p}`) gives `‖g‖_{L^{p,∞}} ≤ X`. -/
theorem wnorm_le_of_distribution_le {g : α' → ε'} (hg : AEStronglyMeasurable g ν) {p : ℝ}
    (hp : 0 < p) {X : ℝ≥0∞} (h : ∀ t : ℝ≥0, 0 < t → distribution g t ν ≤ (X / t) ^ p) :
    wnorm g (ENNReal.ofReal p) ν ≤ X := by
  rw [wnorm_eq_iSup_mul_distribution_rpow hg (ENNReal.ofReal_pos.2 hp).ne'
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  refine iSup_le fun t => ?_
  rcases eq_zero_or_pos t with rfl | ht
  · simp
  calc (t : ℝ≥0∞) * distribution g t ν ^ p⁻¹ ≤ (t : ℝ≥0∞) * ((X / t) ^ p) ^ p⁻¹ := by
        gcongr
        exact h t ht
    _ = (t : ℝ≥0∞) * (X / t) := by rw [ENNReal.rpow_rpow_inv hp.ne']
    _ ≤ X := ENNReal.mul_div_le

end Duality

section Abstract

variable {α α' 𝕂 ε' : Type*} [MeasurableSpace α] [MeasurableSpace α'] {μ : Measure α}
  {ν : Measure α'} [RCLike 𝕂] [TopologicalSpace ε'] [ENormedAddCommMonoid ε']

/-- The indicator of a set of finite measure is in `L^{p,1}`. -/
theorem memLorentz_indicator_one {p : ℝ} (hp : 0 < p) {F : Set α} (hF : MeasurableSet F)
    (hFt : μ F < ⊤) :
    MemLorentz (F.indicator (fun _ => (1 : 𝕂))) (ENNReal.ofReal p) 1 μ := by
  have := eLorentzNorm_indicator_const (μ := μ) (p := ENNReal.ofReal p) (q := 1) (a := (1 : 𝕂))
    hF
  rw [memLorentz_iff]
  have e : (fun _ : α => (1 : 𝕂)) = Function.const α 1 := rfl
  rw [e, this]
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp).ne'
  simp only [hp0, one_ne_zero, ↓reduceIte, ENNReal.ofReal_ne_top, ENNReal.one_ne_top, div_one,
    ENNReal.toReal_one, inv_one, ENNReal.rpow_one, enorm_one, mul_one]
  have : 0 ≤ (ENNReal.ofReal p).toReal⁻¹ := by positivity
  finiteness

/-- The restricted weak-type hypothesis of the vendored theorem, from the weak `L^p` bound
`‖T 1_F‖_{L^{p,∞}} ≤ M μ(F)^{1/p}` by the duality estimate. -/
theorem hasRestrictedWeakType_of_wnorm (T : (α → 𝕂) → α' → ε') {p : ℝ} (hp : 1 < p) {M : ℝ≥0}
    (hmeas : ∀ f, MemLorentz f (ENNReal.ofReal p) 1 μ → AEStronglyMeasurable (T f) ν)
    (hF : ∀ F : Set α, MeasurableSet F → μ F < ⊤ →
      wnorm (T (F.indicator fun _ => 1)) (ENNReal.ofReal p) ν ≤ M * μ F ^ p⁻¹) :
    HasRestrictedWeakType T (ENNReal.ofReal p) (ENNReal.ofReal (p / (p - 1))) μ ν
      (((p / (p - 1)).toNNReal * M : ℝ≥0) : ℝ≥0∞) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  intro F G hFm hFt hGm hGt
  have hmem := memLorentz_indicator_one (𝕂 := 𝕂) (μ := μ) hp0 hFm hFt
  refine ⟨hmeas _ hmem, ?_⟩
  set g := T (F.indicator fun _ => (1 : 𝕂)) with hg
  have hgm := hmeas _ hmem
  rw [eLpNorm_one_eq_lintegral_enorm hgm.restrict]
  have e1 : (ENNReal.ofReal p)⁻¹.toReal = p⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hp0.le]
  have e2 : (ENNReal.ofReal (p / (p - 1)))⁻¹.toReal = 1 - 1 / p := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (div_pos hp0 hp1).le]
    field_simp
  rw [e1, e2]
  have hFw := hF F hFm hFt
  by_cases hX0 : (M : ℝ≥0∞) * μ F ^ p⁻¹ = 0
  · -- `T 1_F = 0` a.e.
    rw [hX0, nonpos_iff_eq_zero] at hFw
    have := (wnorm_eq_zero_iff hgm (ENNReal.ofReal_pos.2 hp0).ne').1 hFw
    have h0 : ∀ᵐ x ∂ν, ‖g x‖ₑ = 0 := by
      filter_upwards [this] with x hx
      simpa using hx
    rw [lintegral_congr_ae (g := fun _ => 0) (ae_restrict_of_ae h0)]
    simp
  · have hXt : (M : ℝ≥0∞) * μ F ^ p⁻¹ ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 hp0.le) hFt.ne)
    set X : ℝ≥0 := ((M : ℝ≥0∞) * μ F ^ p⁻¹).toNNReal with hXdef
    have hXE : (X : ℝ≥0∞) = (M : ℝ≥0∞) * μ F ^ p⁻¹ := ENNReal.coe_toNNReal hXt
    have hXpos : 0 < X := by
      rw [pos_iff_ne_zero]
      intro h0
      apply hX0
      rw [← hXE, h0]; simp
    have := lintegral_enorm_restrict_le hgm hp hXpos (hFw.trans_eq hXE.symm) G
    refine this.trans (le_of_eq ?_)
    rw [hXE, ENNReal.coe_mul]
    have : ((p / (p - 1)).toNNReal : ℝ≥0∞) = ENNReal.ofReal (p / (p - 1)) := rfl
    rw [this]
    ring

/-- Weak continuity (the hypothesis `weakly_cont_T` of the vendored theorem) from a.e. pointwise
convergence of `T (fs n)` to `T f` under monotone pointwise approximation, by Fatou. -/
theorem eLpNorm_le_limsup_of_ae_tendsto (T : (α → 𝕂) → α' → ε') {P : ℝ≥0∞}
    (hmeas : ∀ f, MemLorentz f P 1 μ → AEStronglyMeasurable (T f) ν)
    (hcont : ∀ (f : α → 𝕂) (fs : ℕ → α → 𝕂), MemLorentz f P 1 μ →
      (∀ n, AEStronglyMeasurable (fs n) μ) → (∀ a, Monotone fun n => ‖fs n a‖) →
      (∀ a, Tendsto (fun n => fs n a) atTop (𝓝 (f a))) →
      ∀ᵐ x ∂ν, Tendsto (fun n => T (fs n) x) atTop (𝓝 (T f x)))
    {f : α → 𝕂} {fs : ℕ → α → 𝕂} (hf : MemLorentz f P 1 μ)
    (hfs : ∀ n, AEStronglyMeasurable (fs n) μ) (hmono : ∀ a, Monotone fun n => ‖fs n a‖)
    (hlim : ∀ a, Tendsto (fun n => fs n a) atTop (𝓝 (f a))) (G : Set α') :
    eLpNorm (T f) 1 (ν.restrict G) ≤
      limsup (fun n => eLpNorm (T (fs n)) 1 (ν.restrict G)) atTop := by
  have hfsl : ∀ n, MemLorentz (fs n) P 1 μ := by
    intro n
    have hle : ∀ a, ‖fs n a‖ₑ ≤ ‖f a‖ₑ := by
      intro a
      have : ‖fs n a‖ ≤ ‖f a‖ :=
        (hmono a).ge_of_tendsto ((hlim a).norm) n
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal this
    rw [memLorentz_iff]
    exact lt_of_le_of_lt (eLorentzNorm_mono_enorm_ae (hfs n) (Eventually.of_forall hle)) hf
  have hmeasn : ∀ n, AEStronglyMeasurable (T (fs n)) ν := fun n => hmeas _ (hfsl n)
  have hae := hcont f fs hf hfs hmono hlim
  have hmeasf := hmeas f hf
  simp_rw [eLpNorm_one_eq_lintegral_enorm (hmeasn _).restrict]
  rw [eLpNorm_one_eq_lintegral_enorm hmeasf.restrict]
  calc ∫⁻ x in G, ‖T f x‖ₑ ∂ν
      = ∫⁻ x in G, liminf (fun n => ‖T (fs n) x‖ₑ) atTop ∂ν := by
        refine lintegral_congr_ae (ae_restrict_of_ae ?_)
        filter_upwards [hae] with x hx
        exact (hx.enorm.liminf_eq).symm
    _ ≤ liminf (fun n => ∫⁻ x in G, ‖T (fs n) x‖ₑ ∂ν) atTop :=
        lintegral_liminf_le' fun n => (hmeasn n).enorm.restrict
    _ ≤ _ := liminf_le_limsup

/-- **Restricted weak type implies `L^{p,1} → L^{p,∞}`**, abstract form: let `1 < p < ∞` and let `T`
be an operator on functions `α → 𝕂` that is a.e. subadditive on `L^{p,1}`, homogeneous, extensional
(`f = g` a.e. gives `T f = T g` a.e.), with `T 0 = 0`, a.e. strongly measurable values on `L^{p,1}`,
continuous under monotone pointwise approximation (`hcont`), and of restricted weak type
`‖T 1_F‖_{L^{p,∞}} ≤ M μ(F)^{1/p}` for measurable `F` of finite measure.  Then
`‖T f‖_{L^{p,∞}} ≤ (4/(p-1)) M ‖f‖_{L^{p,1}}` for every `f ∈ L^{p,1}`. -/
theorem wnorm_le_of_restricted_weak [SigmaFinite μ] [SigmaFinite ν] (T : (α → 𝕂) → α' → ε')
    {p : ℝ} (hp : 1 < p) {M : ℝ≥0} (hM : 0 < M)
    (hmeas : ∀ f, MemLorentz f (ENNReal.ofReal p) 1 μ → AEStronglyMeasurable (T f) ν)
    (hadd : ∀ f g, MemLorentz f (ENNReal.ofReal p) 1 μ → MemLorentz g (ENNReal.ofReal p) 1 μ →
      ∀ᵐ x ∂ν, ‖T (f + g) x‖ₑ ≤ ‖T f x‖ₑ + ‖T g x‖ₑ)
    (hhom : ∀ (a : 𝕂) (f : α → 𝕂), ∀ᵐ x ∂ν, ‖T (a • f) x‖ₑ ≤ ‖a‖ₑ * ‖T f x‖ₑ)
    (hzero : T 0 =ᵐ[ν] 0) (hext : ∀ f g : α → 𝕂, f =ᵐ[μ] g → T f =ᵐ[ν] T g)
    (hcont : ∀ (f : α → 𝕂) (fs : ℕ → α → 𝕂), MemLorentz f (ENNReal.ofReal p) 1 μ →
      (∀ n, AEStronglyMeasurable (fs n) μ) → (∀ a, Monotone fun n => ‖fs n a‖) →
      (∀ a, Tendsto (fun n => fs n a) atTop (𝓝 (f a))) →
      ∀ᵐ x ∂ν, Tendsto (fun n => T (fs n) x) atTop (𝓝 (T f x)))
    (hF : ∀ F : Set α, MeasurableSet F → μ F < ⊤ →
      wnorm (T (F.indicator fun _ => 1)) (ENNReal.ofReal p) ν ≤ M * μ F ^ p⁻¹)
    {f : α → 𝕂} (hf : MemLorentz f (ENNReal.ofReal p) 1 μ) :
    wnorm (T f) (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal (4 / (p - 1)) * M * eLorentzNorm f (ENNReal.ofReal p) 1 μ := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hq0 : 0 < p / (p - 1) := div_pos hp0 hp1
  have hpq : (ENNReal.ofReal p).HolderConjugate (ENNReal.ofReal (p / (p - 1))) := by
    rw [ENNReal.holderConjugate_iff, ← ENNReal.ofReal_inv_of_pos hp0,
      ← ENNReal.ofReal_inv_of_pos hq0, ← ENNReal.ofReal_add (inv_nonneg.2 hp0.le)
        (inv_nonneg.2 hq0.le)]
    have : p⁻¹ + (p / (p - 1))⁻¹ = 1 := by field_simp; ring
    rw [this, ENNReal.ofReal_one]
  have hT := hasRestrictedWeakType_of_wnorm T hp hmeas hF
  have hc : 0 < (p / (p - 1)).toNNReal * M := mul_pos (Real.toNNReal_pos.2 hq0) hM
  have key := HasRestrictedWeakType.hasLorentzType hpq ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top hc hT (T_meas := fun {f} hf => hmeas f hf)
    (T_subadd := fun {f g} hf hg => hadd f g hf hg) (T_submul := hhom)
    (weakly_cont_T := fun {f fs} hf hfs hmono hlim G =>
      eLpNorm_le_limsup_of_ae_tendsto T hmeas hcont hf hfs hmono hlim G)
    (T_zero := hzero) (T_ae_eq_of_ae_eq := fun {f g} hfg => hext f g hfg)
  have h := (key f hf).2
  refine h.trans (le_of_eq ?_)
  congr 1
  have e1 : ((p / (p - 1)).toNNReal : ℝ≥0∞) = ENNReal.ofReal (p / (p - 1)) := rfl
  have e4 : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by simp
  rw [ENNReal.coe_mul, e1, ← ENNReal.ofReal_coe_nnreal (p := M), e4,
    ← ENNReal.ofReal_mul hq0.le, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
    ← ENNReal.ofReal_div_of_pos hp0, ← ENNReal.ofReal_mul (div_pos (by norm_num) hp1).le]
  congr 1
  field_simp

end Abstract

section FiniteSum

variable {α α' ι 𝕂 : Type*} [MeasurableSpace α] [MeasurableSpace α'] {μ : Measure α}
  {ν : Measure α'} [RCLike 𝕂]

/-- The operator `f ↦ ∑_{j ∈ J} (∫ f k_j dμ) ψ_j`: a finite sum of the linear functionals
`f ↦ ∫ f k_j dμ` times fixed functions `ψ_j`.  The operators `S^ρ[f] = ∑_P ⟨f, φ_P⟩ φ_P a_P` of
[O+] for a finite family of multitiles `P` are of this form (`k_P = conj φ_P`,
`ψ_P = φ_P a_P`). -/
def finSumOp (μ : Measure α) (J : Finset ι) (k : ι → α → 𝕂) (ψ : ι → α' → 𝕂) (f : α → 𝕂)
    (x : α') : 𝕂 :=
  ∑ j ∈ J, (∫ y, f y * k j y ∂μ) * ψ j x

/-- **Restricted weak type implies `L^{p,1} → L^{p,∞}` for finite sums of bounded functionals**
(used for 1- and 2-indices in [O+] `csrhobound`): for `1 < p < ∞`, `k_j ∈ L^{p'}`, `ψ_j`
measurable, if `‖T 1_F‖_{L^{p,∞}} ≤ M μ(F)^{1/p}` for all measurable `F` of finite measure, then
`‖T f‖_{L^{p,∞}} ≤ (4/(p-1)) M ‖f‖_{L^{p,1}}` for all `f ∈ L^{p,1}`, where
`T = finSumOp μ J k ψ`. -/
theorem wnorm_finSumOp_le [SigmaFinite μ] [SigmaFinite ν] (J : Finset ι) {p : ℝ} (hp : 1 < p)
    (k : ι → α → 𝕂) (hk : ∀ j ∈ J, MemLp (k j) (ENNReal.ofReal (p / (p - 1))) μ)
    (ψ : ι → α' → 𝕂) (hψ : ∀ j ∈ J, AEStronglyMeasurable (ψ j) ν) {M : ℝ≥0} (hM : 0 < M)
    (hF : ∀ F : Set α, MeasurableSet F → μ F < ⊤ →
      wnorm (finSumOp μ J k ψ (F.indicator fun _ => 1)) (ENNReal.ofReal p) ν ≤ M * μ F ^ p⁻¹)
    {f : α → 𝕂} (hf : MemLorentz f (ENNReal.ofReal p) 1 μ) :
    wnorm (finSumOp μ J k ψ f) (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal (4 / (p - 1)) * M * eLorentzNorm f (ENNReal.ofReal p) 1 μ := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hq0 : 0 < p / (p - 1) := div_pos hp0 hp1
  have hpq : (ENNReal.ofReal p).HolderConjugate (ENNReal.ofReal (p / (p - 1))) := by
    rw [ENNReal.holderConjugate_iff, ← ENNReal.ofReal_inv_of_pos hp0,
      ← ENNReal.ofReal_inv_of_pos hq0, ← ENNReal.ofReal_add (inv_nonneg.2 hp0.le)
        (inv_nonneg.2 hq0.le)]
    have : p⁻¹ + (p / (p - 1))⁻¹ = 1 := by field_simp; ring
    rw [this, ENNReal.ofReal_one]
  -- integrability of `f * k_j` for `f ∈ L^{p,1}`
  have hint : ∀ g : α → 𝕂, MemLorentz g (ENNReal.ofReal p) 1 μ → ∀ j ∈ J,
      Integrable (fun y => g y * k j y) μ := by
    intro g hg j hj
    have hgp : MemLp g (ENNReal.ofReal p) μ := hg.memLp ⟨one_pos, by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le⟩
    exact hgp.integrable_mul (hk j hj)
  refine wnorm_le_of_restricted_weak (finSumOp μ J k ψ) hp hM ?_ ?_ ?_ ?_ ?_ ?_ hF hf
  · -- measurability
    intro g hg
    unfold finSumOp
    refine Finset.aestronglyMeasurable_fun_sum J fun j hj => ?_
    exact aestronglyMeasurable_const.mul (hψ j hj)
  · -- subadditivity
    intro g h hg hh
    refine Eventually.of_forall fun x => ?_
    have : finSumOp μ J k ψ (g + h) x = finSumOp μ J k ψ g x + finSumOp μ J k ψ h x := by
      unfold finSumOp
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← add_mul, ← integral_add (hint g hg j hj) (hint h hh j hj)]
      simp only [Pi.add_apply, add_mul]
    rw [this]
    exact enorm_add_le _ _
  · -- homogeneity
    intro a g
    refine Eventually.of_forall fun x => ?_
    have : finSumOp μ J k ψ (a • g) x = a * finSumOp μ J k ψ g x := by
      unfold finSumOp
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have : ∫ y, (a • g) y * k j y ∂μ = a * ∫ y, g y * k j y ∂μ := by
        rw [← integral_const_mul]
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [this, mul_assoc]
    rw [this, enorm_mul]
  · -- `T 0 = 0`
    refine Eventually.of_forall fun x => ?_
    simp [finSumOp]
  · -- extensionality
    intro g h hgh
    refine Eventually.of_forall fun x => ?_
    unfold finSumOp
    refine Finset.sum_congr rfl fun j hj => ?_
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hgh] with y hy
    rw [hy]
  · -- continuity under monotone approximation
    intro g gs hg hgs hmono hlim
    refine Eventually.of_forall fun x => ?_
    unfold finSumOp
    refine tendsto_finsetSum _ fun j hj => ?_
    refine Tendsto.mul_const _ ?_
    have hgp : MemLp g (ENNReal.ofReal p) μ := hg.memLp ⟨one_pos, by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le⟩
    refine tendsto_integral_of_dominated_convergence (fun y => ‖g y‖ * ‖k j y‖) ?_ ?_ ?_ ?_
    · intro n
      exact (hgs n).mul (hk j hj).aestronglyMeasurable
    · exact (hint g hg j hj).norm.congr (Eventually.of_forall fun y => by simp [norm_mul])
    · intro n
      refine Eventually.of_forall fun y => ?_
      rw [norm_mul]
      have : ‖gs n y‖ ≤ ‖g y‖ := (hmono y).ge_of_tendsto ((hlim y).norm) n
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    · exact Eventually.of_forall fun y => (hlim y).mul_const _

end FiniteSum

end PrimeCarleson.Proof.Common

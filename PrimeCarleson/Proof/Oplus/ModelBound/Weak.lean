module

public import PrimeCarleson.Proof.Oplus.ModelBound.LevelSet
public import PrimeCarleson.Proof.Oplus.Decomposition.Reflection
public import PrimeCarleson.Proof.Common.LorentzSuperposition

/-!
# `csrhobound`: the restricted weak type bound for the model operators ([O+] L1092-L1137)

Source: [O+] `csrhobound`, L1092–L1096; [O+] `csrhobound`, L1097–L1098 (L1092-L1121, L1131-L1137),
in the amended forms used here: every index `ρ` with `m, n ∈ {1, …, 4}`, every profile choice, every
finite family of `ρ`-multitiles, `r > 2` and `r' ≤ p < 2r/(r-2)`:
`‖𝒮^ρ[f]‖_{L^{p,∞}} ≤ M ‖f‖_{L^{p,1}}` for every `f ∈ L^{p,1}`.

* `wnorm_le_of_levelSet`: the level set bound `|{|g| > λ}| ≤ (C/λ)^p |F|` for all `λ > 0` gives
  `‖g‖_{L^{p,∞}} ≤ C |F|^{1/p}`;
* `csrho_of_levelSet`: from the level set bound for the indicators `1_F` to the `L^{p,1} → L^{p,∞}`
  bound for `𝒮^ρ = finSumOp volume 𝔓 (conj φ_P) (φ_P a_P)` (`modelOp_eq_sum`) by
  `Common.wnorm_finSumOp_le` (the superposition argument, constant `4/(p-1)`);
* `csrhobound_oneOrTwo`: `1`- and `2`-indices, no hypothesis on `Ξ`;
* `levelSet_three`, `csrhobound_three` (3-indices by symmetry): a `3`-index
  `ρ = (3, m, n, side)` is reflected to the `2`-index `ρ̃ = (2, n, m, opposite side)`
  (`modelOp_refl`, for `Ξ` without dyadic end points) with the profile choice `ch.flip` and the
  reversed data. The reflection `x ↦ -x` preserves Lebesgue measure, so the level sets (hence the
  weak `L^p` norms) are unchanged. The transfer is made at the level of the level set bound
  (equivalent to the transfer of the `L^{p,1} → L^{p,∞}` bound), and the bound for `2`-indices is
  applied at `ρ̃ ∉ R`;
* `csrhobound`: all indices at once (`Ξ` without dyadic end points).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson.Proof.Common

/-- The weak `L^p` norm from the level set bound `|{|g| > λ}| ≤ (C/λ)^p |F|` (`λ > 0`). -/
theorem wnorm_le_of_levelSet {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {p C : ℝ}
    (hp : 0 < p) (hC : 0 < C) {F : Set ℝ}
    (h : ∀ lam : ℝ, 0 < lam → volume {x | lam < ‖g x‖} ≤
      ENNReal.ofReal ((C / lam) ^ p) * volume F) :
    wnorm g (ENNReal.ofReal p) volume ≤ ENNReal.ofReal C * volume F ^ p⁻¹ := by
  refine wnorm_le_of_distribution_le hg hp fun t ht => ?_
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  have hset : {x | (t : ℝ≥0∞) < ‖g x‖ₑ} = {x | (t : ℝ) < ‖g x‖} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff']
    exact ⟨fun h => h.1, fun h => ⟨h, htr.trans h⟩⟩
  have hdist : distribution g t volume ≤ ENNReal.ofReal ((C / t) ^ p) * volume F := by
    rw [distribution_eq_measure_superlevelSet, superlevelSet, hset]
    exact h t htr
  refine hdist.trans (le_of_eq ?_)
  have e1 : ENNReal.ofReal C / (t : ℝ≥0∞) = ENNReal.ofReal (C / t) := by
    rw [ENNReal.ofReal_div_of_pos htr, ENNReal.ofReal_coe_nnreal]
  rw [ENNReal.mul_div_right_comm, e1, ENNReal.mul_rpow_of_nonneg _ _ hp.le,
    ENNReal.rpow_inv_rpow hp.ne', ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le]

/-- **`L^{p,1} → L^{p,∞}` from the level set bound for indicators** (the superposition step for 1-
and 2-indices in [O+] `csrhobound`): if `|{|𝒮^ρ 1_F| > λ}| ≤ (C/λ)^p |F|` for every measurable `F`
with `0 < |F| < ∞` and every `λ > 0`, then `‖𝒮^ρ f‖_{L^{p,∞}} ≤ (4/(p-1)) C ‖f‖_{L^{p,1}}`. -/
theorem csrho_of_levelSet {ρ : Idx} {r p : ℝ} (hp : 1 < p) (ch : ProfileChoice)
    (L : Linearization r) (𝔓 : Finset (Multitile ρ)) {C : ℝ} (hC : 0 < C)
    (hlev : ∀ F : Set ℝ, MeasurableSet F → volume F ≠ 0 → volume F ≠ ⊤ → ∀ lam : ℝ, 0 < lam →
      volume {x | lam < ‖modelOp ch L 𝔓 (F.indicator fun _ => (1 : ℂ)) x‖} ≤
        ENNReal.ofReal ((C / lam) ^ p) * volume F)
    {f : ℝ → ℂ} (hf : MemLorentz f (ENNReal.ofReal p) 1 volume) :
    wnorm (modelOp ch L 𝔓 f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (4 / (p - 1)) * (C.toNNReal : ℝ≥0∞) *
        eLorentzNorm f (ENNReal.ofReal p) 1 volume := by
  have hp0 : 0 < p := by linarith
  have hfun : ∀ g : ℝ → ℂ, modelOp ch L 𝔓 g = finSumOp volume 𝔓
      (fun P y => conj (P.wavePacket ch y)) (fun P x => P.wavePacket ch x * P.aP L x) g :=
    fun g => funext fun x => modelOp_eq_sum ch L 𝔓 g x
  have hF : ∀ F : Set ℝ, MeasurableSet F → volume F < ⊤ →
      wnorm (finSumOp volume 𝔓 (fun P y => conj (P.wavePacket ch y))
        (fun P x => P.wavePacket ch x * P.aP L x) (F.indicator fun _ => (1 : ℂ)))
        (ENNReal.ofReal p) volume ≤ (C.toNNReal : ℝ≥0∞) * volume F ^ p⁻¹ := by
    intro F hFm hFt
    rw [← hfun]
    have hmeas : AEStronglyMeasurable (modelOp ch L 𝔓 (F.indicator fun _ => (1 : ℂ))) volume :=
      (measurable_modelOp ch L 𝔓 _).aestronglyMeasurable
    have hCe : (C.toNNReal : ℝ≥0∞) = ENNReal.ofReal C := rfl
    rw [hCe]
    refine wnorm_le_of_levelSet hmeas hp0 hC (F := F) fun lam hlam => ?_
    by_cases hF0 : volume F = 0
    · have hg0 : ∀ x, modelOp ch L 𝔓 (F.indicator fun _ => (1 : ℂ)) x = 0 := by
        intro x
        unfold modelOp
        refine Finset.sum_eq_zero fun P _ => ?_
        have hc : P.coeff ch (F.indicator fun _ => (1 : ℂ)) = 0 := by
          unfold Multitile.coeff pairing
          refine integral_eq_zero_of_ae ?_
          have hnot : ∀ᵐ y, y ∉ F := by
            rw [ae_iff]
            simpa using hF0
          filter_upwards [hnot] with y hy
          simp [hy]
        rw [hc]
        simp
      have : {x | lam < ‖modelOp ch L 𝔓 (F.indicator fun _ => (1 : ℂ)) x‖} = ∅ := by
        ext x
        simp [hg0, hlam.le]
      rw [this]
      simp
    · exact hlev F hFm hF0 hFt.ne lam hlam
  rw [hfun]
  exact wnorm_finSumOp_le (μ := volume) (ν := volume) 𝔓 hp
    (fun P y => conj (P.wavePacket ch y)) (fun P _ => memLp_conj_wavePacket P ch _)
    (fun P x => P.wavePacket ch x * P.aP L x)
    (fun P _ => (measurable_psi P ch L).aestronglyMeasurable)
    (M := C.toNNReal) (Real.toNNReal_pos.2 hC) hF hf

/-- The indicator `1_F` (complex valued) is bounded by `1_F`. -/
theorem norm_indicator_one_le (F : Set ℝ) (x : ℝ) :
    ‖F.indicator (fun _ => (1 : ℂ)) x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ F <;> simp [hx]

/-- `ofReal (4/(p-1)) * ofReal C = ↑((4/(p-1)).toNNReal * C.toNNReal)`. -/
theorem ofReal_mul_toNNReal (a C : ℝ) :
    ENNReal.ofReal a * (C.toNNReal : ℝ≥0∞) = ((a.toNNReal * C.toNNReal : ℝ≥0) : ℝ≥0∞) := by
  rw [ENNReal.coe_mul]
  rfl

/-- **`csrhobound`** ([O+] L1097-L1098, L1131-L1137): for every `1`- or `2`-index
`ρ` with `m, n ∈ {1, …, 4}` (not only those in `R`), every profile choice, finite family of
`ρ`-multitiles and linearizing data, and `f ∈ L^{p,1}`, `r' ≤ p < 2r/(r-2)`:
`‖𝒮^ρ[f]‖_{L^{p,∞}} ≤ M ‖f‖_{L^{p,1}}`, `M = (4/(p-1)) C`, `C` the constant of
`levelSet_family`. -/
theorem csrhobound_oneOrTwo {r p : ℝ} (hr : 2 < r) (hp1 : Real.conjExponent r ≤ p)
    (hp2 : p < 2 * r / (r - 2)) {C₁ C₂ C₃ : ℝ} (hC : AdmissibleConstants C₁ C₂ C₃)
    (hC₂ : C₂ = 2) :
    ∃ M : ℝ≥0, 0 < M ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo], ρ.IsStd → ∀ (ch : ProfileChoice)
      (L : Linearization r) (𝔓 : Finset (Multitile ρ)) {f : ℝ → ℂ},
      MemLorentz f (ENNReal.ofReal p) 1 volume →
      wnorm (modelOp ch L 𝔓 f) (ENNReal.ofReal p) volume ≤
        (M : ℝ≥0∞) * eLorentzNorm f (ENNReal.ofReal p) 1 volume := by
  have hr1 : 1 < r := by linarith
  have hp : 1 < p := lt_of_lt_of_le (one_lt_conjExponent hr1) hp1
  obtain ⟨C, hC0, hfam⟩ := levelSet_family hr hp1 hp2 hC hC₂
  refine ⟨(4 / (p - 1)).toNNReal * C.toNNReal,
    mul_pos (Real.toNNReal_pos.2 (div_pos (by norm_num) (by linarith))) (Real.toNNReal_pos.2 hC0),
    ?_⟩
  intro ρ _ hρ ch L 𝔓 f hf
  have := csrho_of_levelSet hp ch L 𝔓 hC0 (fun F hF hF0 hFt lam hlam =>
    hfam hρ ch hF hF0 hFt (measurable_const.indicator hF).aestronglyMeasurable
      (Filter.Eventually.of_forall (norm_indicator_one_le F)) L 𝔓 lam hlam) hf
  rwa [ofReal_mul_toNNReal] at this

/-- **The level set bound for a `3`-index** ([O+] L1099-L1121): for
`ρ = (3, m, n, side)` with `m, n ∈ {1, …, 4}`, any profile choice and any linearizing data with `Ξ`
free of dyadic end points, `|{|𝒮^ρ f| > λ}| ≤ (C/λ)^p |F|` for `|f| ≤ 1_F`, by reflection to the
`2`-index `ρ̃ = (2, n, m, opposite side)` (`ρ̃ ∉ R` in general) with the profile choice `ch.flip`,
the data `L.refl` and `f(-·)`. -/
theorem levelSet_three {r p : ℝ} (hr : 2 < r) (hp1 : Real.conjExponent r ≤ p)
    (hp2 : p < 2 * r / (r - 2)) {C₁ C₂ C₃ : ℝ} (hC : AdmissibleConstants C₁ C₂ C₃)
    (hC₂ : C₂ = 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ρ : Idx}, ρ.typ = IdxType.three → ρ.IsStd → ∀ (ch : ProfileChoice)
      {f : ℝ → ℂ} {F : Set ℝ}, MeasurableSet F → volume F ≠ 0 → volume F ≠ ⊤ →
      AEStronglyMeasurable f volume → (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) →
      ∀ (L : Linearization r), AvoidsDyadicEndpoints (L.Ξ : Set ℝ) →
      ∀ (𝔓 : Finset (Multitile ρ)) (lam : ℝ), 0 < lam →
      volume {x | lam < ‖modelOp ch L 𝔓 f x‖} ≤ ENNReal.ofReal ((C / lam) ^ p) * volume F := by
  obtain ⟨C, hC0, hfam⟩ := levelSet_family hr hp1 hp2 hC hC₂
  refine ⟨C, hC0, ?_⟩
  intro ρ hρ3 hρ ch f F hF hF0 hFt hfm hfF L hΞ 𝔓 lam hlam
  have : Fact ρ.refl.IsOneOrTwo := ⟨Idx.isOneOrTwo_refl_of_typ_three hρ3⟩
  have hρ' : ρ.refl.IsStd := Idx.isStd_refl.2 hρ
  have hneg : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  obtain ⟨F', hF'def⟩ : ∃ F' : Set ℝ, F' = (fun x : ℝ => -x) ⁻¹' F := ⟨_, rfl⟩
  have hF'm : MeasurableSet F' := by rw [hF'def]; exact hF.preimage hneg.measurable
  have hvF' : volume F' = volume F := by
    rw [hF'def]; exact hneg.measure_preimage hF.nullMeasurableSet
  have hfm' : AEStronglyMeasurable (fun y => f (-y)) volume := hfm.comp_measurePreserving hneg
  have hfF' : ∀ᵐ y, ‖f (-y)‖ ≤ F'.indicator (fun _ => (1 : ℝ)) y := by
    filter_upwards [hneg.quasiMeasurePreserving.ae hfF] with y hy
    have hi : F'.indicator (fun _ => (1 : ℝ)) y = F.indicator (fun _ => (1 : ℝ)) (-y) := by
      by_cases h : -y ∈ F
      · have h' : y ∈ F' := by rw [hF'def]; exact h
        rw [Set.indicator_of_mem h', Set.indicator_of_mem h]
      · have h' : y ∉ F' := by rw [hF'def]; exact h
        rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]
    rw [hi]
    exact hy
  have key := hfam hρ' ch.flip hF'm (hvF' ▸ hF0) (hvF' ▸ hFt) hfm' hfF' L.refl
    (𝔓.image Multitile.refl) lam hlam
  have hset : {x | lam < ‖modelOp ch L 𝔓 f x‖} = (fun x : ℝ => -x) ⁻¹'
      {y | lam < ‖modelOp ch.flip L.refl (𝔓.image Multitile.refl) (fun y => f (-y)) y‖} := by
    ext x
    simp only [mem_preimage, Set.mem_ofPred_eq, modelOp_refl ch L hΞ 𝔓 f x]
  rw [hset, hneg.measure_preimage
    (measurableSet_lt measurable_const (measurable_modelOp _ _ _ _).norm).nullMeasurableSet]
  rwa [hvF'] at key

/-- **`csrhobound`** ([O+] L1097-L1121): the bound
`‖𝒮^ρ[f]‖_{L^{p,∞}} ≤ M ‖f‖_{L^{p,1}}` for the `3`-indices with `m, n ∈ {1, …, 4}` (in particular
for the three `3`-indices of `R`), from the reflection to `(2, n, m, opposite side)`, for
linearizing data with `Ξ` free of dyadic end points. -/
theorem csrhobound_three {r p : ℝ} (hr : 2 < r) (hp1 : Real.conjExponent r ≤ p)
    (hp2 : p < 2 * r / (r - 2)) {C₁ C₂ C₃ : ℝ} (hC : AdmissibleConstants C₁ C₂ C₃)
    (hC₂ : C₂ = 2) :
    ∃ M : ℝ≥0, 0 < M ∧ ∀ {ρ : Idx}, ρ.typ = IdxType.three → ρ.IsStd → ∀ (ch : ProfileChoice)
      (L : Linearization r), AvoidsDyadicEndpoints (L.Ξ : Set ℝ) →
      ∀ (𝔓 : Finset (Multitile ρ)) {f : ℝ → ℂ}, MemLorentz f (ENNReal.ofReal p) 1 volume →
      wnorm (modelOp ch L 𝔓 f) (ENNReal.ofReal p) volume ≤
        (M : ℝ≥0∞) * eLorentzNorm f (ENNReal.ofReal p) 1 volume := by
  have hr1 : 1 < r := by linarith
  have hp : 1 < p := lt_of_lt_of_le (one_lt_conjExponent hr1) hp1
  obtain ⟨C, hC0, hlev⟩ := levelSet_three hr hp1 hp2 hC hC₂
  refine ⟨(4 / (p - 1)).toNNReal * C.toNNReal,
    mul_pos (Real.toNNReal_pos.2 (div_pos (by norm_num) (by linarith))) (Real.toNNReal_pos.2 hC0),
    ?_⟩
  intro ρ hρ3 hρ ch L hΞ 𝔓 f hf
  have := csrho_of_levelSet hp ch L 𝔓 hC0 (fun F hF hF0 hFt lam hlam =>
    hlev hρ3 hρ ch hF hF0 hFt (measurable_const.indicator hF).aestronglyMeasurable
      (Filter.Eventually.of_forall (norm_indicator_one_le F)) L hΞ 𝔓 lam hlam) hf
  rwa [ofReal_mul_toNNReal] at this

/-- **`csrhobound`** ([O+] L1092-L1096): the bound
`‖𝒮^ρ[f]‖_{L^{p,∞}} ≤ M ‖f‖_{L^{p,1}}` for every index `ρ` with `m, n ∈ {1, …, 4}` (types `1, 2,
3`; in particular all ten indices of `R`), every profile choice, finite family and linearizing data
with `Ξ` free of dyadic end points, `r > 2`, `r' ≤ p < 2r/(r-2)`, with `M = M(p, r)` independent of
all of them. -/
theorem csrhobound {r p : ℝ} (hr : 2 < r) (hp1 : Real.conjExponent r ≤ p)
    (hp2 : p < 2 * r / (r - 2)) {C₁ C₂ C₃ : ℝ} (hC : AdmissibleConstants C₁ C₂ C₃)
    (hC₂ : C₂ = 2) :
    ∃ M : ℝ≥0, 0 < M ∧ ∀ {ρ : Idx}, ρ.IsStd → ∀ (ch : ProfileChoice)
      (L : Linearization r), AvoidsDyadicEndpoints (L.Ξ : Set ℝ) →
      ∀ (𝔓 : Finset (Multitile ρ)) {f : ℝ → ℂ}, MemLorentz f (ENNReal.ofReal p) 1 volume →
      wnorm (modelOp ch L 𝔓 f) (ENNReal.ofReal p) volume ≤
        (M : ℝ≥0∞) * eLorentzNorm f (ENNReal.ofReal p) 1 volume := by
  obtain ⟨M₁, hM₁, h12⟩ := csrhobound_oneOrTwo hr hp1 hp2 hC hC₂
  obtain ⟨M₃, hM₃, h3⟩ := csrhobound_three hr hp1 hp2 hC hC₂
  refine ⟨max M₁ M₃, lt_max_of_lt_left hM₁, ?_⟩
  intro ρ hρ ch L hΞ 𝔓 f hf
  by_cases h : ρ.typ = IdxType.three
  · refine (h3 h hρ ch L hΞ 𝔓 hf).trans ?_
    gcongr
    exact le_max_right _ _
  · have : Fact ρ.IsOneOrTwo := ⟨h⟩
    refine (h12 hρ ch L 𝔓 hf).trans ?_
    gcongr
    exact le_max_left _ _

end PrimeCarleson.Proof.Oplus

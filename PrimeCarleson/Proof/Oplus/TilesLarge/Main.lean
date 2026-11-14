module

public import PrimeCarleson.Proof.Oplus.TilesLarge.SingleScale
public import PrimeCarleson.Proof.Oplus.TilesLarge.Packing
public import PrimeCarleson.Proof.Oplus.TreeSmall.TreeSum

/-!
# The auxiliary tile estimate `tileslargemaxprop` ([O+] Proposition `tileslargemaxprop`)

[O+] L2473-L2482 (statement), L2485-L2547 (proof): "Let `𝔓`
be a finite set of multitiles, `λ > 0`, `F ⊂ ℝ`, `|f| ≤ 1_F` and `Ω_λ = {M[1_F] > λ}`. Then
`‖∑_{P ∈ 𝔓 : I ⊂ Ω} ⟨f, φ_P⟩ φ_P a_P‖_{L¹(ℝ ∖ Ω)} ≲ |F| λ^{-1/r}`." Consumed at L2656
(the small-`F` case of `L1except`) with `λ = C'' |F|` and `Ω_λ = G`.

`tileslargemaxprop` proves it for every `1`- or `2`-index `ρ`, every profile choice, every finite
family `S` of `ρ`-multitiles all of whose time intervals lie in `Ω_λ` (the family
`{P ∈ 𝔓 : I ⊂ Ω_λ}` of the proposition), every `r ≥ 2`, `N ≥ 4`, with a
constant depending on `N` only (neither the separation assumptions, the constants `C₁, C₂, C₃`,
nor the squares `M` of the tiles enter). `tileslargemaxprop_treeSum` is the form with the
indicator `1_E` (`treeSum ch f L E S`) used at L2656.

Proof (L2487-L2546): `exists_scale` gives, for every `I ⊂ Ω_λ`, the integer `ℓ = ℓ(I) ≥ 0` with
`2^ℓ I ⊂ Ω_λ` and `2^{ℓ+1} I ⊄ Ω_λ` (display `(2lIOmega)`; if `Ω_λ = ℝ` the `L¹(ℝ ∖ Ω_λ)` norm is
zero); the tiles are grouped by their time interval (Minkowski in `L¹(ℝ ∖ Ω_λ)`), each group is
bounded by `exists_eLpNorm_single_scale_le` (`≲ 2^{-ℓ(N-3)} λ^{1/r'} |I|`), the intervals with
`ℓ(I) = ℓ` are packed by `sum_ofReal_length_le_of_scale` (`∑ |I| ≤ 6 |Ω_λ|`), the sum over `ℓ` is
geometric (`N ≥ 4`) and `|Ω_λ| ≤ 4 |F|/λ` is the weak `(1, 1)` bound for `M` (the form
`volume_maximalHLR_indicator_gt_le` of `Common/HardyLittlewoodR.lean`), so
`λ^{1/r'} |Ω_λ| ≲ |F| λ^{1/r' - 1} = |F| λ^{-1/r}`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson.Proof.Common

/-- **The scale of an interval `I ⊂ Ω`** (display `(2lIOmega)`, L2487-L2490): if `Ω ≠ ℝ` and
`I ⊂ Ω` there is `ℓ ≥ 0` with `2^ℓ I ⊂ Ω` and `2^{ℓ+1} I ⊄ Ω` (the largest `ℓ` with `2^ℓ I ⊂ Ω`;
`ℓ = 0` is admissible since `2^0 I = I ⊂ Ω`). -/
theorem exists_scale {Ω : Set ℝ} (hne : Ωᶜ.Nonempty) {I : Dyadic} (h : I.toSet ⊆ Ω) :
    ∃ ℓ : ℕ, I.dilate ((2 : ℝ) ^ ℓ) ⊆ Ω ∧ ¬ I.dilate ((2 : ℝ) ^ (ℓ + 1)) ⊆ Ω := by
  classical
  obtain ⟨y, hy⟩ := hne
  have hex : ∃ n : ℕ, ¬ I.dilate ((2 : ℝ) ^ n) ⊆ Ω := by
    have hy' : y ∈ ⋃ n : ℕ, I.dilate ((2 : ℝ) ^ (n + 1)) := by
      rw [I.iUnion_dilate_pow]; exact mem_univ y
    obtain ⟨n, hn⟩ := mem_iUnion.1 hy'
    exact ⟨n + 1, fun hsub => hy (hsub hn)⟩
  have hm : ¬ I.dilate ((2 : ℝ) ^ (Nat.find hex)) ⊆ Ω := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hm
    rw [h0, pow_zero, Dyadic.dilate_one]
    exact h
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, Nat.find hex = ℓ + 1 := ⟨Nat.find hex - 1, by omega⟩
  refine ⟨ℓ, ?_, hℓ ▸ hm⟩
  by_contra hcon
  exact Nat.find_min hex (by omega : ℓ < Nat.find hex) hcon

/-- **The sum over intervals and scales, one scale** ([O+] L2538-L2546): for
`N ≥ 3` there is `K` such that for every finite set `S` of `ρ`-multitiles (`ρ` a `1`- or
`2`-index) whose time intervals `I` all satisfy `(2lIOmega)` for the same `ℓ` (`2^ℓ I ⊂ Ω_λ` and
`2^{ℓ+1} I ⊄ Ω_λ`),
`‖∑_{P ∈ S} ⟨f, φ_P⟩ φ_P a_P‖_{L¹(ℝ ∖ Ω_λ)} ≤ K ((2^ℓ)⁻¹)^{N-3} λ^{1/r'} · 6 |Ω_λ|`
(the single-scale bound summed over the intervals, which are packed by
`sum_ofReal_length_le_of_scale`). -/
theorem exists_eLpNorm_scale_class_le (N : ℕ) (hN : 3 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx}, ρ.IsOneOrTwo → ∀ {r : ℝ}, 2 ≤ r → ∀ (ch : ProfileChoice)
      (L : Linearization r) (S : Finset (Multitile ρ)) {F : Set ℝ} {f : ℝ → ℂ},
      MeasurableSet F → AEStronglyMeasurable f volume →
      (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) → ∀ {lam : ℝ}, 0 < lam → ∀ {ℓ : ℕ},
      (∀ P ∈ S, P.I.dilate ((2 : ℝ) ^ ℓ) ⊆ maxSuperlevel F lam ∧
        ¬ P.I.dilate ((2 : ℝ) ^ (ℓ + 1)) ⊆ maxSuperlevel F lam) →
        eLpNorm (fun x => ∑ P ∈ S, P.coeff ch f * P.wavePacket ch x * P.aP L x) 1
          (volume.restrict (maxSuperlevel F lam)ᶜ) ≤
        ENNReal.ofReal (K * (((2 : ℝ) ^ ℓ)⁻¹) ^ (N - 3) * lam ^ (1 / Real.conjExponent r)) *
          (6 * volume (maxSuperlevel F lam)) := by
  classical
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_eLpNorm_single_scale_le N hN
  refine ⟨K₁, hK₁0, ?_⟩
  intro ρ hρ r hr ch L S F f hF hfm hfF lam hlam ℓ hS
  set Ω := maxSuperlevel F lam with hΩ
  set J : Finset Dyadic := S.image Multitile.I with hJ
  set c : ℝ := K₁ * (((2 : ℝ) ^ ℓ)⁻¹) ^ (N - 3) * lam ^ (1 / Real.conjExponent r) with hc
  have hc0 : 0 ≤ c := by positivity
  set G : Dyadic → ℝ → ℂ := fun I x =>
    ∑ P ∈ S.filter (fun P => P.I = I), P.coeff ch f * P.wavePacket ch x * P.aP L x with hG
  have hsplit : (fun x => ∑ P ∈ S, P.coeff ch f * P.wavePacket ch x * P.aP L x) =
      ∑ I ∈ J, G I := by
    funext x
    rw [Finset.sum_apply]
    simp only [hG]
    exact (Finset.sum_fiberwise_of_maps_to (s := S) (t := J) (g := Multitile.I)
      (fun P hP => Finset.mem_image_of_mem _ hP) (fun P => P.coeff ch f * P.wavePacket ch x *
        P.aP L x)).symm
  have hIJ : ∀ I ∈ J, I.dilate ((2 : ℝ) ^ ℓ) ⊆ Ω ∧ ¬ I.dilate ((2 : ℝ) ^ (ℓ + 1)) ⊆ Ω := by
    intro I hI
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hI
    exact hS P hP
  have hgroup : ∀ I ∈ J, eLpNorm (G I) 1 (volume.restrict Ωᶜ) ≤
      ENNReal.ofReal (c * I.length) := by
    intro I hI
    have h1 := hK₁ hρ hr ch L (S.filter fun P => P.I = I) (I₀ := I)
      (fun P hP => (Finset.mem_filter.1 hP).2) hF hfm hfF hlam (ℓ := ℓ)
      (hIJ I hI).1 (hIJ I hI).2
    refine h1.trans (le_of_eq ?_)
    congr 1
  calc eLpNorm (fun x => ∑ P ∈ S, P.coeff ch f * P.wavePacket ch x * P.aP L x) 1
        (volume.restrict Ωᶜ)
      ≤ ∑ I ∈ J, eLpNorm (G I) 1 (volume.restrict Ωᶜ) := by
        rw [hsplit]
        exact eLpNorm_sum_le (μ := volume.restrict Ωᶜ) (s := J) (f := G) le_rfl
    _ ≤ ∑ I ∈ J, ENNReal.ofReal c * ENNReal.ofReal I.length := by
        refine Finset.sum_le_sum fun I hI => (hgroup I hI).trans (le_of_eq ?_)
        rw [← ENNReal.ofReal_mul hc0]
    _ = ENNReal.ofReal c * ∑ I ∈ J, ENNReal.ofReal I.length := by rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal c * (6 * volume Ω) := by
        gcongr
        exact sum_ofReal_length_le_of_scale (Ω := Ω) (ℓ := ℓ) J (fun I hI => (hIJ I hI).1)
          (fun I hI => (hIJ I hI).2) (measurableSet_maxSuperlevel F lam)

/-- **`tileslargemaxprop`** ([O+] Proposition `tileslargemaxprop`, L2473-L2547, with its proof
steps: the `ℓ²`, `sup` and `ℓ^r` coefficient bounds, the single-scale `L¹` bound, the sparsity of
`F` near a scale and the sum over intervals and scales). For `N ≥ 4` there is `K > 0` such that for
every `1`- or `2`-index `ρ`, `r ≥ 2`, profile choice, linearizing data `L` (for `r`), finite set `S`
of `ρ`-multitiles, measurable `F`, `f` with `|f| ≤ 1_F` and `λ > 0` such that
`I ⊂ Ω_λ = {M[1_F] > λ}` for all `P ∈ S`,
`‖∑_{P ∈ S} ⟨f, φ_P⟩ φ_P a_P‖_{L¹(ℝ ∖ Ω_λ)} ≤ K λ^{-1/r} |F|`. -/
theorem tileslargemaxprop (N : ℕ) (hN : 4 ≤ N) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ρ : Idx}, ρ.IsOneOrTwo → ∀ {r : ℝ}, 2 ≤ r → ∀ (ch : ProfileChoice)
      (L : Linearization r) (S : Finset (Multitile ρ)) {F : Set ℝ} {f : ℝ → ℂ},
      MeasurableSet F → AEStronglyMeasurable f volume →
      (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) → ∀ {lam : ℝ}, 0 < lam →
      (∀ P ∈ S, P.I.toSet ⊆ maxSuperlevel F lam) →
        eLpNorm (fun x => ∑ P ∈ S, P.coeff ch f * P.wavePacket ch x * P.aP L x) 1
          (volume.restrict (maxSuperlevel F lam)ᶜ) ≤
        ENNReal.ofReal (K * lam ^ (-(1 / r))) * volume F := by
  classical
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_eLpNorm_scale_class_le N (by omega)
  refine ⟨48 * K₁ + 1, by positivity, ?_⟩
  intro ρ hρ r hr ch L S F f hF hfm hfF lam hlam hS
  have hr1 : 1 < r := by linarith
  set Ω := maxSuperlevel F lam with hΩ
  by_cases hne : Ωᶜ.Nonempty
  swap
  · have : Ωᶜ = ∅ := not_nonempty_iff_eq_empty.1 hne
    rw [this, Measure.restrict_empty]
    simp
  set s : ℝ := 1 / Real.conjExponent r with hs
  have hs_eq : s = 1 - 1 / r := one_div_conjExponent_eq hr1
  -- the scale of each time interval
  choose! sc hsc using fun (I : Dyadic) (hI : I.toSet ⊆ Ω) => exists_scale hne hI
  set M : ℕ := S.sup (fun P => sc P.I) with hM
  -- grouping by scale
  set G : ℕ → ℝ → ℂ := fun ℓ x =>
    ∑ P ∈ S.filter (fun P => sc P.I = ℓ), P.coeff ch f * P.wavePacket ch x * P.aP L x with hG
  have hsplit : (fun x => ∑ P ∈ S, P.coeff ch f * P.wavePacket ch x * P.aP L x) =
      ∑ ℓ ∈ Finset.range (M + 1), G ℓ := by
    funext x
    rw [Finset.sum_apply]
    simp only [hG]
    exact (Finset.sum_fiberwise_of_maps_to (s := S) (t := Finset.range (M + 1))
      (g := fun P => sc P.I)
      (fun P hP => Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := fun P => sc P.I) hP)))
      (fun P => P.coeff ch f * P.wavePacket ch x * P.aP L x)).symm
  have hclass : ∀ ℓ ∈ Finset.range (M + 1), eLpNorm (G ℓ) 1 (volume.restrict Ωᶜ) ≤
      ENNReal.ofReal (K₁ * ((1 / 2 : ℝ) ^ ℓ) * lam ^ s) * (6 * volume Ω) := by
    intro ℓ _
    have h1 := hK₁ hρ hr ch L (S.filter fun P => sc P.I = ℓ) hF hfm hfF hlam (ℓ := ℓ)
      (fun P hP => by
        obtain ⟨hP1, hP2⟩ := Finset.mem_filter.1 hP
        rw [← hP2]; exact hsc P.I (hS P hP1))
    refine h1.trans ?_
    gcongr
    have h2 : (((2 : ℝ) ^ ℓ)⁻¹) ^ (N - 3) ≤ (1 / 2 : ℝ) ^ ℓ := by
      have h3 : ((2 : ℝ) ^ ℓ)⁻¹ = (1 / 2 : ℝ) ^ ℓ := by rw [one_div, inv_pow]
      rw [h3]
      refine pow_le_of_le_one (by positivity) ?_ (by omega)
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have : 0 ≤ lam ^ s := by positivity
    gcongr
  -- the weak type `(1, 1)` bound
  have hweak : volume Ω ≤ ENNReal.ofReal (4 / lam) * volume F := by
    have h1 := volume_maximalHLR_indicator_gt_le hF (t := ENNReal.ofReal lam)
      (ENNReal.ofReal_pos.2 hlam).ne'
    refine h1.trans (le_of_eq ?_)
    rw [ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_inv_of_pos hlam,
      show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    ring
  have e1 : lam ^ s = lam ^ (-(1 / r)) * lam := by
    rw [hs_eq, sub_eq_add_neg, Real.rpow_add hlam, Real.rpow_one, mul_comm]
  have e4 : K₁ * lam ^ s * 6 * 2 * (4 / lam) = 48 * K₁ * lam ^ (-(1 / r)) := by
    rw [e1]
    field_simp
    ring
  have hlr : 0 ≤ lam ^ (-(1 / r)) := by positivity
  have hgeo : ∑ ℓ ∈ Finset.range (M + 1), ENNReal.ofReal ((1 / 2 : ℝ) ^ ℓ) ≤ ENNReal.ofReal 2 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ℓ _ => by positivity)]
    exact ENNReal.ofReal_le_ofReal (sum_geometric_two_le _)
  -- assemble
  calc eLpNorm (fun x => ∑ P ∈ S, P.coeff ch f * P.wavePacket ch x * P.aP L x) 1
        (volume.restrict Ωᶜ)
      ≤ ∑ ℓ ∈ Finset.range (M + 1), eLpNorm (G ℓ) 1 (volume.restrict Ωᶜ) := by
        rw [hsplit]
        exact eLpNorm_sum_le (μ := volume.restrict Ωᶜ) (s := Finset.range (M + 1)) (f := G) le_rfl
    _ ≤ ∑ ℓ ∈ Finset.range (M + 1), ENNReal.ofReal (K₁ * lam ^ s) *
          (ENNReal.ofReal ((1 / 2 : ℝ) ^ ℓ) * (6 * volume Ω)) := by
        refine Finset.sum_le_sum fun ℓ hℓ => (hclass ℓ hℓ).trans (le_of_eq ?_)
        rw [show K₁ * (1 / 2 : ℝ) ^ ℓ * lam ^ s = (K₁ * lam ^ s) * (1 / 2 : ℝ) ^ ℓ by ring,
          ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ = ENNReal.ofReal (K₁ * lam ^ s) *
          ((∑ ℓ ∈ Finset.range (M + 1), ENNReal.ofReal ((1 / 2 : ℝ) ^ ℓ)) * (6 * volume Ω)) := by
        rw [← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ ENNReal.ofReal (K₁ * lam ^ s) * (ENNReal.ofReal 2 * (6 * volume Ω)) := by gcongr
    _ ≤ ENNReal.ofReal (K₁ * lam ^ s) * (ENNReal.ofReal 2 * (6 *
          (ENNReal.ofReal (4 / lam) * volume F))) := by gcongr
    _ = ENNReal.ofReal (48 * K₁ * lam ^ (-(1 / r))) * volume F := by
        rw [show (6 : ℝ≥0∞) = ENNReal.ofReal 6 by simp, ← mul_assoc (ENNReal.ofReal 6),
          ← mul_assoc, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        have : K₁ * lam ^ s * 2 * 6 * (4 / lam) = 48 * K₁ * lam ^ (-(1 / r)) := by
          rw [← e4]; ring
        rw [this]
    _ ≤ ENNReal.ofReal ((48 * K₁ + 1) * lam ^ (-(1 / r))) * volume F := by
        gcongr
        nlinarith

/-- **`tileslargemaxprop` with the indicator `1_E`** (the form consumed at L2656 of [O+], in the
small-`F` case of `L1except`): the tree sum `treeSum ch f L E S =
∑_{P ∈ S} ⟨f, φ_P⟩ φ_P a_P 1_E` of the tiles with `I ⊂ Ω_λ` satisfies
`‖treeSum‖_{L¹(ℝ ∖ Ω_λ)} ≤ K λ^{-1/r} |F|` for every measurable set `E` (measurability makes the
tree sum measurable; the `L¹` norm is `∞` for a non-measurable function). -/
theorem tileslargemaxprop_treeSum (N : ℕ) (hN : 4 ≤ N) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ρ : Idx}, ρ.IsOneOrTwo → ∀ {r : ℝ}, 2 ≤ r → ∀ (ch : ProfileChoice)
      (L : Linearization r) {E : Set ℝ}, MeasurableSet E → ∀ (S : Finset (Multitile ρ)) {F : Set ℝ}
      {f : ℝ → ℂ}, MeasurableSet F → AEStronglyMeasurable f volume →
      (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) → ∀ {lam : ℝ}, 0 < lam →
      (∀ P ∈ S, P.I.toSet ⊆ maxSuperlevel F lam) →
        eLpNorm (treeSum ch f L E S) 1 (volume.restrict (maxSuperlevel F lam)ᶜ) ≤
        ENNReal.ofReal (K * lam ^ (-(1 / r))) * volume F := by
  obtain ⟨K, hK0, hK⟩ := tileslargemaxprop N hN
  refine ⟨K, hK0, fun {ρ} hρ {r} hr ch L {E} hE S {F} {f} hF hfm hfF {lam} hlam hS => ?_⟩
  have hmeas : Measurable (treeSum ch f L E S) := by
    have : treeSum ch f L E S = fun x => (∑ P ∈ S, P.coeff ch f * P.wavePacket ch x *
        P.aP L x) * E.indicator (fun _ => (1 : ℂ)) x := by
      funext x
      simp only [treeSum, Finset.sum_mul]
    rw [this]
    exact (measurable_tileSum ch f L S).mul (measurable_const.indicator hE)
  refine (eLpNorm_mono_ae hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)).trans (hK hρ hr ch L S hF hfm hfF hlam hS)
  simp only [treeSum]
  rw [← Finset.sum_mul, norm_mul]
  have h1 : ‖E.indicator (fun _ => (1 : ℂ)) x‖ ≤ 1 := by
    by_cases hx : x ∈ E <;> simp [hx]
  have h2 := norm_nonneg (∑ P ∈ S, P.coeff ch f * P.wavePacket ch x * P.aP L x)
  nlinarith

end PrimeCarleson.Proof.Oplus

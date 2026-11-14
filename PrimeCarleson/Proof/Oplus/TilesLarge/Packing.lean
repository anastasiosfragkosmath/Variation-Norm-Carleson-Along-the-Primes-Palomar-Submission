module

public import PrimeCarleson.Proof.Oplus.TilesLarge.Sparsity
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.BmoGeometry

/-!
# The packing of the intervals at one scale of `Ω_λ` ([O+] L2538-L2542)

Source: [O+] `tileslargemaxprop`, L2538–L2546 (L2538-L2542): "For `ℓ ≥ 0` let `𝓘_ℓ` be the set of
all dyadic intervals satisfying `(2lIOmega)` [`2^ℓ I ⊂ Ω_λ` and `2^{ℓ+1} I ⊄ Ω_λ`]. ... By
considering the collection of maximal dyadic intervals in `𝓘_ℓ`, one sees that
`∑_{I ∈ 𝓘_ℓ} |I| ≲ |Ω_λ|`."

The statement is proved here (for every finite `𝒥 ⊆ 𝓘_ℓ`, with the constant `6`) by a bounded
overlap argument instead of the printed "at most 2 intervals `I' ⊂ I` at each level" (which is a
one-line sketch): for `I ∈ 𝓘_ℓ` the middle half `E_I = (1/2) I` of `I` lies in `Ω_λ` and its
points `x` have `2^ℓ |I|/4 ≤ dist(x, ℝ ∖ Ω_λ) ≤ (5/4) 2^ℓ |I|`; hence the sizes of the intervals
`I` with `x ∈ E_I` lie in a window of ratio `5 < 8`, at most three dyadic scales, and dyadic
intervals of one scale containing `x` coincide (`pointwise_card_le_three`), so
`∑_I 1_{E_I} ≤ 3 · 1_{Ω_λ}` and `∑_I |I| = 2 ∑_I |E_I| ≤ 6 |Ω_λ|`
(`sum_ofReal_length_le_of_scale`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

variable {Ω : Set ℝ} {ℓ : ℕ}

/-- For `I` with `2^ℓ I ⊂ Ω`, every point outside `Ω` is at distance `≥ 2^ℓ |I|/2` from `c(I)`. -/
theorem Dyadic.le_abs_sub_center_of_dilate_subset {I : Dyadic} (h : I.dilate ((2 : ℝ) ^ ℓ) ⊆ Ω)
    {y : ℝ} (hy : y ∉ Ω) : (2 : ℝ) ^ ℓ * I.length / 2 ≤ |y - I.center| := by
  by_contra hlt
  rw [not_le, abs_lt] at hlt
  exact hy (h ⟨by linarith [hlt.1], by linarith [hlt.2]⟩)

/-- The middle half `E_I = (1/2) I` of `I ∈ 𝓘_ℓ`: points `x` of `E_I` have
`2^ℓ |I|/4 ≤ dist(x, ℝ ∖ Ω) ≤ (5/4) 2^ℓ |I|`. -/
theorem Dyadic.infDist_bounds {I : Dyadic} (h1 : I.dilate ((2 : ℝ) ^ ℓ) ⊆ Ω)
    (h2 : ¬ I.dilate ((2 : ℝ) ^ (ℓ + 1)) ⊆ Ω) {x : ℝ} (hx : x ∈ I.dilate (1 / 2)) :
    (2 : ℝ) ^ ℓ * I.length / 4 ≤ infDist x Ωᶜ ∧ infDist x Ωᶜ ≤ 5 * (2 ^ ℓ * I.length) / 4 := by
  have hL := I.length_pos
  have h2l : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
  have hxc : |x - I.center| ≤ I.length / 4 := by
    obtain ⟨a, b⟩ := hx
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨y₀, hy₀, hy₀Ω⟩ := Set.not_subset.1 h2
  have hy₀c := Dyadic.abs_sub_center_le_of_mem_dilate_succ hy₀
  have hne : Ωᶜ.Nonempty := ⟨y₀, hy₀Ω⟩
  constructor
  · rw [Metric.le_infDist hne]
    intro y hy
    have h3 := Dyadic.le_abs_sub_center_of_dilate_subset h1 hy
    have h4 : |y - I.center| ≤ |y - x| + |x - I.center| := by
      have := abs_add_le (y - x) (x - I.center)
      simpa using this
    rw [Real.dist_eq, abs_sub_comm]
    nlinarith
  · refine (Metric.infDist_le_dist_of_mem hy₀Ω).trans ?_
    rw [Real.dist_eq]
    have h4 : |x - y₀| ≤ |x - I.center| + |I.center - y₀| := by
      have := abs_add_le (x - I.center) (I.center - y₀)
      simpa using this
    rw [abs_sub_comm I.center y₀] at h4
    nlinarith

open Classical in
/-- **At most three intervals `I ∈ 𝒥` have `x ∈ E_I`** (`𝒥 ⊆ 𝓘_ℓ`). -/
theorem pointwise_card_le_three (𝒥 : Finset Dyadic) (h1 : ∀ I ∈ 𝒥, I.dilate ((2 : ℝ) ^ ℓ) ⊆ Ω)
    (h2 : ∀ I ∈ 𝒥, ¬ I.dilate ((2 : ℝ) ^ (ℓ + 1)) ⊆ Ω) (x : ℝ) :
    (𝒥.filter fun I => x ∈ I.dilate (1 / 2)).card ≤ 3 := by
  set 𝒥x := 𝒥.filter fun I => x ∈ I.dilate (1 / 2) with h𝒥x
  rcases 𝒥x.eq_empty_or_nonempty with he | hne
  · rw [he]; simp
  obtain ⟨I₀, hI₀, hmin⟩ := Finset.exists_min_image 𝒥x Dyadic.k hne
  have hmem : ∀ I ∈ 𝒥x, I ∈ 𝒥 ∧ x ∈ I.dilate (1 / 2) := fun I hI => Finset.mem_filter.1 hI
  -- every `I ∈ 𝒥x` has `I₀.k ≤ I.k ≤ I₀.k + 2`
  have hrange : ∀ I ∈ 𝒥x, I.k ∈ Finset.Icc I₀.k (I₀.k + 2) := by
    intro I hI
    refine Finset.mem_Icc.2 ⟨hmin I hI, ?_⟩
    obtain ⟨hI𝒥, hxI⟩ := hmem I hI
    obtain ⟨hI₀𝒥, hxI₀⟩ := hmem I₀ hI₀
    have hb := Dyadic.infDist_bounds (h1 I hI𝒥) (h2 I hI𝒥) hxI
    have hb₀ := Dyadic.infDist_bounds (h1 I₀ hI₀𝒥) (h2 I₀ hI₀𝒥) hxI₀
    have h2l : (0 : ℝ) < 2 ^ ℓ := by positivity
    -- `|I| ≤ 5 |I₀|`
    have hle : I.length ≤ 5 * I₀.length := by
      have : (2 : ℝ) ^ ℓ * I.length / 4 ≤ 5 * (2 ^ ℓ * I₀.length) / 4 := hb.1.trans hb₀.2
      nlinarith
    have hlt : (2 : ℝ) ^ I.k < 2 ^ (I₀.k + 3) := by
      have e : (2 : ℝ) ^ (I₀.k + 3) = 8 * 2 ^ I₀.k := by
        rw [zpow_add₀ (by norm_num)]; norm_num; ring
      rw [e]
      have : (0 : ℝ) < 2 ^ I₀.k := zpow_pos (by norm_num) _
      exact lt_of_le_of_lt hle (by unfold Dyadic.length at *; nlinarith)
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 hlt
    omega
  have hinj : Set.InjOn Dyadic.k (𝒥x : Set Dyadic) := by
    intro I hI I' hI' hk
    have hxI : x ∈ I.toSet := by
      have := (hmem I hI).2
      exact (I.dilate_mono (by norm_num : (1 / 2 : ℝ) ≤ 1)) this |> fun h => by
        rw [Dyadic.dilate_one] at h; exact h
    have hxI' : x ∈ I'.toSet := by
      have := (hmem I' hI').2
      exact (I'.dilate_mono (by norm_num : (1 / 2 : ℝ) ≤ 1)) this |> fun h => by
        rw [Dyadic.dilate_one] at h; exact h
    exact Dyadic.eq_of_k_eq_of_mem hk hxI hxI'
  calc 𝒥x.card ≤ (Finset.Icc I₀.k (I₀.k + 2)).card :=
        Finset.card_le_card_of_injOn Dyadic.k (fun I hI => hrange I hI) hinj
    _ = 3 := by rw [Int.card_Icc]; omega

/-- **The sum over intervals and scales, packing** ([O+] L2538-L2542): if
`𝒥` is a finite set of dyadic intervals with `2^ℓ I ⊂ Ω` and `2^{ℓ+1} I ⊄ Ω` for each `I ∈ 𝒥` then
`∑_{I ∈ 𝒥} |I| ≤ 6 |Ω|`. -/
theorem sum_ofReal_length_le_of_scale (𝒥 : Finset Dyadic)
    (h1 : ∀ I ∈ 𝒥, I.dilate ((2 : ℝ) ^ ℓ) ⊆ Ω)
    (h2 : ∀ I ∈ 𝒥, ¬ I.dilate ((2 : ℝ) ^ (ℓ + 1)) ⊆ Ω) (hΩ : MeasurableSet Ω) :
    ∑ I ∈ 𝒥, ENNReal.ofReal I.length ≤ 6 * volume Ω := by
  classical
  have hE : ∀ I : Dyadic, MeasurableSet (I.dilate (1 / 2)) := fun I => I.measurableSet_dilate _
  have hvol : ∀ I ∈ 𝒥, ENNReal.ofReal I.length = 2 * volume (I.dilate (1 / 2)) := by
    intro I _
    rw [Dyadic.volume_dilate, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring
  have hsub : ∀ I ∈ 𝒥, I.dilate (1 / 2) ⊆ Ω := fun I hI x hx => by
    have h3 : I.dilate (1 / 2) ⊆ I.dilate 1 := I.dilate_mono (by norm_num)
    have h4 : I.dilate 1 ⊆ I.dilate ((2 : ℝ) ^ ℓ) := I.dilate_mono (one_le_pow₀ (by norm_num))
    exact h1 I hI (h4 (h3 hx))
  have hsum : ∑ I ∈ 𝒥, volume (I.dilate (1 / 2)) ≤ 3 * volume Ω := by
    calc ∑ I ∈ 𝒥, volume (I.dilate (1 / 2))
        = ∫⁻ x, ∑ I ∈ 𝒥, (I.dilate (1 / 2)).indicator (fun _ => (1 : ℝ≥0∞)) x := by
          rw [lintegral_finsetSum _ (fun I _ => measurable_const.indicator (hE I))]
          refine Finset.sum_congr rfl fun I _ => ?_
          rw [lintegral_indicator (hE I), setLIntegral_const, one_mul]
      _ ≤ ∫⁻ x, Ω.indicator (fun _ => (3 : ℝ≥0∞)) x := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ Ω
          · rw [Set.indicator_of_mem hx]
            have hc := pointwise_card_le_three 𝒥 h1 h2 x
            calc ∑ I ∈ 𝒥, (I.dilate (1 / 2)).indicator (fun _ => (1 : ℝ≥0∞)) x
                = ∑ I ∈ 𝒥, if x ∈ I.dilate (1 / 2) then (1 : ℝ≥0∞) else 0 := by
                  refine Finset.sum_congr rfl fun I _ => ?_
                  simp only [Set.indicator_apply]
              _ = ((𝒥.filter fun I => x ∈ I.dilate (1 / 2)).card : ℝ≥0∞) := by
                  rw [Finset.sum_boole]
              _ ≤ 3 := by exact_mod_cast hc
          · rw [Set.indicator_of_notMem hx]
            have : ∀ I ∈ 𝒥, (I.dilate (1 / 2)).indicator (fun _ => (1 : ℝ≥0∞)) x = 0 := by
              intro I hI
              exact Set.indicator_of_notMem (fun hxI => hx (hsub I hI hxI)) _
            rw [Finset.sum_eq_zero this]
      _ = 3 * volume Ω := by
          rw [lintegral_indicator hΩ, setLIntegral_const, mul_comm]
  calc ∑ I ∈ 𝒥, ENNReal.ofReal I.length = ∑ I ∈ 𝒥, 2 * volume (I.dilate (1 / 2)) :=
        Finset.sum_congr rfl hvol
    _ = 2 * ∑ I ∈ 𝒥, volume (I.dilate (1 / 2)) := by rw [Finset.mul_sum]
    _ ≤ 2 * (3 * volume Ω) := by gcongr
    _ = 6 * volume Ω := by rw [← mul_assoc]; norm_num

end PrimeCarleson.Proof.Oplus

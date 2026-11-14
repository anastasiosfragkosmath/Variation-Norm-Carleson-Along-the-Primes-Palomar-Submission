module

public import PrimeCarleson.Frozen.RVariationOn
public import PrimeCarleson.Frozen.PartialFourierIntegral
public import PrimeCarleson.Proof.Common.Variation
public import PrimeCarleson.Proof.Paper.P4a.LpCount

/-!
# The Euclidean input and the variation toolkit

Source: main paper `l:varcar`, `l:varcarZ`, L1777–L1812, and `p:disc`, `c:disc`, L2932–L3000.

**The `[O+]` input.** `OplusVariationBound` is, as a `Prop`, *exactly the statement* of the
theorem `PrimeCarleson.variation_norm_carleson_real`
(`PrimeCarleson/Frozen/VariationNormCarlesonReal.lean`, `[O+]` Theorem 1.2): for `r > 2` and
`r' < p < ∞` there is `C` with `‖ ‖𝒮[f](·, x)‖_{V^r_ξ} ‖_{L^p(dx)} ≤ C ‖f‖_{L^p}` for every Schwartz
`f`. Every theorem of `P7/` that consumes
the Euclidean variational Carleson estimate takes `hO : OplusVariationBound` as a hypothesis (the
*conditional theorems*). Since `variation_norm_carleson_real` is proved, `OplusVariationBound` holds
by `fun r hr p hp => variation_norm_carleson_real r hr p hp`.

This file also contains the elementary facts about `V^r` and `ℓ^p(ℤ)` used throughout:

* `rVariationOn_eq_iSup_finset`: `V^r` over `S` is the supremum of `V^r` over finite `T ⊆ S`;
* `eLpNorm_count_iSup_le`: the `ℓ^p(ℤ)` norm of a pointwise directed supremum is at most the
  supremum of the norms (the "monotone convergence over finite `T`" of the paper);
* `rVariationOn_comp_monotone_le`: `V^r(a ∘ κ) ≤ V^r(a)` for continuous `a` and monotone `κ`;
* `rVariationOn_const_sub_shift_le`: `V^r(λ ↦ G - a(x + λ) : S) ≤ V^r(a)`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.MswTransference

/-- **The `[O+]` input as a `Prop`**: the statement of the theorem
`PrimeCarleson.variation_norm_carleson_real` ([O+] Theorem 1.2, the variational Carleson theorem
in the partial-Fourier-integral form). Conditional theorems of `P7/` take
`hO : OplusVariationBound`. -/
def OplusVariationBound : Prop :=
  ∀ r : ℝ, 2 < r → ∀ p : ℝ, r / (r - 1) < p → ∃ C : ℝ, ∀ f : 𝓢(ℝ, ℂ),
    eLpNorm (fun x => rVariationOn r Set.univ (fun ξ => partialFourierIntegral f ξ x))
        (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) volume

/-! ### `V^r` over `S` is the supremum over finite subsets -/

/-- `V^r` over `S` is the supremum of `V^r` over the finite subsets `T ⊆ S`. -/
theorem rVariationOn_eq_iSup_finset (r : ℝ) (S : Set ℝ) (a : ℝ → ℂ) :
    rVariationOn r S a = ⨆ (T : Finset ℝ) (_ : (T : Set ℝ) ⊆ S), rVariationOn r (T : Set ℝ) a := by
  refine le_antisymm (rVariationOn_le fun J t hm hS => ?_)
    (iSup₂_le fun T hT => rVariationOn_mono_set hT a)
  classical
  refine le_iSup₂_of_le (Finset.univ.image t) ?_ ?_
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    exact hS i
  · exact le_rVariationOn hm fun i => by simp

/-- The `ℓ^p(ℤ)` norm of a pointwise directed supremum is at most the supremum of the norms
(`0 < p`): the monotone-convergence step of the reduction to finite sets of frequencies (Source:
main paper `l:varcarZ`, L1812, and `p:disc`, L2983–L2986). -/
theorem eLpNorm_count_iSup_le {ι : Type*} {F : ι → ℤ → ℝ≥0∞} {p : ℝ} (hp : 0 < p)
    (hdir : ∀ i j, ∃ k, ∀ n, F i n ≤ F k n ∧ F j n ≤ F k n) :
    eLpNorm (fun n => ⨆ i, F i n) (ENNReal.ofReal p) Measure.count ≤
      ⨆ i, eLpNorm (F i) (ENNReal.ofReal p) Measure.count := by
  have hmono : Monotone (fun x : ℝ≥0∞ => x ^ p) := ENNReal.monotone_rpow_of_nonneg hp.le
  have hcont : Continuous (fun x : ℝ≥0∞ => x ^ p) := ENNReal.continuous_rpow_const
  have hp' : 0 < 1 / p := one_div_pos.2 hp
  have hmono' : Monotone (fun x : ℝ≥0∞ => x ^ (1 / p)) := ENNReal.monotone_rpow_of_nonneg hp'.le
  have hcont' : Continuous (fun x : ℝ≥0∞ => x ^ (1 / p)) := ENNReal.continuous_rpow_const
  have h1 : ∀ n, (⨆ i, F i n) ^ p = ⨆ i, F i n ^ p := fun n =>
    hmono.map_iSup_of_continuousAt hcont.continuousAt (ENNReal.zero_rpow_of_pos hp)
  have h2 : ∑' n, ⨆ i, F i n ^ p = ⨆ i, ∑' n, F i n ^ p := by
    calc ∑' n, ⨆ i, F i n ^ p = ⨆ s : Finset ℤ, ∑ n ∈ s, ⨆ i, F i n ^ p :=
          ENNReal.tsum_eq_iSup_sum
      _ = ⨆ s : Finset ℤ, ⨆ i, ∑ n ∈ s, F i n ^ p := by
          refine iSup_congr fun s => ENNReal.finsetSum_iSup fun i j => ?_
          obtain ⟨k, hk⟩ := hdir i j
          exact ⟨k, fun n => ⟨hmono (hk n).1, hmono (hk n).2⟩⟩
      _ = ⨆ i, ⨆ s : Finset ℤ, ∑ n ∈ s, F i n ^ p := iSup_comm
      _ = ⨆ i, ∑' n, F i n ^ p := iSup_congr fun i => ENNReal.tsum_eq_iSup_sum.symm
  rw [eLpNorm_count_eq_tsum_enn _ hp]
  simp_rw [eLpNorm_count_eq_tsum_enn _ hp]
  simp_rw [h1]
  rw [h2]
  exact (hmono'.map_iSup_of_continuousAt hcont'.continuousAt
    (ENNReal.zero_rpow_of_pos hp')).le

/-! ### Reparametrizations -/

/-- **Monotone reparametrization**: for a continuous `a` and a (not necessarily strictly)
monotone `κ`, `V^r(a ∘ κ : S) ≤ V^r(a)`. (A chain `t₀ < ⋯ < t_J` is sent to the weakly
increasing chain `κ t_i`, which is approximated by the strictly increasing chains
`κ t_i + iε`, and `a` is continuous.) -/
theorem rVariationOn_comp_monotone_le {r : ℝ} {a : ℝ → ℂ} (ha : Continuous a)
    {κ : ℝ → ℝ} (hκ : Monotone κ) (S : Set ℝ) :
    rVariationOn r S (fun t => a (κ t)) ≤ rVariationOn r Set.univ a := by
  refine rVariationOn_le fun J t hm _ => ?_
  let u : ℝ → Fin (J + 1) → ℝ := fun ε j => κ (t j) + ((j : ℕ) : ℝ) * ε
  let L : ℝ → ℝ≥0∞ := fun ε =>
    (∑ i : Fin J, ‖a (u ε i.castSucc) - a (u ε i.succ)‖ₑ ^ r) ^ (1 / r)
  have hbound : ∀ ε : ℝ, 0 < ε → L ε ≤ rVariationOn r Set.univ a := by
    intro ε hε
    have hs : StrictMono (u ε) := by
      intro j k hjk
      have h1 : κ (t j) ≤ κ (t k) := hκ (hm.monotone hjk.le)
      have h2 : ((j : ℕ) : ℝ) < (k : ℕ) := by exact_mod_cast hjk
      have h3 : ((j : ℕ) : ℝ) * ε < ((k : ℕ) : ℝ) * ε := mul_lt_mul_of_pos_right h2 hε
      simp only [u]
      linarith
    exact le_rVariationOn (r := r) (S := Set.univ) (a := a) hs fun _ => Set.mem_univ _
  have hcont : Continuous L := by
    refine ENNReal.continuous_rpow_const.comp (continuous_finsetSum _ fun i _ => ?_)
    refine ENNReal.continuous_rpow_const.comp ?_
    have hu : ∀ j : Fin (J + 1), Continuous fun ε : ℝ => u ε j := fun j => by
      simp only [u]
      fun_prop
    exact ((ha.comp (hu _)).sub (ha.comp (hu _))).enorm
  have hlim : Tendsto L (𝓝[>] 0) (𝓝 (L 0)) := (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have h0 : L 0 ≤ rVariationOn r Set.univ a :=
    le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => hbound ε hε)
  simpa [L, u] using h0

/-- Constants cancel in the `r`-variation, and a shift of the index is a reparametrization:
`V^r(λ ↦ G - a(x + λ) : S) ≤ V^r(a)`. -/
theorem rVariationOn_const_sub_shift_le {r : ℝ} (S : Set ℝ) (G : ℂ) (a : ℝ → ℂ) (x : ℝ) :
    rVariationOn r S (fun lam => G - a (x + lam)) ≤ rVariationOn r Set.univ a := by
  refine rVariationOn_le fun J t hm _ => ?_
  have hs : StrictMono fun j : Fin (J + 1) => x + t j := fun j k hjk => by
    have := hm hjk
    simp only
    linarith
  have h := le_rVariationOn (r := r) (S := Set.univ) (a := a) hs fun _ => Set.mem_univ _
  refine le_trans (le_of_eq ?_) h
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sub_sub_sub_cancel_left, enorm_sub_rev]

end PrimeCarleson.Proof.Paper

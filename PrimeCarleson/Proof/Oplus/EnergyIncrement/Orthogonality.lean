module

public import PrimeCarleson.Proof.Oplus.EnergyIncrement.Disjointness
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.TailWeight

/-!
# The interaction bound `etreeorth1` ([O+] L1526-L1553)

Source: [O+] `etreeorth1`, L1530–L1532 (L1526-L1553). Everything is proved for an arbitrary finite
subfamily `U ⊂ 𝔓` and arbitrary coefficients `c_P` (in particular `c_P = ⟨g, φ_P⟩`), so that the
same proof serves `f` (`squarebyfct`) and `f' = 1_{2^{ℓ+5}J} f`, a subsequence `S_{j(ν)}`
(`squarebyfctanalog`), the source's "exactly the same reasoning" (L1728-L1733).

With `N = 3` (so that `∫ w_I = 1`):

* `sum_sum_same_scale_le` (etreeorth1, L1530-L1553): `∑_{P,P' : |I'| = |I|} |c_P||c_{P'}||G_{PP'}| ≤
  K₀ ∑_P |c_P|²`, using `⟨φ_P, φ_{P'}⟩ = 0` unless `C₃ ω_u ∩ C₃ ω_{u'} ≠ ∅`, (separationprop2) and
  the Schwartz estimate.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- The Schwartz estimate `|⟨φ_P, φ_{P'}⟩| ≤ K₀ (|I|/|I'|)^{1/2} ⟨w_I, 1_{I'}⟩` for `|I'| ≤ |I|`
with the weight exponent `N = 3` (L1537-L1543). -/
def SchwartzBound (K₀ : ℝ) : Prop :=
  ∀ (ρ ρ' : Idx) (ch ch' : ProfileChoice) (P : Multitile ρ) (P' : Multitile ρ'),
    P'.I.length ≤ P.I.length →
    ‖pairing (P.wavePacket ch) (P'.wavePacket ch')‖ ≤
      K₀ * √(P.I.length / P'.I.length) * ∫ x in P'.I.toSet, P.I.weight 3 x

/-- The Schwartz estimate holds with some constant ([O+] `schwartzestimate`). -/
theorem exists_schwartzBound : ∃ K₀ : ℝ, 0 ≤ K₀ ∧ SchwartzBound K₀ :=
  Multitile.exists_norm_pairing_wavePacket_le 3

/-- `∫ w_I = 1` for `N = 3`. -/
theorem Dyadic.integral_weight_three (I : Dyadic) : ∫ x, I.weight 3 x = 1 := by
  rw [Dyadic.integral_weight (by norm_num)]; norm_num

section Vanishing

variable {ρ : Idx} {C₁ C₂ C₃ : ℝ}

/-- `⟨φ_P, φ_{P'}⟩ = 0` unless the closed `C₃`-dilates of `ω_u, ω_{u'}` meet (Plancherel and
`supp φ̂_P ⊂ C₃ ω_u`, L1549). -/
theorem pairing_eq_zero_of_not_near (hC : AdmissibleConstants C₁ C₂ C₃) (ch ch' : ProfileChoice)
    {P P' : Multitile ρ} (h : ¬ Multitile.Near C₃ P P') :
    pairing (P.wavePacket ch) (P'.wavePacket ch') = 0 := by
  have hd : Disjoint (P.ωu.dilate C₃) (P'.ωu.dilate C₃) :=
    Set.disjoint_left.2 fun x hx hx' => h (Multitile.Near.of_inter ⟨x, hx, hx'⟩)
  exact pairing_wavePacketOf_eq_zero_of_support ch.isProfile ch'.isProfile P.I P.ωu P'.I P'.ωu
    ((subset_tsupport _).trans (hC.packet_support ch P.I P.ωu))
    ((subset_tsupport _).trans (hC.packet_support ch' P'.I P'.ωu)) hd

/-- For `P, P'` of a separated family with `|I| = |I'|` and `ω_u ≠ ω_{u'}`,
`⟨φ_P, φ_{P'}⟩ = 0` (L1549: "`⟨φ_P, φ_{P'}⟩ = 0` unless `C₃ ω_u ∩ C₃ ω_{u'} ≠ ∅`", then
(separationprop2)). -/
theorem pairing_eq_zero_of_ωu_ne (hC : AdmissibleConstants C₁ C₂ C₃) {𝔓 : Finset (Multitile ρ)}
    (hsep : Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ))) (ch ch' : ProfileChoice)
    {P P' : Multitile ρ} (hP : P ∈ 𝔓) (hP' : P' ∈ 𝔓) (hlen : P.I.length = P'.I.length)
    (hne : P.ωu ≠ P'.ωu) : pairing (P.wavePacket ch) (P'.wavePacket ch') = 0 :=
  pairing_eq_zero_of_not_near hC ch ch' fun hnear =>
    hne (ωu_eq_of_near_of_I_length_eq hC hsep hP hP' hlen hnear)

end Vanishing

section Algebra

/-- The symmetrization step of the source: `∑_P ∑_{P' ∈ filter} a_P a_{P'} G_{PP'} ≤
∑_P a_P² ∑_{P' ∈ filter} G_{PP'}` for a symmetric relation and symmetric nonnegative `G`. -/
theorem sum_sum_filter_le {ι : Type*} (U : Finset ι) (R : ι → ι → Prop)
    [∀ P P', Decidable (R P P')] (hR : ∀ P P', R P P' → R P' P) (G : ι → ι → ℝ)
    (a' : ι → ℝ) (hG0 : ∀ P P', 0 ≤ G P P') (hG : ∀ P P', G P' P = G P P') :
    ∑ P ∈ U, ∑ P' ∈ U.filter (R P), a' P * a' P' * G P P' ≤
      ∑ P ∈ U, a' P ^ 2 * ∑ P' ∈ U.filter (R P), G P P' := by
  have h2 : ∀ P P', a' P * a' P' * G P P' ≤ (a' P ^ 2 * G P P' + a' P' ^ 2 * G P' P) / 2 := by
    intro P P'
    rw [hG P P']
    nlinarith [sq_nonneg (a' P - a' P'), hG0 P P']
  calc ∑ P ∈ U, ∑ P' ∈ U.filter (R P), a' P * a' P' * G P P'
      ≤ ∑ P ∈ U, ∑ P' ∈ U.filter (R P), (a' P ^ 2 * G P P' + a' P' ^ 2 * G P' P) / 2 :=
        Finset.sum_le_sum fun P _ => Finset.sum_le_sum fun P' _ => h2 P P'
    _ = (∑ P ∈ U, a' P ^ 2 * ∑ P' ∈ U.filter (R P), G P P' +
          ∑ P ∈ U, ∑ P' ∈ U.filter (R P), a' P' ^ 2 * G P' P) / 2 := by
        simp_rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = ∑ P ∈ U, a' P ^ 2 * ∑ P' ∈ U.filter (R P), G P P' := by
        have : ∑ P ∈ U, ∑ P' ∈ U.filter (R P), a' P' ^ 2 * G P' P =
            ∑ P ∈ U, a' P ^ 2 * ∑ P' ∈ U.filter (R P), G P P' := by
          simp_rw [Finset.sum_filter]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun P _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun P' _ => ?_
          by_cases h : R P P'
          · simp [h, hR P P' h]
          · by_cases h' : R P' P
            · exact absurd (hR P' P h') h
            · simp [h, h']
        rw [this]; ring

end Algebra

section SameScale

variable {ρ : Idx} {C₁ C₂ C₃ : ℝ}

/-- **The row sums of the same-scale interactions are at most `K₀`** (L1549-L1553): for `P ∈ 𝔓`
and `U ⊂ 𝔓` finite, `∑_{P' ∈ U, |I'| = |I|} |⟨φ_P, φ_{P'}⟩| ≤ K₀`. The only `P'` with a nonzero
interaction have `ω_{u'} = ω_u` (separationprop2) and then distinct `P'` have disjoint `I'`,
so the sum is at most `K₀ ∫ w_I = K₀`. -/
theorem sum_norm_pairing_same_scale_le (hC : AdmissibleConstants C₁ C₂ C₃)
    {𝔓 : Finset (Multitile ρ)} (hsep : Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)))
    {K₀ : ℝ} (hK₀0 : 0 ≤ K₀) (hK₀ : SchwartzBound K₀) (ch : ProfileChoice)
    {U : Finset (Multitile ρ)} (hU : (U : Set (Multitile ρ)) ⊆ 𝔓) {P : Multitile ρ} (hP : P ∈ 𝔓) :
    ∑ P' ∈ U.filter (fun P' => P'.I.length = P.I.length),
      ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖ ≤ K₀ := by
  classical
  set F := U.filter (fun P' => P'.I.length = P.I.length) with hF
  set F₀ := F.filter (fun P' => P'.ωu = P.ωu) with hF₀
  have hzero : ∀ P' ∈ F, P' ∉ F₀ → ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖ = 0 := by
    intro P' hP' hnF
    have h1 := Finset.mem_filter.1 hP'
    have hne : P.ωu ≠ P'.ωu := fun h =>
      hnF (Finset.mem_filter.2 ⟨hP', h.symm⟩)
    rw [pairing_eq_zero_of_ωu_ne hC hsep ch ch hP (hU h1.1) h1.2.symm hne, norm_zero]
  rw [← Finset.sum_subset (Finset.filter_subset _ _) fun P' hP' hnF => hzero P' hP' hnF]
  have hterm : ∀ P' ∈ F₀, ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖ ≤
      K₀ * ∫ x in P'.I.toSet, P.I.weight 3 x := by
    intro P' hP'
    have h1 := Finset.mem_filter.1 (Finset.mem_filter.1 hP').1
    have := hK₀ ρ ρ ch ch P P' (le_of_eq h1.2)
    rw [h1.2, div_self P.I.length_ne_zero, Real.sqrt_one, mul_one] at this
    exact this
  have hdisj : Set.Pairwise (F₀ : Set (Multitile ρ))
      (Function.onFun Disjoint fun P' => P'.I.toSet) := by
    intro P' hP' P'' hP'' hne
    have h1 := Finset.mem_filter.1 (Finset.mem_coe.1 hP')
    have h2 := Finset.mem_filter.1 (Finset.mem_coe.1 hP'')
    have h1' := (Finset.mem_filter.1 h1.1).2
    have h2' := (Finset.mem_filter.1 h2.1).2
    have hIne : P'.I ≠ P''.I := fun h => hne (Multitile.ext h (h1.2.trans h2.2.symm))
    exact Dyadic.disjoint_of_k_eq_of_ne (Dyadic.length_eq_iff.1 (h1'.trans h2'.symm)) hIne
  have hint : ∀ P' ∈ F₀, IntegrableOn (P.I.weight 3) P'.I.toSet := fun P' _ =>
    (P.I.integrable_weight (by norm_num)).integrableOn
  calc ∑ P' ∈ F₀, ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖
      ≤ ∑ P' ∈ F₀, K₀ * ∫ x in P'.I.toSet, P.I.weight 3 x := Finset.sum_le_sum hterm
    _ = K₀ * ∫ x in ⋃ P' ∈ F₀, P'.I.toSet, P.I.weight 3 x := by
        rw [← Finset.mul_sum, integral_biUnion_finset F₀ (fun P' _ => P'.I.measurableSet_toSet)
          hdisj hint]
    _ ≤ K₀ * ∫ x, P.I.weight 3 x := by
        apply mul_le_mul_of_nonneg_left _ hK₀0
        exact setIntegral_le_integral (P.I.integrable_weight (by norm_num))
          (Filter.Eventually.of_forall fun x => P.I.weight_nonneg 3 x)
    _ = K₀ := by rw [Dyadic.integral_weight_three, mul_one]

/-- **`etreeorth1`** ([O+] L1530-L1553), for an arbitrary finite subfamily `U ⊂ 𝔓` and arbitrary
coefficients: `∑_{P, P' ∈ U : |I'| = |I|} |c_P||c_{P'}||⟨φ_P, φ_{P'}⟩| ≤ K₀ ∑_P |c_P|²`. -/
theorem sum_sum_same_scale_le (hC : AdmissibleConstants C₁ C₂ C₃) {𝔓 : Finset (Multitile ρ)}
    (hsep : Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ))) {K₀ : ℝ} (hK₀0 : 0 ≤ K₀)
    (hK₀ : SchwartzBound K₀) (ch : ProfileChoice) {U : Finset (Multitile ρ)}
    (hU : (U : Set (Multitile ρ)) ⊆ 𝔓) (c : Multitile ρ → ℂ) :
    ∑ P ∈ U, ∑ P' ∈ U.filter (fun P' => P'.I.length = P.I.length),
      ‖c P‖ * ‖c P'‖ * ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖ ≤
      K₀ * ∑ P ∈ U, ‖c P‖ ^ 2 := by
  classical
  refine (sum_sum_filter_le U (fun P P' => P'.I.length = P.I.length)
    (fun P P' h => h.symm) (fun P P' => ‖pairing (P.wavePacket ch)
      (P'.wavePacket ch)‖) (fun P => ‖c P‖) (fun _ _ => norm_nonneg _)
    (fun P P' => norm_pairing_comm _ _)).trans ?_
  calc ∑ P ∈ U, ‖c P‖ ^ 2 * ∑ P' ∈ U.filter (fun P' => P'.I.length = P.I.length),
        ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖
      ≤ ∑ P ∈ U, ‖c P‖ ^ 2 * K₀ := Finset.sum_le_sum fun P hP =>
        mul_le_mul_of_nonneg_left (sum_norm_pairing_same_scale_le hC hsep hK₀0 hK₀ ch hU (hU hP))
          (by positivity)
    _ = K₀ * ∑ P ∈ U, ‖c P‖ ^ 2 := by rw [Finset.mul_sum]; simp_rw [mul_comm]

end SameScale

end PrimeCarleson.Proof.Oplus

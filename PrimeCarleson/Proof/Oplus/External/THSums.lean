module

public import PrimeCarleson.Proof.Oplus.TreeSmall.WeightSums
public import PrimeCarleson.Proof.Oplus.TreeSmall.Intervals

/-!
# Almost-diagonal sums over disjoint dyadic intervals

The geometric counting behind the near part of the tile-energy bound
(replacing the case distinctions (a), (b), (c) of Grafakos–Tao–Terwilleger by a Schur test),
Source: Grafakos–Tao–Terwilleger, L789–L1231.

For dyadic `I, J` put `W(I, J) = (1 + dist(I, J)/|I|)^{-2}` (`kerW`) and
`m(I, J) = (|J|/|I|)^2 W(I, J)` if `|J| ≤ |I|`, `m(I, J) = W(I, J)` otherwise (`kerM`).

* row sums (`I` fixed, `J` over a finite family of pairwise disjoint dyadic intervals, those larger
  than `I` disjoint from `I`): `∑_J m(I, J) ≤ 25` (`sum_kerM_le_row`);
* column sums (`J` fixed, `I` over distinct dyadic intervals, those smaller than `J` disjoint from
  `J`): `∑_I |I| m(I, J) ≤ 100 |J|` (`sum_length_mul_kerM_le_col`);
* Schur: `∑_I |I| (∑_J m(I, J))² ≤ 2500 ∑_J |J|` (`sum_length_mul_sq_kerM_le`).
-/

@[expose] public noncomputable section

open MeasureTheory Set

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-! ### Elementary lemmas -/

/-- `a^{-2} ≤ k² b^{-2}` when `b ≤ k a`. -/
theorem zpow_neg_two_le_mul {a b k : ℝ} (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    (h : b ≤ k * a) : a ^ (-2 : ℤ) ≤ k ^ 2 * b ^ (-2 : ℤ) := by
  rw [zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat]
  have h2 : b ^ 2 ≤ (k * a) ^ 2 := pow_le_pow_left₀ hb.le h 2
  have h3 : ((k * a) ^ 2)⁻¹ ≤ (b ^ 2)⁻¹ := inv_anti₀ (by positivity) h2
  have h4 : (a ^ 2)⁻¹ = k ^ 2 * ((k * a) ^ 2)⁻¹ := by
    have : k ≠ 0 := hk.ne'
    have : a ≠ 0 := ha.ne'
    field_simp
  rw [h4]
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

namespace Dyadic

/-- Disjoint dyadic intervals are ordered on the line. -/
theorem right_le_left_or_right_le_left_of_disjoint {I J : Dyadic}
    (h : Disjoint I.toSet J.toSet) : I.right ≤ J.left ∨ J.right ≤ I.left := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨h1, h2⟩ := hcon
  exact Set.disjoint_left.1 h
    (show max I.left J.left ∈ I.toSet from ⟨le_max_left _ _, max_lt I.left_lt_right h1⟩)
    (show max I.left J.left ∈ J.toSet from ⟨le_max_right _ _, max_lt h2 J.left_lt_right⟩)

/-- If `J` lies to the right of `I`, `dist(I, J) = J.left - I.right`. -/
theorem dist_eq_of_right_le {I J : Dyadic} (h : I.right ≤ J.left) :
    I.dist J = J.left - I.right := by
  have h1 := I.left_lt_right
  have h2 := J.left_lt_right
  unfold dist
  rw [max_eq_right (by rw [max_eq_left (by linarith)]; linarith), max_eq_left (by linarith)]

/-- If `J` lies to the left of `I`, `dist(I, J) = I.left - J.right`. -/
theorem dist_eq_of_right_le' {I J : Dyadic} (h : J.right ≤ I.left) :
    I.dist J = I.left - J.right := by
  have h1 := I.left_lt_right
  have h2 := J.left_lt_right
  unfold dist
  rw [max_eq_right (by rw [max_eq_right (by linarith)]; linarith), max_eq_right (by linarith)]

end Dyadic

/-- The weight `W(I, J) = (1 + dist(I, J)/|I|)^{-2}`. -/
def kerW (I J : Dyadic) : ℝ := (1 + I.dist J / I.length) ^ (-2 : ℤ)

/-- The kernel `m(I, J) = (|J|/|I|)^2 W(I, J)` for `|J| ≤ |I|` and `W(I, J)` otherwise. -/
def kerM (I J : Dyadic) : ℝ :=
  (if J.length ≤ I.length then (J.length / I.length) ^ 2 else 1) * kerW I J

/-- `W(I, J) > 0`. -/
theorem kerW_pos (I J : Dyadic) : 0 < kerW I J := by
  have := I.length_pos
  have := I.dist_nonneg J
  unfold kerW; positivity

/-- `m(I, J) ≥ 0`. -/
theorem kerM_nonneg (I J : Dyadic) : 0 ≤ kerM I J := by
  have := kerW_pos I J
  unfold kerM
  split_ifs <;> positivity

/-- `W(I, J) ≤ (25/4) (1 + |x - c(I)|/|I|)^{-2}` if `|x - c(I)| ≤ dist(I, J) + (3/2)|I|`. -/
theorem kerW_le_weight_of_abs_le {I J : Dyadic} {x : ℝ}
    (h : |x - I.center| ≤ I.dist J + 3 / 2 * I.length) :
    kerW I J ≤ 25 / 4 * (1 + |x - I.center| / I.length) ^ (-2 : ℤ) := by
  have hI := I.length_pos
  have hd := I.dist_nonneg J
  have hb : 1 + |x - I.center| / I.length ≤ 5 / 2 * (1 + I.dist J / I.length) := by
    have h3 : |x - I.center| / I.length ≤ 3 / 2 + I.dist J / I.length := by
      rw [div_le_iff₀ hI]
      have : (3 / 2 + I.dist J / I.length) * I.length = 3 / 2 * I.length + I.dist J := by
        field_simp
      rw [this]; linarith
    have h4 : 0 ≤ I.dist J / I.length := div_nonneg hd hI.le
    linarith
  have := zpow_neg_two_le_mul (a := 1 + I.dist J / I.length) (b := 1 + |x - I.center| / I.length)
    (k := 5 / 2) (by positivity) (by positivity) (by norm_num) hb
  rw [show (5 / 2 : ℝ) ^ 2 = 25 / 4 by norm_num] at this
  exact this

/-- For `x ∈ J` with `|J| ≤ |I|`: `W(I, J) ≤ (25/4) (1 + |x - c(I)|/|I|)^{-2}`. -/
theorem kerW_le_weight_of_length_le {I J : Dyadic} (hle : J.length ≤ I.length) {x : ℝ}
    (hx : x ∈ J.toSet) :
    kerW I J ≤ 25 / 4 * (1 + |x - I.center| / I.length) ^ (-2 : ℤ) := by
  have h1 := Dyadic.abs_sub_center_le_dist (I := I) hx
  exact kerW_le_weight_of_abs_le (by linarith)

/-! ### Row sums -/

/-- `∑_{J small} |J| W(I, J) ≤ (25/4) · 2|I|`: integral comparison over disjoint `J`. -/
theorem sum_length_mul_kerW_le_small (I : Dyadic) (S : Finset Dyadic)
    (hdisj : (S : Set Dyadic).PairwiseDisjoint Dyadic.toSet)
    (hsmall : ∀ J ∈ S, J.length ≤ I.length) :
    ∑ J ∈ S, J.length * kerW I J ≤ 25 / 4 * (2 * I.length) := by
  have hI := I.length_pos
  set w : ℝ → ℝ := fun y => (1 + |y - I.center| / I.length) ^ (-2 : ℤ) with hw
  have hwint : Integrable w := by
    have := integrable_one_add_abs_div_zpow (N := 2) (le_refl 2) I.center hI
    simpa [hw] using this
  have hwnn : ∀ y, 0 ≤ w y := fun y => by simp only [hw]; positivity
  have hA : ∀ J ∈ S, J.length * kerW I J ≤ 25 / 4 * ∫ y in J.toSet, w y := by
    intro J hJ
    have hfin : volume J.toSet ≠ ⊤ := by rw [Dyadic.volume_toSet]; exact ENNReal.ofReal_ne_top
    have h1 : ∀ y ∈ J.toSet, kerW I J ≤ 25 / 4 * w y := fun y hy =>
      kerW_le_weight_of_length_le (hsmall J hJ) hy
    have h2 := setIntegral_mono_on (integrableOn_const hfin)
      ((hwint.const_mul (25 / 4)).integrableOn) J.measurableSet_toSet h1
    rw [setIntegral_const, smul_eq_mul, Dyadic.volume_real_toSet, integral_const_mul] at h2
    linarith
  calc ∑ J ∈ S, J.length * kerW I J ≤ ∑ J ∈ S, 25 / 4 * ∫ y in J.toSet, w y :=
        Finset.sum_le_sum hA
    _ = 25 / 4 * ∫ y in ⋃ J ∈ S, J.toSet, w y := by
        rw [← Finset.mul_sum, integral_biUnion_finset S (fun J _ => J.measurableSet_toSet) hdisj
          (fun J _ => hwint.integrableOn)]
    _ ≤ 25 / 4 * ∫ y, w y :=
        mul_le_mul_of_nonneg_left (setIntegral_le_integral hwint (Filter.Eventually.of_forall hwnn))
          (by norm_num)
    _ = 25 / 4 * (2 * I.length) := by
        have := integral_one_add_abs_div_zpow (N := 2) (le_refl 2) I.center hI
        simp only [hw]
        rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, this]
        norm_num
        ring

/-- **Row sum, large `J`**: for pairwise disjoint `J` with `|J| ≥ |I|` and `J ∩ I = ∅`,
`∑_J W(I, J) ≤ 25/2`. -/
theorem sum_kerW_le_large (I : Dyadic) (S : Finset Dyadic)
    (hdisj : (S : Set Dyadic).PairwiseDisjoint Dyadic.toSet)
    (hlarge : ∀ J ∈ S, I.length ≤ J.length) (hdisjI : ∀ J ∈ S, Disjoint I.toSet J.toSet) :
    ∑ J ∈ S, kerW I J ≤ 25 / 4 * 2 := by
  classical
  have hI := I.length_pos
  set w : ℝ → ℝ := fun y => (1 + |y - I.center| / I.length) ^ (-2 : ℤ) with hw
  have hwint : Integrable w := by
    have := integrable_one_add_abs_div_zpow (N := 2) (le_refl 2) I.center hI
    simpa [hw] using this
  have hwnn : ∀ y, 0 ≤ w y := fun y => by simp only [hw]; positivity
  -- the sub-interval of length `|I|` of `J` next to `I`
  set sub : Dyadic → Set ℝ := fun J =>
    if I.right ≤ J.left then Ico J.left (J.left + I.length) else Ico (J.right - I.length) J.right
    with hsub
  have hsubJ : ∀ J ∈ S, sub J ⊆ J.toSet := by
    intro J hJ y hy
    have hl := hlarge J hJ
    have hr := J.right_eq
    simp only [hsub] at hy
    split_ifs at hy with h
    · exact ⟨hy.1, by linarith [hy.2]⟩
    · exact ⟨by linarith [hy.1], hy.2⟩
  have hvol : ∀ J, volume (sub J) = ENNReal.ofReal I.length := by
    intro J
    simp only [hsub]
    split_ifs
    · rw [Real.volume_Ico]; congr 1; ring
    · rw [Real.volume_Ico]; congr 1; ring
  have hmeas : ∀ J, MeasurableSet (sub J) := by
    intro J; simp only [hsub]; split_ifs <;> exact measurableSet_Ico
  have hdisjsub : (S : Set Dyadic).PairwiseDisjoint sub := by
    intro J hJ J' hJ' hne
    exact (hdisj hJ hJ' hne).mono (hsubJ J hJ) (hsubJ J' hJ')
  have hA : ∀ J ∈ S, I.length * kerW I J ≤ 25 / 4 * ∫ y in sub J, w y := by
    intro J hJ
    have hfin : volume (sub J) ≠ ⊤ := by rw [hvol]; exact ENNReal.ofReal_ne_top
    have h1 : ∀ y ∈ sub J, kerW I J ≤ 25 / 4 * w y := by
      intro y hy
      apply kerW_le_weight_of_abs_le
      have hI' := I.right_eq
      have hI'' := I.center_eq
      simp only [hsub] at hy
      split_ifs at hy with h
      · rw [Dyadic.dist_eq_of_right_le h]
        have hy1 := hy.1
        have hy2 := hy.2
        rw [abs_le]; constructor <;> linarith
      · have hdj := Dyadic.right_le_left_or_right_le_left_of_disjoint (hdisjI J hJ)
        have hJI : J.right ≤ I.left := by
          rcases hdj with h' | h'
          · exact absurd h' h
          · exact h'
        rw [Dyadic.dist_eq_of_right_le' hJI]
        have hy1 := hy.1
        have hy2 := hy.2
        rw [abs_le]; constructor <;> linarith
    have h2 := setIntegral_mono_on (integrableOn_const hfin)
      ((hwint.const_mul (25 / 4)).integrableOn) (hmeas J) h1
    rw [setIntegral_const, smul_eq_mul, integral_const_mul] at h2
    have hreal : volume.real (sub J) = I.length := by
      simp [Measure.real, hvol, hI.le]
    rw [hreal] at h2
    exact h2
  have hsum : I.length * ∑ J ∈ S, kerW I J ≤ 25 / 4 * (2 * I.length) := by
    rw [Finset.mul_sum]
    calc ∑ J ∈ S, I.length * kerW I J ≤ ∑ J ∈ S, 25 / 4 * ∫ y in sub J, w y :=
          Finset.sum_le_sum hA
      _ = 25 / 4 * ∫ y in ⋃ J ∈ S, sub J, w y := by
          rw [← Finset.mul_sum, integral_biUnion_finset S (fun J _ => hmeas J) hdisjsub
            (fun J _ => hwint.integrableOn)]
      _ ≤ 25 / 4 * ∫ y, w y :=
          mul_le_mul_of_nonneg_left
            (setIntegral_le_integral hwint (Filter.Eventually.of_forall hwnn)) (by norm_num)
      _ = 25 / 4 * (2 * I.length) := by
          have := integral_one_add_abs_div_zpow (N := 2) (le_refl 2) I.center hI
          simp only [hw]
          rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, this]
          norm_num
          ring
  have : ∑ J ∈ S, kerW I J ≤ 25 / 4 * 2 := by
    by_contra hcon
    rw [not_le] at hcon
    have := mul_lt_mul_of_pos_left hcon hI
    nlinarith
  exact this

/-! ### Geometric sums over scales -/

/-- `∑_{k ∈ K} (1/2)^{k - k₀} ≤ 2` for a finite set of integers `k ≥ k₀`. -/
theorem sum_geom_ge {K : Finset ℤ} {k₀ : ℤ} (h : ∀ k ∈ K, k₀ ≤ k) :
    ∑ k ∈ K, ((1 : ℝ) / 2) ^ (k - k₀).toNat ≤ 2 := by
  classical
  have hinj : Set.InjOn (fun k : ℤ => (k - k₀).toNat) K := by
    intro a ha b hb hab
    have := h a ha
    have := h b hb
    simp only at hab
    omega
  rw [← Finset.sum_image (f := fun j : ℕ => ((1 : ℝ) / 2) ^ j) hinj]
  refine (summable_geometric_two.sum_le_tsum _ (fun _ _ => by positivity)).trans ?_
  rw [tsum_geometric_two]

/-- `∑_{k ∈ K} (1/2)^{k₀ - k} ≤ 2` for a finite set of integers `k ≤ k₀`. -/
theorem sum_geom_le {K : Finset ℤ} {k₀ : ℤ} (h : ∀ k ∈ K, k ≤ k₀) :
    ∑ k ∈ K, ((1 : ℝ) / 2) ^ (k₀ - k).toNat ≤ 2 := by
  classical
  have hinj : Set.InjOn (fun k : ℤ => (k₀ - k).toNat) K := by
    intro a ha b hb hab
    have := h a ha
    have := h b hb
    simp only at hab
    omega
  rw [← Finset.sum_image (f := fun j : ℕ => ((1 : ℝ) / 2) ^ j) hinj]
  refine (summable_geometric_two.sum_le_tsum _ (fun _ _ => by positivity)).trans ?_
  rw [tsum_geometric_two]

/-- `|J| / 2^k = (1/2)^{k - k_J}` for `k ≥ k_J`. -/
theorem length_div_two_zpow {J : Dyadic} {k : ℤ} (hk : J.k ≤ k) :
    J.length / (2 : ℝ) ^ k = ((1 : ℝ) / 2) ^ (k - J.k).toNat := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k = J.k + n := ⟨(k - J.k).toNat, by omega⟩
  have : (k - J.k).toNat = n := by omega
  rw [this, hn, zpow_add₀ (by norm_num), zpow_natCast]
  unfold Dyadic.length
  rw [one_div, inv_pow]
  field_simp

/-- `2^k / |J| = (1/2)^{k_J - k}` for `k ≤ k_J`. -/
theorem two_zpow_div_length {J : Dyadic} {k : ℤ} (hk : k ≤ J.k) :
    (2 : ℝ) ^ k / J.length = ((1 : ℝ) / 2) ^ (J.k - k).toNat := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, J.k = k + n := ⟨(J.k - k).toNat, by omega⟩
  have : (J.k - k).toNat = n := by omega
  rw [this]
  unfold Dyadic.length
  rw [hn, zpow_add₀ (by norm_num), zpow_natCast, one_div, inv_pow]
  field_simp

/-! ### Column sums -/

/-- One scale `ℓ ≥ |J|`: `∑_{I of scale ℓ} W(I, J) ≤ 225/8`. -/
theorem sum_kerW_scale_le_large {ι : Type*} (F : Finset ι) (Iof : ι → Dyadic) (J : Dyadic)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hlen : ∀ i ∈ F, (Iof i).length = ℓ) (hJℓ : J.length ≤ ℓ)
    (hdisj : (F : Set ι).PairwiseDisjoint fun i => (Iof i).toSet) :
    ∑ i ∈ F, kerW (Iof i) J ≤ 225 / 8 := by
  have hbound := sum_one_add_abs_zpow_le F Iof hℓ hlen hdisj (N := 2) (le_refl 2) J.center
    (d := 0) le_rfl (fun i _ y _ => abs_nonneg _)
  have hterm : ∀ i ∈ F, kerW (Iof i) J ≤
      25 / 4 * (1 + |(Iof i).center - J.center| / ℓ) ^ (-((2 : ℕ) : ℤ)) := by
    intro i hi
    have hli := hlen i hi
    have h1 := Dyadic.abs_sub_center_le_dist (I := Iof i) (x := J.center) J.center_mem_toSet
    rw [abs_sub_comm] at h1
    have := kerW_le_weight_of_abs_le (I := Iof i) (J := J) (x := J.center) (by
      rw [abs_sub_comm]; rw [hli] at h1 ⊢; linarith)
    rw [abs_sub_comm, hli] at this
    simpa using this
  calc ∑ i ∈ F, kerW (Iof i) J
      ≤ ∑ i ∈ F, 25 / 4 * (1 + |(Iof i).center - J.center| / ℓ) ^ (-((2 : ℕ) : ℤ)) :=
        Finset.sum_le_sum hterm
    _ = 25 / 4 * ∑ i ∈ F, (1 + |(Iof i).center - J.center| / ℓ) ^ (-((2 : ℕ) : ℤ)) := by
        rw [Finset.mul_sum]
    _ ≤ 25 / 4 * ((3 / 2) ^ 2 * (2 * (1 / (((2 : ℕ) : ℝ) - 1)) *
          (1 + 0 / ℓ) ^ (-(((2 : ℕ) : ℤ) - 1)))) := by gcongr
    _ = 225 / 8 := by norm_num

/-- If `|c(I) - x| = dist(I, J) + |I|/2` then `W(I, J) ≤ (9/4) (1 + |c(I) - x|/|I|)^{-2}`. -/
theorem kerW_le_of_abs_eq {I J : Dyadic} {x : ℝ}
    (h : |I.center - x| = I.dist J + I.length / 2) :
    kerW I J ≤ 9 / 4 * (1 + |I.center - x| / I.length) ^ (-2 : ℤ) := by
  have hI := I.length_pos
  have hd := I.dist_nonneg J
  have hb : 1 + |I.center - x| / I.length ≤ 3 / 2 * (1 + I.dist J / I.length) := by
    rw [h]
    have : (I.dist J + I.length / 2) / I.length = I.dist J / I.length + 1 / 2 := by
      field_simp
    have h4 : 0 ≤ I.dist J / I.length := div_nonneg hd hI.le
    rw [this]
    linarith
  have := zpow_neg_two_le_mul (a := 1 + I.dist J / I.length) (b := 1 + |I.center - x| / I.length)
    (k := 3 / 2) (by positivity) (by positivity) (by norm_num) hb
  rw [show (3 / 2 : ℝ) ^ 2 = 9 / 4 by norm_num] at this
  exact this

/-- One scale `ℓ < |J|`, intervals disjoint from `J`: `∑_{I of scale ℓ} W(I, J) ≤ 81/4`. -/
theorem sum_kerW_scale_le_small {ι : Type*} (F : Finset ι) (Iof : ι → Dyadic) (J : Dyadic)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hlen : ∀ i ∈ F, (Iof i).length = ℓ)
    (hdisj : (F : Set ι).PairwiseDisjoint fun i => (Iof i).toSet)
    (hdJ : ∀ i ∈ F, Disjoint (Iof i).toSet J.toSet) :
    ∑ i ∈ F, kerW (Iof i) J ≤ 81 / 4 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not F (fun i => J.right ≤ (Iof i).left)]
  have hR : ∑ i ∈ F.filter (fun i => J.right ≤ (Iof i).left), kerW (Iof i) J ≤ 81 / 8 := by
    have hF : ∀ i ∈ F.filter (fun i => J.right ≤ (Iof i).left), (Iof i).length = ℓ :=
      fun i hi => hlen i (Finset.mem_filter.1 hi).1
    have hbound := sum_one_add_abs_zpow_le (F.filter (fun i => J.right ≤ (Iof i).left)) Iof hℓ hF
      (hdisj.subset (by intro i hi; exact (Finset.mem_filter.1 hi).1)) (N := 2) (le_refl 2)
      J.right (d := 0) le_rfl (fun i _ y _ => abs_nonneg _)
    have hterm : ∀ i ∈ F.filter (fun i => J.right ≤ (Iof i).left), kerW (Iof i) J ≤
        9 / 4 * (1 + |(Iof i).center - J.right| / ℓ) ^ (-((2 : ℕ) : ℤ)) := by
      intro i hi
      have hi' := Finset.mem_filter.1 hi
      have hli := hlen i hi'.1
      have hdist := Dyadic.dist_eq_of_right_le' hi'.2
      have hc := (Iof i).center_eq
      have hr := (Iof i).right_eq
      have habs : |(Iof i).center - J.right| = (Iof i).dist J + (Iof i).length / 2 := by
        rw [abs_of_nonneg (by linarith [(Iof i).left_lt_right, (Iof i).length_pos]), hdist]
        linarith
      have := kerW_le_of_abs_eq habs
      rw [hli] at this
      simpa using this
    calc ∑ i ∈ F.filter (fun i => J.right ≤ (Iof i).left), kerW (Iof i) J
        ≤ ∑ i ∈ F.filter (fun i => J.right ≤ (Iof i).left),
            9 / 4 * (1 + |(Iof i).center - J.right| / ℓ) ^ (-((2 : ℕ) : ℤ)) :=
          Finset.sum_le_sum hterm
      _ = 9 / 4 * ∑ i ∈ F.filter (fun i => J.right ≤ (Iof i).left),
            (1 + |(Iof i).center - J.right| / ℓ) ^ (-((2 : ℕ) : ℤ)) := by rw [Finset.mul_sum]
      _ ≤ 9 / 4 * ((3 / 2) ^ 2 * (2 * (1 / (((2 : ℕ) : ℝ) - 1)) *
            (1 + 0 / ℓ) ^ (-(((2 : ℕ) : ℤ) - 1)))) := by gcongr
      _ = 81 / 8 := by norm_num
  have hL : ∑ i ∈ F.filter (fun i => ¬ J.right ≤ (Iof i).left), kerW (Iof i) J ≤ 81 / 8 := by
    have hF : ∀ i ∈ F.filter (fun i => ¬ J.right ≤ (Iof i).left), (Iof i).length = ℓ :=
      fun i hi => hlen i (Finset.mem_filter.1 hi).1
    have hbound := sum_one_add_abs_zpow_le (F.filter (fun i => ¬ J.right ≤ (Iof i).left)) Iof hℓ hF
      (hdisj.subset (by intro i hi; exact (Finset.mem_filter.1 hi).1)) (N := 2) (le_refl 2)
      J.left (d := 0) le_rfl (fun i _ y _ => abs_nonneg _)
    have hterm : ∀ i ∈ F.filter (fun i => ¬ J.right ≤ (Iof i).left), kerW (Iof i) J ≤
        9 / 4 * (1 + |(Iof i).center - J.left| / ℓ) ^ (-((2 : ℕ) : ℤ)) := by
      intro i hi
      have hi' := Finset.mem_filter.1 hi
      have hli := hlen i hi'.1
      have hdj := Dyadic.right_le_left_or_right_le_left_of_disjoint (hdJ i hi'.1)
      have hIJ : (Iof i).right ≤ J.left := by
        rcases hdj with h | h
        · exact h
        · exact absurd h hi'.2
      have hdist := Dyadic.dist_eq_of_right_le hIJ
      have hc := (Iof i).center_eq
      have hr := (Iof i).right_eq
      have habs : |(Iof i).center - J.left| = (Iof i).dist J + (Iof i).length / 2 := by
        rw [abs_of_nonpos (by linarith [(Iof i).left_lt_right, (Iof i).length_pos]), hdist]
        linarith
      have := kerW_le_of_abs_eq habs
      rw [hli] at this
      simpa using this
    calc ∑ i ∈ F.filter (fun i => ¬ J.right ≤ (Iof i).left), kerW (Iof i) J
        ≤ ∑ i ∈ F.filter (fun i => ¬ J.right ≤ (Iof i).left),
            9 / 4 * (1 + |(Iof i).center - J.left| / ℓ) ^ (-((2 : ℕ) : ℤ)) :=
          Finset.sum_le_sum hterm
      _ = 9 / 4 * ∑ i ∈ F.filter (fun i => ¬ J.right ≤ (Iof i).left),
            (1 + |(Iof i).center - J.left| / ℓ) ^ (-((2 : ℕ) : ℤ)) := by rw [Finset.mul_sum]
      _ ≤ 9 / 4 * ((3 / 2) ^ 2 * (2 * (1 / (((2 : ℕ) : ℝ) - 1)) *
            (1 + 0 / ℓ) ^ (-(((2 : ℕ) : ℤ) - 1)))) := by gcongr
      _ = 81 / 8 := by norm_num
  linarith

/-- Distinct dyadic intervals of one scale (an injective family) are pairwise disjoint. -/
theorem pairwiseDisjoint_scale {ι : Type*} (Q : Finset ι) (Iof : ι → Dyadic)
    (hinj : Set.InjOn Iof (Q : Set ι)) (k : ℤ) :
    ((Q.filter (fun i => (Iof i).k = k) : Finset ι) : Set ι).PairwiseDisjoint
      fun i => (Iof i).toSet := by
  classical
  intro i hi j hj hne
  have hi' := Finset.mem_filter.1 (Finset.mem_coe.1 hi)
  have hj' := Finset.mem_filter.1 (Finset.mem_coe.1 hj)
  exact Dyadic.disjoint_of_k_eq_of_ne (hi'.2.trans hj'.2.symm) (fun h => hne (hinj hi'.1 hj'.1 h))

/-- **Column sum**: `∑_I |I| m(I, J) ≤ 100 |J|` for distinct dyadic `I` (those smaller than `J`
disjoint from `J`). -/
theorem sum_length_mul_kerM_le_col {ι : Type*} (Q : Finset ι) (Iof : ι → Dyadic)
    (hinj : Set.InjOn Iof (Q : Set ι)) (J : Dyadic)
    (hrel : ∀ i ∈ Q, (Iof i).length < J.length → Disjoint (Iof i).toSet J.toSet) :
    ∑ i ∈ Q, (Iof i).length * kerM (Iof i) J ≤ 100 * J.length := by
  classical
  have hJ := J.length_pos
  rw [← Finset.sum_filter_add_sum_filter_not Q (fun i => J.length ≤ (Iof i).length)]
  have hbig : ∑ i ∈ Q.filter (fun i => J.length ≤ (Iof i).length), (Iof i).length *
      kerM (Iof i) J ≤ 225 / 4 * J.length := by
    set Qb := Q.filter (fun i => J.length ≤ (Iof i).length) with hQb
    set K := Qb.image (fun i => (Iof i).k) with hK
    have hKge : ∀ k ∈ K, J.k ≤ k := by
      intro k hk
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hk
      exact Dyadic.length_le_iff.1 (Finset.mem_filter.1 hi).2
    have hfib : ∀ k ∈ K, ∑ i ∈ Qb.filter (fun i => (Iof i).k = k), (Iof i).length *
        kerM (Iof i) J ≤ 225 / 8 * J.length * ((1 : ℝ) / 2) ^ (k - J.k).toNat := by
      intro k hk
      set F := Qb.filter (fun i => (Iof i).k = k) with hF
      have hℓ : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
      have hlen : ∀ i ∈ F, (Iof i).length = (2 : ℝ) ^ k := by
        intro i hi
        have := (Finset.mem_filter.1 hi).2
        unfold Dyadic.length; rw [this]
      have hJℓ : J.length ≤ (2 : ℝ) ^ k := by
        unfold Dyadic.length
        exact zpow_le_zpow_right₀ (by norm_num) (hKge k hk)
      have hdisj : (F : Set ι).PairwiseDisjoint fun i => (Iof i).toSet := by
        refine (pairwiseDisjoint_scale Qb Iof ?_ k)
        exact hinj.mono (by intro i hi; exact (Finset.mem_filter.1 hi).1)
      have hsum := sum_kerW_scale_le_large F Iof J hℓ hlen hJℓ hdisj
      have hterm : ∀ i ∈ F, (Iof i).length * kerM (Iof i) J =
          J.length * (J.length / (2 : ℝ) ^ k) * kerW (Iof i) J := by
        intro i hi
        have hi' := Finset.mem_filter.1 hi
        have hle := (Finset.mem_filter.1 hi'.1).2
        unfold kerM
        simp only [hle, ↓reduceIte]
        rw [hlen i hi]
        field_simp
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, length_div_two_zpow (hKge k hk)]
      calc J.length * ((1 : ℝ) / 2) ^ (k - J.k).toNat * ∑ i ∈ F, kerW (Iof i) J
          ≤ J.length * ((1 : ℝ) / 2) ^ (k - J.k).toNat * (225 / 8) := by gcongr
        _ = 225 / 8 * J.length * ((1 : ℝ) / 2) ^ (k - J.k).toNat := by ring
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun i => (Iof i).k) (t := K)
      (fun i hi => Finset.mem_image_of_mem _ hi)]
    calc ∑ k ∈ K, ∑ i ∈ Qb.filter (fun i => (Iof i).k = k), (Iof i).length * kerM (Iof i) J
        ≤ ∑ k ∈ K, 225 / 8 * J.length * ((1 : ℝ) / 2) ^ (k - J.k).toNat :=
          Finset.sum_le_sum hfib
      _ = 225 / 8 * J.length * ∑ k ∈ K, ((1 : ℝ) / 2) ^ (k - J.k).toNat := by
          rw [Finset.mul_sum]
      _ ≤ 225 / 8 * J.length * 2 := by gcongr; exact sum_geom_ge hKge
      _ = 225 / 4 * J.length := by ring
  have hsmall : ∑ i ∈ Q.filter (fun i => ¬ J.length ≤ (Iof i).length), (Iof i).length *
      kerM (Iof i) J ≤ 81 / 2 * J.length := by
    set Qs := Q.filter (fun i => ¬ J.length ≤ (Iof i).length) with hQs
    set K := Qs.image (fun i => (Iof i).k) with hK
    have hKle : ∀ k ∈ K, k ≤ J.k := by
      intro k hk
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hk
      have := (Finset.mem_filter.1 hi).2
      rw [not_le] at this
      exact (Dyadic.length_lt_iff.1 this).le
    have hfib : ∀ k ∈ K, ∑ i ∈ Qs.filter (fun i => (Iof i).k = k), (Iof i).length *
        kerM (Iof i) J ≤ 81 / 4 * J.length * ((1 : ℝ) / 2) ^ (J.k - k).toNat := by
      intro k hk
      set F := Qs.filter (fun i => (Iof i).k = k) with hF
      have hℓ : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
      have hlen : ∀ i ∈ F, (Iof i).length = (2 : ℝ) ^ k := by
        intro i hi
        have := (Finset.mem_filter.1 hi).2
        unfold Dyadic.length; rw [this]
      have hdisj : (F : Set ι).PairwiseDisjoint fun i => (Iof i).toSet := by
        refine (pairwiseDisjoint_scale Qs Iof ?_ k)
        exact hinj.mono (by intro i hi; exact (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).1)
      have hdJ : ∀ i ∈ F, Disjoint (Iof i).toSet J.toSet := by
        intro i hi
        have hi' := Finset.mem_filter.1 (Finset.mem_filter.1 hi).1
        have := (Finset.mem_filter.1 (Finset.mem_filter.1 hi).1).2
        rw [not_le] at this
        exact hrel i hi'.1 this
      have hsum := sum_kerW_scale_le_small F Iof J hℓ hlen hdisj hdJ
      have hterm : ∀ i ∈ F, (Iof i).length * kerM (Iof i) J = (2 : ℝ) ^ k * kerW (Iof i) J := by
        intro i hi
        have hi' := (Finset.mem_filter.1 (Finset.mem_filter.1 hi).1).2
        unfold kerM
        simp only [hi', ↓reduceIte, one_mul]
        rw [hlen i hi]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      have h2k : (2 : ℝ) ^ k = J.length * ((1 : ℝ) / 2) ^ (J.k - k).toNat := by
        have := two_zpow_div_length (J := J) (k := k) (hKle k hk)
        field_simp at this ⊢
        linarith
      rw [h2k]
      calc J.length * ((1 : ℝ) / 2) ^ (J.k - k).toNat * ∑ i ∈ F, kerW (Iof i) J
          ≤ J.length * ((1 : ℝ) / 2) ^ (J.k - k).toNat * (81 / 4) := by gcongr
        _ = 81 / 4 * J.length * ((1 : ℝ) / 2) ^ (J.k - k).toNat := by ring
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun i => (Iof i).k) (t := K)
      (fun i hi => Finset.mem_image_of_mem _ hi)]
    calc ∑ k ∈ K, ∑ i ∈ Qs.filter (fun i => (Iof i).k = k), (Iof i).length * kerM (Iof i) J
        ≤ ∑ k ∈ K, 81 / 4 * J.length * ((1 : ℝ) / 2) ^ (J.k - k).toNat :=
          Finset.sum_le_sum hfib
      _ = 81 / 4 * J.length * ∑ k ∈ K, ((1 : ℝ) / 2) ^ (J.k - k).toNat := by
          rw [Finset.mul_sum]
      _ ≤ 81 / 4 * J.length * 2 := by gcongr; exact sum_geom_le hKle
      _ = 81 / 2 * J.length := by ring
  linarith

/-- A dyadic interval inside another is not longer. -/
theorem Dyadic.length_le_of_subset' {I J : Dyadic} (h : J.toSet ⊆ I.toSet) :
    J.length ≤ I.length :=
  Dyadic.length_le_iff.2 (Dyadic.k_le_of_toSet_subset h)

/-- **Row sum**: `∑_J m(I, J) ≤ 25` for pairwise disjoint `J` (those larger than `I` disjoint
from `I`). -/
theorem sum_kerM_le_row (I : Dyadic) (S : Finset Dyadic)
    (hdisj : (S : Set Dyadic).PairwiseDisjoint Dyadic.toSet)
    (hrel : ∀ J ∈ S, I.length < J.length → Disjoint I.toSet J.toSet) :
    ∑ J ∈ S, kerM I J ≤ 25 := by
  classical
  have hI := I.length_pos
  rw [← Finset.sum_filter_add_sum_filter_not S (fun J => J.length ≤ I.length)]
  have h1 : ∑ J ∈ S.filter (fun J => J.length ≤ I.length), kerM I J ≤ 25 / 2 := by
    have hsmall := sum_length_mul_kerW_le_small I (S.filter (fun J => J.length ≤ I.length))
      (hdisj.subset (by intro J hJ; exact (Finset.mem_filter.1 hJ).1))
      (fun J hJ => (Finset.mem_filter.1 hJ).2)
    calc ∑ J ∈ S.filter (fun J => J.length ≤ I.length), kerM I J
        ≤ ∑ J ∈ S.filter (fun J => J.length ≤ I.length), J.length * kerW I J / I.length := by
          refine Finset.sum_le_sum fun J hJ => ?_
          have hle := (Finset.mem_filter.1 hJ).2
          have hr0 : 0 ≤ J.length / I.length := by have := J.length_pos; positivity
          have hr1 : J.length / I.length ≤ 1 := (div_le_one hI).2 hle
          have hW := kerW_pos I J
          simp only [kerM, hle, ↓reduceIte]
          calc (J.length / I.length) ^ 2 * kerW I J ≤ (J.length / I.length) * kerW I J :=
                mul_le_mul_of_nonneg_right (by nlinarith) hW.le
            _ = J.length * kerW I J / I.length := by ring
      _ = (∑ J ∈ S.filter (fun J => J.length ≤ I.length), J.length * kerW I J) / I.length := by
          rw [Finset.sum_div]
      _ ≤ (25 / 4 * (2 * I.length)) / I.length := by gcongr
      _ = 25 / 2 := by field_simp; ring
  have h2 : ∑ J ∈ S.filter (fun J => ¬ J.length ≤ I.length), kerM I J ≤ 25 / 2 := by
    have hlarge := sum_kerW_le_large I (S.filter (fun J => ¬ J.length ≤ I.length))
      (hdisj.subset (by intro J hJ; exact (Finset.mem_filter.1 hJ).1))
      (fun J hJ => by have := (Finset.mem_filter.1 hJ).2; rw [not_le] at this; exact this.le)
      (fun J hJ => by
        have := (Finset.mem_filter.1 hJ).2
        rw [not_le] at this
        exact hrel J (Finset.mem_filter.1 hJ).1 this)
    calc ∑ J ∈ S.filter (fun J => ¬ J.length ≤ I.length), kerM I J
        = ∑ J ∈ S.filter (fun J => ¬ J.length ≤ I.length), kerW I J := by
          refine Finset.sum_congr rfl fun J hJ => ?_
          have := (Finset.mem_filter.1 hJ).2
          simp only [kerM, this, ↓reduceIte, one_mul]
      _ ≤ 25 / 4 * 2 := hlarge
      _ = 25 / 2 := by norm_num
  linarith

/-- **The Schur estimate**: for distinct dyadic `I` (indexed injectively by `Q`) and a finite
family `S` of pairwise disjoint dyadic `J`, each either inside or disjoint from each `I`,
`∑_I |I| (∑_J m(I, J))² ≤ 2500 ∑_J |J|`. -/
theorem sum_length_mul_sq_kerM_le {ι : Type*} (Q : Finset ι) (Iof : ι → Dyadic)
    (hinj : Set.InjOn Iof (Q : Set ι)) (S : Finset Dyadic)
    (hdisj : (S : Set Dyadic).PairwiseDisjoint Dyadic.toSet)
    (hrel : ∀ i ∈ Q, ∀ J ∈ S, J.toSet ⊆ (Iof i).toSet ∨ Disjoint (Iof i).toSet J.toSet) :
    ∑ i ∈ Q, (Iof i).length * (∑ J ∈ S, kerM (Iof i) J) ^ 2 ≤ 2500 * ∑ J ∈ S, J.length := by
  have hdis : ∀ i ∈ Q, ∀ J ∈ S, (Iof i).length < J.length → Disjoint (Iof i).toSet J.toSet := by
    intro i hi J hJ hlt
    rcases hrel i hi J hJ with h | h
    · exact absurd (Dyadic.length_le_of_subset' h) (not_le.2 hlt)
    · exact h
  have hrow : ∀ i ∈ Q, ∑ J ∈ S, kerM (Iof i) J ≤ 25 := fun i hi =>
    sum_kerM_le_row (Iof i) S hdisj (fun J hJ => hdis i hi J hJ)
  have hcol : ∀ J ∈ S, ∑ i ∈ Q, (Iof i).length * kerM (Iof i) J ≤ 100 * J.length := fun J hJ =>
    sum_length_mul_kerM_le_col Q Iof hinj J (fun i hi => fun hlt => hdis i hi J hJ hlt)
  calc ∑ i ∈ Q, (Iof i).length * (∑ J ∈ S, kerM (Iof i) J) ^ 2
      ≤ ∑ i ∈ Q, (Iof i).length * (25 * ∑ J ∈ S, kerM (Iof i) J) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hx0 : 0 ≤ ∑ J ∈ S, kerM (Iof i) J := Finset.sum_nonneg fun J _ => kerM_nonneg _ _
        refine mul_le_mul_of_nonneg_left ?_ (Iof i).length_pos.le
        nlinarith [hrow i hi]
    _ = 25 * ∑ J ∈ S, ∑ i ∈ Q, (Iof i).length * kerM (Iof i) J := by
        have h1 : ∀ i ∈ Q, (Iof i).length * (25 * ∑ J ∈ S, kerM (Iof i) J) =
            25 * ∑ J ∈ S, (Iof i).length * kerM (Iof i) J := by
          intro i _
          rw [← Finset.mul_sum]
          ring
        rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Finset.sum_comm]
    _ ≤ 25 * ∑ J ∈ S, 100 * J.length := by
        gcongr with J hJ
        exact hcol J hJ
    _ = 2500 * ∑ J ∈ S, J.length := by rw [← Finset.mul_sum]; ring

end PrimeCarleson.Proof.Oplus

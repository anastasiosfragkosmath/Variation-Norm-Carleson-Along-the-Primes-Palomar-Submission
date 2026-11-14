module

public import PrimeCarleson.Proof.Oplus.Estimates.All

/-!
# The tail weight sum of the energy increment ([O+] L1627-L1644)

Source: [O+] `energyincrementprop`, L1627–L1644: for each `l`,
`∑_{P ∈ S_j : |I| = 2^l} ⟨w_I, 1_{ℝ ∖ I_{S_j}}⟩ ≲ 1`, with
`w_I(x) = |I|⁻¹ (1 + |x - c(I)|/|I|)^{-N}`.

The packets of one scale in `S_j` have pairwise distinct (hence disjoint) time intervals, all
inside `I_{S_j}`; this is the pure real-analysis statement
`exists_sum_integral_weight_compl_le`: for dyadic intervals `I ∈ A` of one scale inside a dyadic
interval `IS`, `∑_{I ∈ A} ∫_{ℝ ∖ IS} w_I ≤ K` with `K` absolute (independent of `N ≥ 3`, `IS`,
the scale, and `A`; in fact `K = 2`).

* `integral_Ioi_inv_mul_one_add_abs_div_zpow`, `integral_Iio_inv_mul_one_add_abs_div_zpow`: the
  exact tails `∫_{x > q} L⁻¹ (1 + |x - c|/L)^{-N} = (N - 1)⁻¹ (1 + (q - c)/L)^{-(N-1)}` and its
  mirror image;
* `Dyadic.integral_weight_compl_le`: for `I ⊆ IS`, `∫_{ℝ ∖ IS} w_I` is at most
  `((1 + a)^{-2} + (1 + b)^{-2})/2`, where `a, b ≥ 0` are the distances (in units of `|I|`) from
  `I` to the two ends of `IS`;
* `sum_inv_one_add_sq_le`: a finite sum `∑ (1 + φ_i)^{-2}` with `φ_i ≥ n_i` for an injective
  `n : ι → ℕ` is at most `2`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-! ### Tails of the weight -/

/-- `∫_{x > q} L⁻¹ (1 + |x - c|/L)^{-N} dx = (N - 1)⁻¹ (1 + (q - c)/L)^{-(N-1)}` for
`N ≥ 2` and `c ≤ q`. -/
theorem integral_Ioi_inv_mul_one_add_abs_div_zpow {N : ℕ} (hN : 2 ≤ N) (c : ℝ) {L : ℝ}
    (hL : 0 < L) {q : ℝ} (hq : c ≤ q) :
    ∫ x in Ioi q, L⁻¹ * (1 + |x - c| / L) ^ (-(N : ℤ)) =
      (1 / ((N : ℝ) - 1)) * (1 + (q - c) / L) ^ (-((N : ℤ) - 1)) := by
  have hderiv : ∀ x ∈ Ici q,
      HasDerivAt (fun x : ℝ => -(1 + (x - c) / L) ^ (-((N : ℤ) - 1)) / ((N : ℝ) - 1))
        (L⁻¹ * (1 + |x - c| / L) ^ (-(N : ℤ))) x := by
    intro x hx
    have hxc : 0 ≤ (x - c) / L := div_nonneg (by linarith [hx.out]) hL.le
    have h1 : HasDerivAt (fun x : ℝ => (x - c) / L) L⁻¹ x := by
      simpa using ((hasDerivAt_id x).sub_const c).div_const L
    have h2 := (hasDerivAt_neg_one_add_zpow hN _ hxc).comp x h1
    have habs : |x - c| = x - c := abs_of_nonneg (by linarith [hx.out])
    rw [habs]
    refine h2.congr_deriv ?_
    ring
  have hlim : Tendsto (fun x : ℝ => -(1 + (x - c) / L) ^ (-((N : ℤ) - 1)) / ((N : ℝ) - 1))
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => 1 + (x - c) / L) atTop atTop := by
      refine tendsto_atTop_add_const_left _ 1 ?_
      simpa [sub_eq_add_neg] using
        (tendsto_atTop_add_const_right _ (-c) tendsto_id).atTop_div_const hL
    have h1 := (tendsto_zpow_atTop_zero (by omega : -((N : ℤ) - 1) < 0)).comp h0
    simpa using (h1.neg).div_const ((N : ℝ) - 1)
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv (fun x _ => by positivity) hlim]
  ring

/-- `∫_{x < p} L⁻¹ (1 + |x - c|/L)^{-N} dx = (N - 1)⁻¹ (1 + (c - p)/L)^{-(N-1)}` for
`N ≥ 2` and `p ≤ c`. -/
theorem integral_Iio_inv_mul_one_add_abs_div_zpow {N : ℕ} (hN : 2 ≤ N) (c : ℝ) {L : ℝ}
    (hL : 0 < L) {p : ℝ} (hp : p ≤ c) :
    ∫ x in Iio p, L⁻¹ * (1 + |x - c| / L) ^ (-(N : ℤ)) =
      (1 / ((N : ℝ) - 1)) * (1 + (c - p) / L) ^ (-((N : ℤ) - 1)) := by
  rw [← integral_Iic_eq_integral_Iio]
  have h := integral_comp_neg_Ioi (-p) (fun x : ℝ => L⁻¹ * (1 + |x - c| / L) ^ (-(N : ℤ)))
  rw [neg_neg] at h
  rw [← h]
  have h2 := integral_Ioi_inv_mul_one_add_abs_div_zpow hN (-c) hL (q := -p) (by linarith)
  have e : -p - -c = c - p := by ring
  rw [e] at h2
  rw [← h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have : |-x - c| = |x - -c| := by
    rw [← abs_neg]; congr 1; ring
  simp only [this]

/-- The numerical tail bound: for `N ≥ 3` and `0 ≤ a ≤ t`,
`(N - 1)⁻¹ (1 + t)^{-(N-1)} ≤ (1/2) (1 + a)^{-2}`. -/
theorem inv_mul_one_add_zpow_le {N : ℕ} (hN : 3 ≤ N) {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) :
    (1 / ((N : ℝ) - 1)) * (1 + t) ^ (-((N : ℤ) - 1)) ≤ (1 / 2) * ((1 + a) ^ 2)⁻¹ := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 3 := ⟨N - 3, by omega⟩
  have e : -(((n + 3 : ℕ) : ℤ) - 1) = -((n + 2 : ℕ) : ℤ) := by push_cast; ring
  rw [e, zpow_neg, zpow_natCast]
  have h1 : (1 + a) ^ 2 ≤ (1 + t) ^ (n + 2) :=
    (pow_le_pow_left₀ (by linarith) (by linarith) 2).trans
      (pow_le_pow_right₀ (by linarith) (by omega))
  have h2 : 0 < (1 + a) ^ 2 := by positivity
  have h3 : ((1 + t) ^ (n + 2))⁻¹ ≤ ((1 + a) ^ 2)⁻¹ := inv_anti₀ h2 h1
  have h4 : 1 / (((n + 3 : ℕ) : ℝ) - 1) ≤ 1 / 2 := by
    push_cast
    rw [div_le_div_iff₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by norm_num)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h5 : 0 < 1 + t := by linarith
  exact mul_le_mul h4 h3 (by positivity) (by norm_num)

/-! ### One interval inside another -/

/-- **The tail of one weight.** If the dyadic interval `I` lies in `IS`, then
`∫_{ℝ ∖ IS} w_I ≤ ((1 + a)^{-2} + (1 + b)^{-2}) / 2`, where `a = (I.left - IS.left)/|I|` and
`b = (IS.right - I.right)/|I|` are the (nonnegative) distances from `I` to the ends of `IS`
in units of `|I|`; `N ≥ 3`. -/
theorem Dyadic.integral_weight_compl_le {N : ℕ} (hN : 3 ≤ N) {I IS : Dyadic}
    (h : I.toSet ⊆ IS.toSet) :
    ∫ x in IS.toSetᶜ, I.weight N x ≤
      (1 / 2) * (((1 + (I.left - IS.left) / I.length) ^ 2)⁻¹ +
        ((1 + (IS.right - I.right) / I.length) ^ 2)⁻¹) := by
  have hL := I.length_pos
  have hN2 : 2 ≤ N := by omega
  have hsub : IS.left ≤ I.left ∧ I.right ≤ IS.right :=
    (Set.Ico_subset_Ico_iff I.left_lt_right).1 h
  have hpq : IS.left ≤ IS.right := IS.left_lt_right.le
  have hlc : I.left ≤ I.center := by rw [I.center_eq]; linarith
  have hcr : I.center ≤ I.right := by rw [I.center_eq, I.right_eq]; linarith
  have hint : Integrable (I.weight N) := I.integrable_weight hN2
  have hcompl : IS.toSetᶜ = Iio IS.left ∪ Ici IS.right := by
    ext x
    simp only [mem_compl_iff, Dyadic.mem_toSet, mem_union, mem_Iio, mem_Ici, not_and_or, not_le,
      not_lt]
  have hdisj : Disjoint (Iio IS.left) (Ici IS.right) :=
    Set.disjoint_left.2 fun x hx hx' => by
      have := hx.out; have := hx'.out; linarith
  have hl : ∫ x in Iio IS.left, I.weight N x =
      (1 / ((N : ℝ) - 1)) * (1 + (I.center - IS.left) / I.length) ^ (-((N : ℤ) - 1)) :=
    integral_Iio_inv_mul_one_add_abs_div_zpow hN2 I.center hL (by linarith)
  have hr : ∫ x in Ici IS.right, I.weight N x =
      (1 / ((N : ℝ) - 1)) * (1 + (IS.right - I.center) / I.length) ^ (-((N : ℤ) - 1)) := by
    rw [integral_Ici_eq_integral_Ioi]
    exact integral_Ioi_inv_mul_one_add_abs_div_zpow hN2 I.center hL (by linarith)
  rw [hcompl, setIntegral_union hdisj measurableSet_Ici hint.integrableOn hint.integrableOn,
    hl, hr]
  have ha : 0 ≤ (I.left - IS.left) / I.length := div_nonneg (by linarith) hL.le
  have hb : 0 ≤ (IS.right - I.right) / I.length := div_nonneg (by linarith) hL.le
  have h1 := inv_mul_one_add_zpow_le hN ha
    (show (I.left - IS.left) / I.length ≤ (I.center - IS.left) / I.length by gcongr)
  have h2 := inv_mul_one_add_zpow_le hN hb
    (show (IS.right - I.right) / I.length ≤ (IS.right - I.center) / I.length by gcongr)
  linarith

/-! ### Summing over distinct positions -/

/-- `∑_{m < M} (1 + m)^{-2} ≤ 2`. -/
theorem sum_range_inv_one_add_sq_le (M : ℕ) :
    ∑ m ∈ Finset.range M, (((1 : ℝ) + m) ^ 2)⁻¹ ≤ 2 := by
  have key : ∀ M : ℕ, 1 ≤ M →
      ∑ m ∈ Finset.range M, (((1 : ℝ) + m) ^ 2)⁻¹ ≤ 2 - 1 / (M : ℝ) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => norm_num
    | succ M hM ih =>
      rw [Finset.sum_range_succ]
      have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
      have h : (((1 : ℝ) + M) ^ 2)⁻¹ ≤ 1 / (M : ℝ) - 1 / ((M + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), inv_eq_one_div,
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  · have h1 := key M hM
    have h2 : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
    linarith

/-- If `φ_i ≥ n_i` for an injective `n : ι → ℕ` on a finite set `A`, then
`∑_{i ∈ A} (1 + φ_i)^{-2} ≤ 2`. -/
theorem sum_inv_one_add_sq_le {ι : Type*} (A : Finset ι) (φ : ι → ℝ) (n : ι → ℕ)
    (hinj : Set.InjOn n A) (hle : ∀ i ∈ A, (n i : ℝ) ≤ φ i) :
    ∑ i ∈ A, ((1 + φ i) ^ 2)⁻¹ ≤ 2 := by
  classical
  calc ∑ i ∈ A, ((1 + φ i) ^ 2)⁻¹ ≤ ∑ i ∈ A, (((1 : ℝ) + n i) ^ 2)⁻¹ := by
        refine Finset.sum_le_sum fun i hi => ?_
        have h := hle i hi
        have h0 : (0 : ℝ) < 1 + n i := by positivity
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h0.le (by linarith) 2)
    _ = ∑ m ∈ A.image n, (((1 : ℝ) + m) ^ 2)⁻¹ := by rw [Finset.sum_image hinj]
    _ ≤ ∑ m ∈ Finset.range ((A.image n).sup id + 1), (((1 : ℝ) + m) ^ 2)⁻¹ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
        intro m hm
        rw [Finset.mem_range]
        have := Finset.le_sup (f := id) hm
        simp only [id] at this
        omega
    _ ≤ 2 := sum_range_inv_one_add_sq_le _

/-! ### The tail weight sum -/

/-- **The tail weight sum** ([O+] `energyincrementprop`, L1627–L1644): there is an absolute
constant `K` such that for
every `N ≥ 3`, every dyadic interval `IS`, every scale `k` and every finite family `A` of dyadic
intervals of scale `2^k` contained in `IS`, `∑_{I ∈ A} ⟨w_I, 1_{ℝ ∖ IS}⟩ ≤ K`. (The proof gives
`K = 2`.) -/
theorem exists_sum_integral_weight_compl_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ), 3 ≤ N → ∀ (IS : Dyadic) (k : ℤ) (A : Finset Dyadic),
      (∀ I ∈ A, I.k = k ∧ I.toSet ⊆ IS.toSet) →
      ∑ I ∈ A, ∫ x in IS.toSetᶜ, I.weight N x ≤ K := by
  refine ⟨2, by norm_num, fun N hN IS k A hA => ?_⟩
  have hL : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hlen : ∀ I ∈ A, I.length = (2 : ℝ) ^ k := fun I hI => by
    rw [Dyadic.length, (hA I hI).1]
  have hleft : ∀ I ∈ A, I.left = (2 : ℝ) ^ k * I.m := fun I hI => by
    rw [Dyadic.left, (hA I hI).1]
  have hright : ∀ I ∈ A, I.right = (2 : ℝ) ^ k * (I.m + 1) := fun I hI => by
    rw [Dyadic.right, (hA I hI).1]
  have hsub : ∀ I ∈ A, IS.left ≤ I.left ∧ I.right ≤ IS.right := fun I hI =>
    (Set.Ico_subset_Ico_iff I.left_lt_right).1 (hA I hI).2
  have hext : ∀ I ∈ A, ∀ J ∈ A, I.m = J.m → I = J := fun I hI J hJ hm =>
    Dyadic.ext (by rw [(hA I hI).1, (hA J hJ).1]) hm
  have h1 : ∀ I ∈ A, ∫ x in IS.toSetᶜ, I.weight N x ≤
      (1 / 2) * (((1 + (I.left - IS.left) / I.length) ^ 2)⁻¹ +
        ((1 + (IS.right - I.right) / I.length) ^ 2)⁻¹) := fun I hI =>
    Dyadic.integral_weight_compl_le hN (hA I hI).2
  -- the left distances
  have hceil : ∀ I ∈ A, ⌈IS.left / (2 : ℝ) ^ k⌉ ≤ I.m := fun I hI => by
    refine Int.ceil_le.2 ?_
    rw [div_le_iff₀ hL, mul_comm, ← hleft I hI]
    exact (hsub I hI).1
  have hleftsum : ∑ I ∈ A, ((1 + (I.left - IS.left) / I.length) ^ 2)⁻¹ ≤ 2 := by
    refine sum_inv_one_add_sq_le A _ (fun I => (I.m - ⌈IS.left / (2 : ℝ) ^ k⌉).toNat) ?_ ?_
    · intro I hI J hJ hIJ
      have h1 := hceil I hI
      have h2 := hceil J hJ
      have : I.m = J.m := by simp only at hIJ; omega
      exact hext I hI J hJ this
    · intro I hI
      have hc := hceil I hI
      have hn : (((I.m - ⌈IS.left / (2 : ℝ) ^ k⌉).toNat : ℕ) : ℝ) =
          ((I.m - ⌈IS.left / (2 : ℝ) ^ k⌉ : ℤ) : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
      have hup := Int.le_ceil (IS.left / (2 : ℝ) ^ k)
      have e : (I.left - IS.left) / I.length = I.m - IS.left / (2 : ℝ) ^ k := by
        rw [hlen I hI, hleft I hI]
        field_simp
      rw [e, hn]
      push_cast
      linarith
  -- the right distances
  have hfloor : ∀ I ∈ A, I.m + 1 ≤ ⌊IS.right / (2 : ℝ) ^ k⌋ := fun I hI => by
    refine Int.le_floor.2 ?_
    rw [le_div_iff₀ hL]
    push_cast
    rw [mul_comm, ← hright I hI]
    exact (hsub I hI).2
  have hrightsum : ∑ I ∈ A, ((1 + (IS.right - I.right) / I.length) ^ 2)⁻¹ ≤ 2 := by
    refine sum_inv_one_add_sq_le A _
      (fun I => (⌊IS.right / (2 : ℝ) ^ k⌋ - 1 - I.m).toNat) ?_ ?_
    · intro I hI J hJ hIJ
      have h1 := hfloor I hI
      have h2 := hfloor J hJ
      have : I.m = J.m := by simp only at hIJ; omega
      exact hext I hI J hJ this
    · intro I hI
      have hc := hfloor I hI
      have hn : (((⌊IS.right / (2 : ℝ) ^ k⌋ - 1 - I.m).toNat : ℕ) : ℝ) =
          ((⌊IS.right / (2 : ℝ) ^ k⌋ - 1 - I.m : ℤ) : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
      have hdn := Int.floor_le (IS.right / (2 : ℝ) ^ k)
      have e : (IS.right - I.right) / I.length = IS.right / (2 : ℝ) ^ k - (I.m + 1) := by
        rw [hlen I hI, hright I hI]
        field_simp
      rw [e, hn]
      push_cast
      linarith
  calc ∑ I ∈ A, ∫ x in IS.toSetᶜ, I.weight N x
      ≤ ∑ I ∈ A, (1 / 2) * (((1 + (I.left - IS.left) / I.length) ^ 2)⁻¹ +
        ((1 + (IS.right - I.right) / I.length) ^ 2)⁻¹) := Finset.sum_le_sum h1
    _ = (1 / 2) * (∑ I ∈ A, ((1 + (I.left - IS.left) / I.length) ^ 2)⁻¹ +
        ∑ I ∈ A, ((1 + (IS.right - I.right) / I.length) ^ 2)⁻¹) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ (1 / 2) * (2 + 2) := by gcongr
    _ = 2 := by norm_num

end PrimeCarleson.Proof.Oplus

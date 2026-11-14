module

public import PrimeCarleson.Proof.Oplus.TreeSmall.SingleTile

/-!
# The small-interval estimate ([O+] L2081-L2125)

Source: [O+] `treeestimatesmallintervals`, L2081–L2091 (L2081-L2125).

* `scale_sum_bound`: for the multitiles of one scale `|I| = ℓ` in a tree whose intervals `I` all
  satisfy `I ⊄ 3J`, `∑_P (1 + dist(I, J)/|I|)^{-M'} ≲ (1 + dist(I_𝒯, J)/ℓ)^{-(M'-1)}`
  (the time intervals of one scale are disjoint, Observation (iii), and `I ⊄ 3J` makes
  `|x - c(I)| ≲ |I| + dist(I, J)` for `x ∈ J`; `WeightSums.lean`).
* `sum_rpow_two_zpow_le`: the geometric sum over the scales `2^s < B`.
* `treeestimate_small_intervals` (Source: [O+] `treeestimatesmallintervals`, L2081–L2091,
L2081-L2125):
  for `J` with `I ⊄ 3J` for all `P ∈ T` (e.g. `J ∈ 𝒥`) and `C'' = 8C₁/(C₂ - 1)`,
  `‖∑_{P ∈ T : |I| < C''|J|} ⟨f, φ_P⟩ φ_P a_P 1_E‖_{L^q(J)} ≲ ene den^{min(1, r'/q)} |J|^{1/q}
  (1 + dist(I_T, J)/|I_T|)^{-(N-6)}` for every `q ≥ 1`: Minkowski over the tiles, the single-tile
  bound for `q ≥ r'` (`single_tile_bound`) and, for `q < r'`, Hölder on `J` from `q = r'`. The
  proof gives the exponent `N - 5` (stronger).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section ScaleSums

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

/-- **The sum over the multitiles of one scale** (L2118-L2123, "using the fact that `T` is a
tree"). -/
theorem scale_sum_bound (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    {𝒯 : MultitileTree ρ} (hT : 𝒯.IsTree C₁ C₂ M)
    (hp2 : SeparationProp2 C₁ (𝒯.T : Set (Multitile ρ))) {T' : Finset (Multitile ρ)}
    (hT' : T' ⊆ 𝒯.T) {J : Dyadic} (hJ : ∀ P ∈ T', ¬ P.I.toSet ⊆ J.dilate 3) (s : ℤ) {M' : ℕ}
    (hM' : 3 ≤ M') :
    ∑ P ∈ T'.filter (fun P => P.I.k = s), (1 + P.I.dist J / P.I.length) ^ (-(M' : ℤ)) ≤
      (15 / 4) ^ M' * (2 * (1 / ((M' : ℝ) - 1)) *
        (1 + 𝒯.I.dist J / (2 : ℝ) ^ s) ^ (-((M' : ℤ) - 1))) := by
  classical
  set F := T'.filter (fun P => P.I.k = s) with hF
  have hℓ : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  have hlen : ∀ P ∈ F, P.I.length = (2 : ℝ) ^ s := fun P hP => by
    have := (Finset.mem_filter.1 hP).2
    unfold Dyadic.length; rw [this]
  have hdisj : (F : Set (Multitile ρ)).PairwiseDisjoint fun P => P.I.toSet := by
    intro P hP P' hP' hne
    have h1 := Finset.mem_filter.1 (Finset.mem_coe.1 hP)
    have h2 := Finset.mem_filter.1 (Finset.mem_coe.1 hP')
    refine treeobs_disjoint_time hC hρ 𝒯 hT hp2 (hT' h1.1) (hT' h2.1) hne ?_
    rw [Dyadic.length_eq_iff]
    have := P.area
    have := P'.area
    omega
  have hx₀ : J.left ∈ J.toSet := J.left_mem_toSet
  have hsum := sum_one_add_abs_zpow_le F Multitile.I hℓ hlen hdisj (N := M') (by omega) J.left
    (d := 𝒯.I.dist J) (𝒯.I.dist_nonneg J) (fun P hP y hy => by
      have := Dyadic.dist_le_abs_sub (I := 𝒯.I) (J := J) (hT.time P (hT' (Finset.mem_filter.1 hP).1)
        hy) hx₀
      exact this)
  have hpt : ∀ P ∈ F, (1 + P.I.dist J / P.I.length) ^ (-(M' : ℤ)) ≤
      (5 / 2) ^ M' * (1 + |P.I.center - J.left| / (2 : ℝ) ^ s) ^ (-(M' : ℤ)) := by
    intro P hP
    have hPT := (Finset.mem_filter.1 hP).1
    have hI := P.I.length_pos
    have hb := Dyadic.one_add_abs_sub_center_div_le (I := P.I) hx₀ (hJ P hPT)
    rw [abs_sub_comm] at hb
    rw [hlen P hP] at hb ⊢
    have hDnn : 0 ≤ P.I.dist J / (2 : ℝ) ^ s := div_nonneg (P.I.dist_nonneg J) hℓ.le
    have hpa : 0 < (1 + P.I.dist J / (2 : ℝ) ^ s) ^ M' := by positivity
    have hpb : 0 < (1 + |P.I.center - J.left| / (2 : ℝ) ^ s) ^ M' := by positivity
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hpa hpb]
    calc 1 * (1 + |P.I.center - J.left| / (2 : ℝ) ^ s) ^ M'
        ≤ (5 / 2 * (1 + P.I.dist J / (2 : ℝ) ^ s)) ^ M' := by
          rw [one_mul]; exact pow_le_pow_left₀ (by positivity) hb M'
      _ = _ := by rw [mul_pow]
  calc ∑ P ∈ F, (1 + P.I.dist J / P.I.length) ^ (-(M' : ℤ))
      ≤ ∑ P ∈ F, (5 / 2) ^ M' * (1 + |P.I.center - J.left| / (2 : ℝ) ^ s) ^ (-(M' : ℤ)) :=
        Finset.sum_le_sum hpt
    _ = (5 / 2) ^ M' * ∑ P ∈ F, (1 + |P.I.center - J.left| / (2 : ℝ) ^ s) ^ (-(M' : ℤ)) := by
        rw [Finset.mul_sum]
    _ ≤ (5 / 2) ^ M' * ((3 / 2) ^ M' * (2 * (1 / ((M' : ℝ) - 1)) *
        (1 + 𝒯.I.dist J / (2 : ℝ) ^ s) ^ (-((M' : ℤ) - 1)))) := by
        gcongr
    _ = _ := by rw [← mul_assoc, ← mul_pow]; norm_num

end ScaleSums

section Geometric

/-- **The geometric sum over scales**: for a finite set `𝒮` of integers with `2^s < B` and
`1/2 ≤ a`, `∑_{s ∈ 𝒮} (2^s)^a ≤ 4 B^a`. -/
theorem sum_rpow_two_zpow_le (𝒮 : Finset ℤ) {B : ℝ} (hB : 0 < B) (h : ∀ s ∈ 𝒮, (2 : ℝ) ^ s < B)
    {a : ℝ} (ha2 : 1 / 2 ≤ a) : ∑ s ∈ 𝒮, ((2 : ℝ) ^ s) ^ a ≤ 4 * B ^ a := by
  by_cases h𝒮 : 𝒮.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.1 h𝒮]
    simp only [Finset.sum_empty]
    positivity
  set m := 𝒮.max' h𝒮 with hm
  have hmmem : m ∈ 𝒮 := Finset.max'_mem _ _
  have hsm : ∀ s ∈ 𝒮, s ≤ m := fun s hs => Finset.le_max' _ _ hs
  set ρ₀ : ℝ := (1 / 2 : ℝ) ^ a with hρ₀
  have hρ₀0 : 0 ≤ ρ₀ := by positivity
  have hρ₀1 : ρ₀ ≤ 3 / 4 := by
    have h1 : ρ₀ ^ 2 ≤ 1 / 2 := by
      rw [hρ₀, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      calc (1 / 2 : ℝ) ^ (a * ((2 : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by push_cast; linarith)
        _ = 1 / 2 := Real.rpow_one _
    nlinarith
  have hterm : ∀ s ∈ 𝒮, ((2 : ℝ) ^ s) ^ a = ((2 : ℝ) ^ m) ^ a * ρ₀ ^ (m - s).toNat := by
    intro s hs
    have hn : (0 : ℤ) ≤ m - s := by linarith [hsm s hs]
    have e1 : (2 : ℝ) ^ s = (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ (m - s).toNat := by
      rw [one_div, inv_pow, ← zpow_natCast, Int.toNat_of_nonneg hn, ← zpow_neg,
        ← zpow_add₀ (by norm_num)]
      congr 1; ring
    rw [e1, Real.mul_rpow (by positivity) (by positivity), hρ₀,
      (Real.rpow_pow_comm (by norm_num) a _).symm]
  have hinj : Set.InjOn (fun s : ℤ => (m - s).toNat) (𝒮 : Set ℤ) := by
    intro s hs s' hs' hss
    have h1 := hsm s hs
    have h2 := hsm s' hs'
    simp only at hss
    omega
  have hgeo : ∑ j ∈ 𝒮.image (fun s : ℤ => (m - s).toNat), ρ₀ ^ j ≤ 4 := by
    calc ∑ j ∈ 𝒮.image (fun s : ℤ => (m - s).toNat), ρ₀ ^ j ≤ ∑' j : ℕ, ρ₀ ^ j :=
          (summable_geometric_of_lt_one hρ₀0 (by linarith)).sum_le_tsum _
            (fun j _ => by positivity)
      _ = (1 - ρ₀)⁻¹ := tsum_geometric_of_lt_one hρ₀0 (by linarith)
      _ ≤ 4 := by
          rw [inv_eq_one_div, div_le_iff₀ (by linarith)]; linarith
  have hmB : ((2 : ℝ) ^ m) ^ a ≤ B ^ a :=
    Real.rpow_le_rpow (by positivity) (h m hmmem).le (by linarith)
  calc ∑ s ∈ 𝒮, ((2 : ℝ) ^ s) ^ a
      = ∑ s ∈ 𝒮, ((2 : ℝ) ^ m) ^ a * ρ₀ ^ (m - s).toNat := Finset.sum_congr rfl hterm
    _ = ((2 : ℝ) ^ m) ^ a * ∑ j ∈ 𝒮.image (fun s : ℤ => (m - s).toNat), ρ₀ ^ j := by
        rw [Finset.sum_image hinj, Finset.mul_sum]
    _ ≤ B ^ a * 4 := by
        have : 0 ≤ ((2 : ℝ) ^ m) ^ a := by positivity
        calc ((2 : ℝ) ^ m) ^ a * ∑ j ∈ 𝒮.image (fun s : ℤ => (m - s).toNat), ρ₀ ^ j
            ≤ ((2 : ℝ) ^ m) ^ a * 4 := mul_le_mul_of_nonneg_left hgeo this
          _ ≤ B ^ a * 4 := by gcongr
    _ = 4 * B ^ a := mul_comm _ _

end Geometric

section SumTiles

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

/-- **The sum over all multitiles of a tree with `|I| < B`** (L2118-L2125): the estimate of the
single tiles summed over the scales (`scale_sum_bound`) and over the scales
(`sum_rpow_two_zpow_le`):
`∑_P |I|^{1/q} (1 + dist(I, J)/|I|)^{-M'} ≤ 4 B^{1/q} (15/4)^{M'} (2/(M'-1))
(1 + dist(I_𝒯, J)/|I_𝒯|)^{-(M'-1)}` for `1 ≤ q ≤ 2`, `M' ≥ 3`. -/
theorem sum_tiles_bound (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    {𝒯 : MultitileTree ρ} (hT : 𝒯.IsTree C₁ C₂ M)
    (hp2 : SeparationProp2 C₁ (𝒯.T : Set (Multitile ρ))) {T' : Finset (Multitile ρ)}
    (hT' : T' ⊆ 𝒯.T) {J : Dyadic} (hJ : ∀ P ∈ T', ¬ P.I.toSet ⊆ J.dilate 3) {q : ℝ}
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) {B : ℝ} (hB : 0 < B) (hsmall : ∀ P ∈ T', P.I.length < B)
    {M' : ℕ} (hM' : 3 ≤ M') :
    ∑ P ∈ T', P.I.length ^ (1 / q) * (1 + P.I.dist J / P.I.length) ^ (-(M' : ℤ)) ≤
      4 * B ^ (1 / q) * ((15 / 4) ^ M' * (2 * (1 / ((M' : ℝ) - 1)))) *
        (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((M' : ℤ) - 1)) := by
  classical
  have hIT := 𝒯.I.length_pos
  have hq0 : 0 < q := by linarith
  have hM1 : (0 : ℝ) < (M' : ℝ) - 1 := by
    have : (3 : ℝ) ≤ M' := by exact_mod_cast hM'
    linarith
  set 𝒮 : Finset ℤ := T'.image (fun P => P.I.k) with h𝒮
  have hmaps : ∀ P ∈ T', P.I.k ∈ 𝒮 := fun P hP => Finset.mem_image_of_mem _ hP
  have hscale : ∀ s ∈ 𝒮, (2 : ℝ) ^ s < B := by
    intro s hs
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hs
    exact hsmall P hP
  have hper : ∀ s ∈ 𝒮, ∑ P ∈ T'.filter (fun P => P.I.k = s),
      P.I.length ^ (1 / q) * (1 + P.I.dist J / P.I.length) ^ (-(M' : ℤ)) ≤
      ((2 : ℝ) ^ s) ^ (1 / q) * (((15 / 4) ^ M' * (2 * (1 / ((M' : ℝ) - 1)))) *
        (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((M' : ℤ) - 1))) := by
    intro s hs
    obtain ⟨P₀, hP₀, hs0⟩ := Finset.mem_image.1 hs
    have hℓ : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
    have hlen : ∀ P ∈ T'.filter (fun P => P.I.k = s), P.I.length = (2 : ℝ) ^ s := fun P hP => by
      have := (Finset.mem_filter.1 hP).2
      unfold Dyadic.length; rw [this]
    have hℓT : (2 : ℝ) ^ s ≤ 𝒯.I.length := by
      have : P₀.I.length ≤ 𝒯.I.length :=
        Dyadic.length_le_iff.2 (Dyadic.k_le_of_toSet_subset (hT.time P₀ (hT' hP₀)))
      have e : P₀.I.length = (2 : ℝ) ^ s := by unfold Dyadic.length; rw [hs0]
      linarith
    have h1 := scale_sum_bound hC hρ hT hp2 hT' hJ s hM'
    have h2 : (1 + 𝒯.I.dist J / (2 : ℝ) ^ s) ^ (-((M' : ℤ) - 1)) ≤
        (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((M' : ℤ) - 1)) := by
      have hd := 𝒯.I.dist_nonneg J
      have hle : 1 + 𝒯.I.dist J / 𝒯.I.length ≤ 1 + 𝒯.I.dist J / (2 : ℝ) ^ s := by
        have : 𝒯.I.dist J / 𝒯.I.length ≤ 𝒯.I.dist J / (2 : ℝ) ^ s :=
          div_le_div_of_nonneg_left hd hℓ hℓT
        linarith
      have e : -((M' : ℤ) - 1) = -(((M' - 1 : ℕ) : ℤ)) := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ M')]; ring
      rw [e, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hle _)
    calc ∑ P ∈ T'.filter (fun P => P.I.k = s),
          P.I.length ^ (1 / q) * (1 + P.I.dist J / P.I.length) ^ (-(M' : ℤ))
        = ∑ P ∈ T'.filter (fun P => P.I.k = s),
          ((2 : ℝ) ^ s) ^ (1 / q) * (1 + P.I.dist J / P.I.length) ^ (-(M' : ℤ)) :=
          Finset.sum_congr rfl fun P hP => by rw [hlen P hP]
      _ = ((2 : ℝ) ^ s) ^ (1 / q) * ∑ P ∈ T'.filter (fun P => P.I.k = s),
          (1 + P.I.dist J / P.I.length) ^ (-(M' : ℤ)) := by rw [Finset.mul_sum]
      _ ≤ ((2 : ℝ) ^ s) ^ (1 / q) * ((15 / 4) ^ M' * (2 * (1 / ((M' : ℝ) - 1)) *
          (1 + 𝒯.I.dist J / (2 : ℝ) ^ s) ^ (-((M' : ℤ) - 1)))) := by
          gcongr
      _ ≤ ((2 : ℝ) ^ s) ^ (1 / q) * ((15 / 4) ^ M' * (2 * (1 / ((M' : ℝ) - 1)) *
          (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((M' : ℤ) - 1)))) := by
          gcongr
      _ = _ := by ring
  have hgeo := sum_rpow_two_zpow_le 𝒮 hB hscale (a := 1 / q)
    (by rw [div_le_div_iff₀ (by norm_num) hq0]; linarith)
  have hc : 0 ≤ ((15 / 4 : ℝ) ^ M' * (2 * (1 / ((M' : ℝ) - 1)))) *
      (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((M' : ℤ) - 1)) := by
    have : (3 : ℝ) ≤ M' := by exact_mod_cast hM'
    have hd := 𝒯.I.dist_nonneg J
    have : 0 < (M' : ℝ) - 1 := by linarith
    positivity
  calc ∑ P ∈ T', P.I.length ^ (1 / q) * (1 + P.I.dist J / P.I.length) ^ (-(M' : ℤ))
      = ∑ s ∈ 𝒮, ∑ P ∈ T'.filter (fun P => P.I.k = s),
        P.I.length ^ (1 / q) * (1 + P.I.dist J / P.I.length) ^ (-(M' : ℤ)) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ s ∈ 𝒮, ((2 : ℝ) ^ s) ^ (1 / q) * (((15 / 4) ^ M' * (2 * (1 / ((M' : ℝ) - 1)))) *
        (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((M' : ℤ) - 1))) := Finset.sum_le_sum hper
    _ = (∑ s ∈ 𝒮, ((2 : ℝ) ^ s) ^ (1 / q)) * (((15 / 4) ^ M' * (2 * (1 / ((M' : ℝ) - 1)))) *
        (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((M' : ℤ) - 1))) := by rw [Finset.sum_mul]
    _ ≤ (4 * B ^ (1 / q)) * (((15 / 4) ^ M' * (2 * (1 / ((M' : ℝ) - 1)))) *
        (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((M' : ℤ) - 1))) :=
        mul_le_mul_of_nonneg_right hgeo hc
    _ = _ := by ring

end SumTiles

section SmallIntervals

/-- **The small-interval estimate for `q ≥ r'`** (L2081-L2125), constant independent of `r, q`
(for `1 ≤ q ≤ 2`). -/
theorem treeestimate_small_intervals_core {r q : ℝ} (hr : 1 < r) (hq : Real.conjExponent r ≤ q)
    (hq2 : q ≤ 2) (N : ℕ) (hN : 7 ≤ N) {C₁ C₂ C₃ : ℝ} (hC : AdmissibleConstants C₁ C₂ C₃) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {M : ℤ}, ρ.IsStd → ∀ (ch : ProfileChoice)
      (f : ℝ → ℂ) {E : Set ℝ}, MeasurableSet E → ∀ (L : Linearization r) {S : Set (Multitile ρ)}
      {ene den : ℝ}, 0 ≤ ene → 0 ≤ den → energy C₁ C₂ M ch f S ≤ ENNReal.ofReal ene →
      density C₁ C₂ M L E S ≤ ENNReal.ofReal den → ∀ (𝒯 : MultitileTree ρ),
      𝒯.IsTree C₁ C₂ M → (∀ P ∈ 𝒯.T, P.InSquare M) → (𝒯.T : Set (Multitile ρ)) ⊆ S →
      Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)) → ∀ {J : Dyadic}, 𝒯.Avoids J →
        eLpNorm (treeSum ch f L E (𝒯.T.filter fun P => P.I.length < Cpp C₁ C₂ * J.length))
            (ENNReal.ofReal q) (volume.restrict J.toSet) ≤
          ENNReal.ofReal (K * ene * den ^ (Real.conjExponent r / q) * J.length ^ (1 / q) *
            (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((N : ℤ) - 6))) := by
  classical
  obtain ⟨Ks, hKs0, hKs⟩ := single_tile_bound hr hq N
  obtain ⟨M', rfl⟩ : ∃ M' : ℕ, N = M' + 4 := ⟨N - 4, by omega⟩
  have hM3 : 3 ≤ M' := by omega
  have hr'1 : 1 < Real.conjExponent r := by
    unfold Real.conjExponent
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have hq1 : 1 ≤ q := (hr'1.trans_le hq).le
  have hq0 : 0 < q := by linarith
  have hC8 := eight_le_Cpp hC
  have hM1 : (0 : ℝ) < (M' : ℝ) - 1 := by
    have : (3 : ℝ) ≤ M' := by exact_mod_cast hM3
    linarith
  set c₀ : ℝ := (15 / 4) ^ M' * (2 * (1 / ((M' : ℝ) - 1))) with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  refine ⟨Ks * (4 * Cpp C₁ C₂ * c₀), by positivity, ?_⟩
  intro ρ _ M hρ ch f E hE L S ene den hene hden hen hde 𝒯 hT hsq hsub hsep J hJ
  set T' := 𝒯.T.filter fun P => P.I.length < Cpp C₁ C₂ * J.length with hT'def
  have hT' : T' ⊆ 𝒯.T := Finset.filter_subset _ _
  have hJ' : ∀ P ∈ T', ¬ P.I.toSet ⊆ J.dilate 3 := fun P hP => hJ P (hT' hP)
  have hJpos := J.length_pos
  have hAT : 1 ≤ 1 + 𝒯.I.dist J / 𝒯.I.length := by
    have : 0 ≤ 𝒯.I.dist J / 𝒯.I.length := div_nonneg (𝒯.I.dist_nonneg J) 𝒯.I.length_pos.le
    linarith
  have hsplit : treeSum ch f L E T' = ∑ P ∈ T', treeSum ch f L E {P} := by
    funext x
    simp [treeSum, Finset.sum_apply]
  have hbound : ∀ P ∈ T', eLpNorm (treeSum ch f L E {P}) (ENNReal.ofReal q)
      (volume.restrict J.toSet) ≤ ENNReal.ofReal (Ks * ene * den ^ (Real.conjExponent r / q) *
        P.I.length ^ (1 / q) * (1 + P.I.dist J / P.I.length) ^ (-((M' + 4 : ℕ) - 4 : ℤ))) :=
    fun P hP => hKs hC hρ ch f hE L hene hden hen hde (hsub (Finset.mem_coe.2 (hT' hP)))
      (hsq P (hT' hP)) (hJ' P hP)
  have hexp : (-(((M' + 4 : ℕ) : ℤ) - 4)) = -(M' : ℤ) := by push_cast; ring
  calc eLpNorm (treeSum ch f L E T') (ENNReal.ofReal q) (volume.restrict J.toSet)
      ≤ ∑ P ∈ T', eLpNorm (treeSum ch f L E {P}) (ENNReal.ofReal q) (volume.restrict J.toSet) := by
        rw [hsplit]
        exact eLpNorm_sum_le (by rw [ENNReal.one_le_ofReal]; exact hq1)
    _ ≤ ∑ P ∈ T', ENNReal.ofReal (Ks * ene * den ^ (Real.conjExponent r / q) *
          P.I.length ^ (1 / q) * (1 + P.I.dist J / P.I.length) ^ (-(M' : ℤ))) :=
        Finset.sum_le_sum fun P hP => by
          have := hbound P hP
          rwa [hexp] at this
    _ = ENNReal.ofReal (∑ P ∈ T', Ks * ene * den ^ (Real.conjExponent r / q) *
          P.I.length ^ (1 / q) * (1 + P.I.dist J / P.I.length) ^ (-(M' : ℤ))) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro P hP
        have := P.I.length_pos
        have := P.I.dist_nonneg J
        positivity
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hsum := sum_tiles_bound hC hρ hT hsep.prop2 hT' hJ' hq1 hq2
          (B := Cpp C₁ C₂ * J.length) (by positivity) (fun P hP => (Finset.mem_filter.1 hP).2)
          hM3
        have hfac : ∀ P ∈ T', Ks * ene * den ^ (Real.conjExponent r / q) *
            P.I.length ^ (1 / q) * (1 + P.I.dist J / P.I.length) ^ (-(M' : ℤ)) =
            (Ks * ene * den ^ (Real.conjExponent r / q)) *
            (P.I.length ^ (1 / q) * (1 + P.I.dist J / P.I.length) ^ (-(M' : ℤ))) :=
          fun P _ => by ring
        rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum]
        have hCq : (Cpp C₁ C₂ * J.length) ^ (1 / q) ≤ Cpp C₁ C₂ * J.length ^ (1 / q) := by
          rw [Real.mul_rpow (by linarith) hJpos.le]
          gcongr
          calc Cpp C₁ C₂ ^ (1 / q) ≤ Cpp C₁ C₂ ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith)
                  (by rw [div_le_one hq0]; exact hq1)
            _ = Cpp C₁ C₂ := Real.rpow_one _
        have hexp2 : (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((M' : ℤ) - 1)) ≤
            (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-(((M' + 4 : ℕ) : ℤ) - 6)) := by
          refine zpow_le_zpow_right₀ hAT ?_
          push_cast; linarith
        have hnn : 0 ≤ Ks * ene * den ^ (Real.conjExponent r / q) := by positivity
        calc Ks * ene * den ^ (Real.conjExponent r / q) * ∑ P ∈ T',
              (P.I.length ^ (1 / q) * (1 + P.I.dist J / P.I.length) ^ (-(M' : ℤ)))
            ≤ Ks * ene * den ^ (Real.conjExponent r / q) *
              (4 * (Cpp C₁ C₂ * J.length) ^ (1 / q) * c₀ *
                (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((M' : ℤ) - 1))) :=
              mul_le_mul_of_nonneg_left hsum hnn
          _ ≤ Ks * ene * den ^ (Real.conjExponent r / q) *
              (4 * (Cpp C₁ C₂ * J.length ^ (1 / q)) * c₀ *
                (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-(((M' + 4 : ℕ) : ℤ) - 6))) := by
              gcongr
          _ = _ := by ring

end SmallIntervals

section SmallIntervalsAll

/-- **`treeestimatesmallintervals`** ([O+] L2081-L2125). Let `r ≥ 2` (the paper: `r > 2`),
`1 ≤ q ≤ 2`, `N ≥ 7`. There is a constant `K` such that for every tree `T ⊂ S` of multitiles in the
square `[-2^M, 2^M]²` with the separation assumptions, `energy(S) ≤ ene`, `density(S) ≤ den`, and
every dyadic `J` with `I ⊄ 3J` for all `P ∈ T` (in particular every `J ∈ 𝒥`), with
`C'' = 8C₁/(C₂ - 1)`:
`‖∑_{P ∈ T : |I| < C''|J|} ⟨f, φ_P⟩ φ_P a_P 1_E‖_{L^q(J)} ≤
K ene den^{min(1, r'/q)} |J|^{1/q} (1 + dist(I_T, J)/|I_T|)^{-(N-6)}`. -/
theorem treeestimate_small_intervals {r q : ℝ} (hr : 2 ≤ r) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (N : ℕ)
    (hN : 7 ≤ N) {C₁ C₂ C₃ : ℝ} (hC : AdmissibleConstants C₁ C₂ C₃) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {M : ℤ}, ρ.IsStd → ∀ (ch : ProfileChoice)
      (f : ℝ → ℂ) {E : Set ℝ}, MeasurableSet E → ∀ (L : Linearization r) {S : Set (Multitile ρ)}
      {ene den : ℝ}, 0 ≤ ene → 0 ≤ den → energy C₁ C₂ M ch f S ≤ ENNReal.ofReal ene →
      density C₁ C₂ M L E S ≤ ENNReal.ofReal den → ∀ (𝒯 : MultitileTree ρ),
      𝒯.IsTree C₁ C₂ M → (∀ P ∈ 𝒯.T, P.InSquare M) → (𝒯.T : Set (Multitile ρ)) ⊆ S →
      Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)) → ∀ {J : Dyadic}, 𝒯.Avoids J →
        eLpNorm (treeSum ch f L E (𝒯.T.filter fun P => P.I.length < Cpp C₁ C₂ * J.length))
            (ENNReal.ofReal q) (volume.restrict J.toSet) ≤
          ENNReal.ofReal (K * ene * den ^ (min 1 (Real.conjExponent r / q)) *
            J.length ^ (1 / q) * (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((N : ℤ) - 6))) := by
  have hr1 : 1 < r := by linarith
  have hr' : 0 < Real.conjExponent r := by
    unfold Real.conjExponent
    exact div_pos (by linarith) (by linarith)
  have hr'2 : Real.conjExponent r ≤ 2 := by
    unfold Real.conjExponent
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hq0 : 0 < q := by linarith
  by_cases hqr : Real.conjExponent r ≤ q
  · obtain ⟨K, hK0, hK⟩ := treeestimate_small_intervals_core hr1 hqr hq2 N hN hC
    refine ⟨K, hK0, ?_⟩
    intro ρ _ M hρ ch f E hE L S ene den hene hden hen hde 𝒯 hT hsq hsub hsep J hJ
    have hmin : min 1 (Real.conjExponent r / q) = Real.conjExponent r / q :=
      min_eq_right (by rw [div_le_one hq0]; exact hqr)
    rw [hmin]
    exact hK hρ ch f hE L hene hden hen hde 𝒯 hT hsq hsub hsep hJ
  · rw [not_le] at hqr
    obtain ⟨K, hK0, hK⟩ := treeestimate_small_intervals_core hr1 (le_refl (Real.conjExponent r))
      hr'2 N hN hC
    refine ⟨K, hK0, ?_⟩
    intro ρ _ M hρ ch f E hE L S ene den hene hden hen hde 𝒯 hT hsq hsub hsep J hJ
    have hJpos := J.length_pos
    have hmin : min 1 (Real.conjExponent r / q) = 1 :=
      min_eq_left (by rw [le_div_iff₀ hq0]; linarith)
    rw [hmin]
    have hcore := hK hρ ch f hE L hene hden hen hde 𝒯 hT hsq hsub hsep hJ
    have hmeas : AEStronglyMeasurable (treeSum ch f L E
        (𝒯.T.filter fun P => P.I.length < Cpp C₁ C₂ * J.length)) (volume.restrict J.toSet) :=
      (measurable_treeSum ch f L hE _).aestronglyMeasurable
    have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (p := ENNReal.ofReal q) (q := ENNReal.ofReal (Real.conjExponent r))
      (ENNReal.ofReal_le_ofReal hqr.le) hmeas
    refine hH.trans ?_
    rw [ENNReal.toReal_ofReal hq0.le, ENNReal.toReal_ofReal hr'.le, Measure.restrict_apply_univ,
      Dyadic.volume_toSet]
    have hd0 : 0 ≤ 𝒯.I.dist J / 𝒯.I.length :=
      div_nonneg (𝒯.I.dist_nonneg J) 𝒯.I.length_pos.le
    have hexp : 0 ≤ 1 / q - 1 / Real.conjExponent r := by
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le hq0 hqr.le
    calc _ ≤ ENNReal.ofReal (K * ene * den ^ (Real.conjExponent r / Real.conjExponent r) *
          J.length ^ (1 / Real.conjExponent r) *
          (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((N : ℤ) - 6))) *
          ENNReal.ofReal J.length ^ (1 / q - 1 / Real.conjExponent r) := by gcongr
      _ = ENNReal.ofReal (K * ene * den ^ (1 : ℝ) * J.length ^ (1 / q) *
          (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((N : ℤ) - 6))) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hJpos.le hexp, ← ENNReal.ofReal_mul (by positivity),
            div_self hr'.ne']
          congr 1
          have : J.length ^ (1 / q) = J.length ^ (1 / Real.conjExponent r) *
              J.length ^ (1 / q - 1 / Real.conjExponent r) := by
            rw [← Real.rpow_add hJpos]; congr 1; ring
          rw [this]; ring
      _ = _ := by rw [Real.rpow_one]

end SmallIntervalsAll

section SmallSum

/-- **The small-interval estimate summed over `J ∈ 𝒥` meeting `16 I_T`** (L2137-L2144): for a finite
set `𝒥s` of elements of `𝒥` meeting `16 I_T` (their total length is at most `48 |I_T|`,
`MultitileTree.sum_length_le`),
`∑_{J ∈ 𝒥s} ∫_J |∑_{P ∈ T : |I| < C''|J|} ⟨f, φ_P⟩ φ_P a_P 1_E|^q ≤
(K ene den^{min(1, r'/q)})^q 48 |I_T|`. -/
theorem treeestimate_small_intervals_sum {r q : ℝ} (hr : 2 ≤ r) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (N : ℕ) (hN : 7 ≤ N) {C₁ C₂ C₃ : ℝ} (hC : AdmissibleConstants C₁ C₂ C₃) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {M : ℤ}, ρ.IsStd → ∀ (ch : ProfileChoice)
      (f : ℝ → ℂ) {E : Set ℝ}, MeasurableSet E → ∀ (L : Linearization r) {S : Set (Multitile ρ)}
      {ene den : ℝ}, 0 ≤ ene → 0 ≤ den → energy C₁ C₂ M ch f S ≤ ENNReal.ofReal ene →
      density C₁ C₂ M L E S ≤ ENNReal.ofReal den → ∀ (𝒯 : MultitileTree ρ),
      𝒯.IsTree C₁ C₂ M → (∀ P ∈ 𝒯.T, P.InSquare M) → (𝒯.T : Set (Multitile ρ)) ⊆ S →
      Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)) → 𝒯.T.Nonempty →
      ∀ (𝒥s : Finset Dyadic), (∀ J ∈ 𝒥s, 𝒯.IsMaxAvoiding J ∧
        (J.toSet ∩ 𝒯.I.dilate 16).Nonempty) →
        ∑ J ∈ 𝒥s, ∫⁻ x in J.toSet, ‖treeSum ch f L E
            (𝒯.T.filter fun P => P.I.length < Cpp C₁ C₂ * J.length) x‖ₑ ^ q ≤
          ENNReal.ofReal ((K * ene * den ^ (min 1 (Real.conjExponent r / q))) ^ q *
            (48 * 𝒯.I.length)) := by
  classical
  obtain ⟨K, hK0, hK⟩ := treeestimate_small_intervals hr hq1 hq2 N hN hC
  refine ⟨K, hK0, ?_⟩
  intro ρ _ M hρ ch f E hE L S ene den hene hden hen hde 𝒯 hT hsq hsub hsep hne 𝒥s h𝒥
  have hq0 : 0 < q := by linarith
  have hr' : 0 < Real.conjExponent r := by
    unfold Real.conjExponent
    exact div_pos (by linarith) (by linarith)
  have hσ0 : 0 ≤ min 1 (Real.conjExponent r / q) := le_min zero_le_one (by positivity)
  set A₀ : ℝ := K * ene * den ^ (min 1 (Real.conjExponent r / q)) with hA₀
  have hA₀0 : 0 ≤ A₀ := by positivity
  have hper : ∀ J ∈ 𝒥s, ∫⁻ x in J.toSet, ‖treeSum ch f L E
      (𝒯.T.filter fun P => P.I.length < Cpp C₁ C₂ * J.length) x‖ₑ ^ q ≤
      ENNReal.ofReal (A₀ ^ q * J.length) := by
    intro J hJ
    have hJpos := J.length_pos
    have hcore := hK hρ ch f hE L hene hden hen hde 𝒯 hT hsq hsub hsep (h𝒥 J hJ).1.1
    have hmeasJ : AEStronglyMeasurable (treeSum ch f L E
        (𝒯.T.filter fun P => P.I.length < Cpp C₁ C₂ * J.length)) (volume.restrict J.toSet) :=
      (measurable_treeSum ch f L hE _).aestronglyMeasurable
    have heq : ∫⁻ x in J.toSet, ‖treeSum ch f L E
        (𝒯.T.filter fun P => P.I.length < Cpp C₁ C₂ * J.length) x‖ₑ ^ q =
        (eLpNorm (treeSum ch f L E (𝒯.T.filter fun P => P.I.length < Cpp C₁ C₂ * J.length))
          (ENNReal.ofReal q) (volume.restrict J.toSet)) ^ q := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq0).ne'
        ENNReal.ofReal_ne_top hmeasJ, ENNReal.toReal_ofReal hq0.le, ← ENNReal.rpow_mul,
        one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
    rw [heq]
    have hAJ : 1 ≤ 1 + 𝒯.I.dist J / 𝒯.I.length := by
      have : 0 ≤ 𝒯.I.dist J / 𝒯.I.length := div_nonneg (𝒯.I.dist_nonneg J) 𝒯.I.length_pos.le
      linarith
    have hFpos : 0 < (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((N : ℤ) - 6)) := by positivity
    have hF1 : (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((N : ℤ) - 6)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ hAJ (by omega)
    have hB0 : 0 ≤ A₀ * J.length ^ (1 / q) *
        (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((N : ℤ) - 6)) := by positivity
    have hBq : (A₀ * J.length ^ (1 / q) *
        (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((N : ℤ) - 6))) ^ q ≤ A₀ ^ q * J.length := by
      rw [Real.mul_rpow (by positivity) hFpos.le, Real.mul_rpow hA₀0 (by positivity),
        ← Real.rpow_mul hJpos.le, one_div_mul_cancel hq0.ne', Real.rpow_one]
      have : ((1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((N : ℤ) - 6))) ^ q ≤ 1 := by
        calc ((1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((N : ℤ) - 6))) ^ q
            ≤ ((1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((N : ℤ) - 6))) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_ge hFpos hF1 hq1
          _ ≤ 1 := by rw [Real.rpow_one]; exact hF1
      calc A₀ ^ q * J.length * ((1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((N : ℤ) - 6))) ^ q
          ≤ A₀ ^ q * J.length * 1 := by gcongr
        _ = _ := mul_one _
    calc (eLpNorm (treeSum ch f L E (𝒯.T.filter fun P => P.I.length < Cpp C₁ C₂ * J.length))
          (ENNReal.ofReal q) (volume.restrict J.toSet)) ^ q
        ≤ (ENNReal.ofReal (A₀ * J.length ^ (1 / q) *
            (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((N : ℤ) - 6)))) ^ q :=
          ENNReal.rpow_le_rpow hcore hq0.le
      _ = ENNReal.ofReal ((A₀ * J.length ^ (1 / q) *
            (1 + 𝒯.I.dist J / 𝒯.I.length) ^ (-((N : ℤ) - 6))) ^ q) :=
          ENNReal.ofReal_rpow_of_nonneg hB0 hq0.le
      _ ≤ _ := ENNReal.ofReal_le_ofReal hBq
  calc ∑ J ∈ 𝒥s, ∫⁻ x in J.toSet, ‖treeSum ch f L E
        (𝒯.T.filter fun P => P.I.length < Cpp C₁ C₂ * J.length) x‖ₑ ^ q
      ≤ ∑ J ∈ 𝒥s, ENNReal.ofReal (A₀ ^ q * J.length) := Finset.sum_le_sum hper
    _ = ENNReal.ofReal (∑ J ∈ 𝒥s, A₀ ^ q * J.length) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun J _ => by have := J.length_pos; positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum]
        calc A₀ ^ q * ∑ J ∈ 𝒥s, J.length ≤ A₀ ^ q * (48 * 𝒯.I.length) :=
              mul_le_mul_of_nonneg_left (MultitileTree.sum_length_le hne hT.time 𝒥s h𝒥)
                (by positivity)
          _ = _ := rfl

end SmallSum

end PrimeCarleson.Proof.Oplus

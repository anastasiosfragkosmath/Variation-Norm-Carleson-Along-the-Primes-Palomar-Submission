module

public import PrimeCarleson.Proof.Oplus.TreeLarge.Fourier
public import PrimeCarleson.Proof.Oplus.TreeLarge.Variation
public import PrimeCarleson.Proof.Oplus.TreeLarge.Scales

/-!
# The `ℓ^r` sum of the `k`-blocks is a variation in the scale parameter ([O+] L2317-L2349)

Source: [O+] `schwartzchoice`, L2295–L2310; [O+] `intervalofscales`, L2317–L2321; [O+]
`intervalofscales2`, L2322–L2324; [O+] `treeestimatelargeintervals`, L2337–L2349 (L2295-L2349).

For an `l`-overlapping tree `T` satisfying (jconsolidation), the `k`-block at `x`
`∑_{P ∈ T : |I| ≥ C''|J|, ξ_{k-1}(x) ∈ ω_l, ξ_k(x) ∈ ω_h} ⟨f, φ_P⟩ φ_P(x)` is a sum over an
interval of scales of the tree (`block_convex`); blocks of different `k` use
disjoint sets of scales (the tiles of one scale have the same `ω_u`, and `ω_l < ω_h`); and the tail
`∑_{|I| ≥ 2^ℓ}` is `e_T (ψ_ℓ * g)` for the demodulated tree function `g` (`schwartzAvg_modTreeFn`).
Hence `variation_in_scale_parameter`: for every `x`

`∑_k |block_k(x)|^r ≤ V^r_{ℓ ≥ ℓ₀}(ψ_ℓ * g (x))^r`.

(The source does not state or prove that the scale windows of different `k` do not overlap; the
disjointness of the blocks gives it.)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

section TileLevel

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

/-- **`intervalofscales` for one block** (L2317-L2334): if `P₁, P₂ ∈ T` with `ξ_{k-1}(x) ∈ ω_l`,
`ξ_k(x) ∈ ω_h` and `P ∈ T` has a scale between those of `P₁` and `P₂`, then `P` has the same
property. (`j`-consolidation, `intervalofscales2`, for `ω_l`; `mem_ωh_middle` for `ω_h`.) -/
theorem block_convex (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd) {𝒯 : MultitileTree ρ}
    (hT : 𝒯.IsTree C₁ C₂ M) (hsep : Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)))
    (hjc : ∃ j : ℤ, ∀ P ∈ 𝒯.T, 𝒯.ξ - j * P.ωu.length ∈ P.ωl) {y y' : ℝ}
    {P₁ P₂ P : Multitile ρ} (hP₁ : P₁ ∈ 𝒯.T) (hP₂ : P₂ ∈ 𝒯.T) (hP : P ∈ 𝒯.T)
    (h1 : P₁.I.k ≤ P.I.k) (h2 : P.I.k ≤ P₂.I.k) (hl₁ : y ∈ P₁.ωl) (hl₂ : y ∈ P₂.ωl)
    (hh₁ : y' ∈ P₁.ωh) (hh₂ : y' ∈ P₂.ωh) : y ∈ P.ωl ∧ y' ∈ P.ωh := by
  rcases h1.eq_or_lt with e1 | lt1
  · have h : P₁.ωu = P.ωu := Multitile.ωu_eq_of_k_eq_of_tree hC hρ hT hsep.prop2 hP₁ hP e1
    have hl : P.ωl = P₁.ωl := by unfold Multitile.ωl; rw [h]
    have hh : P.ωh = P₁.ωh := by unfold Multitile.ωh; rw [h]
    rw [hl, hh]
    exact ⟨hl₁, hh₁⟩
  rcases h2.eq_or_lt with e2 | lt2
  · have h : P.ωu = P₂.ωu := Multitile.ωu_eq_of_k_eq_of_tree hC hρ hT hsep.prop2 hP hP₂ e2
    have hl : P.ωl = P₂.ωl := by unfold Multitile.ωl; rw [h]
    have hh : P.ωh = P₂.ωh := by unfold Multitile.ωh; rw [h]
    rw [hl, hh]
    exact ⟨hl₂, hh₂⟩
  have a1 := P₁.area
  have a2 := P.area
  have a3 := P₂.area
  have hωl : y ∈ P.ωl := by
    obtain ⟨j, hj⟩ := hjc
    have hwl : ∀ Q : Multitile ρ, Q.ωl = (ρ.ωlDyadic Q.ωu).toSet := fun Q =>
      Q.ωl_eq_toSet_ωlDyadic Fact.out
    have hmem : ∀ Q ∈ 𝒯.T, 𝒯.ξ - j * (ρ.ωlDyadic Q.ωu).length ∈ (ρ.ωlDyadic Q.ωu).toSet := by
      intro Q hQ
      have := hj Q hQ
      rw [hwl Q] at this
      simpa [Idx.length_ωlDyadic] using this
    have := mem_middle_of_jconsolidation (A := ρ.ωlDyadic P₁.ωu) (B := ρ.ωlDyadic P.ωu)
      (C := ρ.ωlDyadic P₂.ωu) (by simp only [Idx.ωlDyadic, Dyadic.shift]; omega)
      (by simp only [Idx.ωlDyadic, Dyadic.shift]; omega) (hmem P₁ hP₁) (hmem P hP) (hmem P₂ hP₂)
      (by rw [← hwl]; exact hl₁) (by rw [← hwl]; exact hl₂)
    rwa [← hwl] at this
  refine ⟨hωl, mem_ωh_middle ?_ ?_ hl₁ hωl hl₂ hh₁ hh₂⟩
  · exact Dyadic.two_mul_length_le_of_k_lt (by omega)
  · exact Dyadic.two_mul_length_le_of_k_lt (by omega)

end TileLevel


section VariationInScale

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ} {ψ : 𝓢(ℝ, ℂ)}

open Classical in
/-- **`treeestimatelargeintervals`** ([O+] L2337-L2349). Let `𝒯` be an
`l`-overlapping tree satisfying (jconsolidation) and the separation assumptions, `ψ` a cutoff with
`ψ̂ = 1` on `|ξ| ≤ (C₁ + C₃)/4` and `ψ̂ = 0` on `|ξ| ≥ C₁/2`, `g = e_T^{-1} ∑_{P ∈ T} ⟨f, φ_P⟩ φ_P`
(`modTreeFn`), and `pred` a predicate on scales that is monotone (for the printed use
`|I| ≥ C''|J|`) such that `ℓ₀ ≤ |I|`-scale for the multitiles with `pred`. Then for every `x`,
`∑_k |∑_{P ∈ T : pred, ξ_{k-1}(x) ∈ ω_l, ξ_k(x) ∈ ω_h} ⟨f, φ_P⟩ φ_P(x)|^r ≤
V^r_{ℓ ≥ ℓ₀}(ψ_ℓ * g(x))^r`. -/
theorem variation_in_scale_parameter (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (hψ : IsPsiCutoff (C₁ / 4) (C₃ / 4) ψ) {r : ℝ} (hr : 0 < r) (ch : ProfileChoice)
    (f : ℝ → ℂ) (L : Linearization r) {𝒯 : MultitileTree ρ} (hT : 𝒯.IsTree C₁ C₂ M)
    (hov : 𝒯.IsOverlapping C₂) (hsep : Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)))
    (hjc : ∃ j : ℤ, ∀ P ∈ 𝒯.T, 𝒯.ξ - j * P.ωu.length ∈ P.ωl) (pred : ℤ → Prop)
    (hpred : ∀ s s' : ℤ, s ≤ s' → pred s → pred s') (ℓ₀ : ℤ)
    (hℓ₀ : ∀ P ∈ 𝒯.T, pred P.I.k → ℓ₀ ≤ P.I.k) (x : ℝ) :
    ∑ k : Fin L.K, ‖∑ P ∈ 𝒯.T.filter (fun P => pred P.I.k ∧
        L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh),
          P.coeff ch f * P.wavePacket ch x‖ₑ ^ r ≤
      rVariationOn r ((↑) '' {ℓ : ℤ | ℓ₀ ≤ ℓ}) (fun t =>
        schwartzAvg ψ ⌊t⌋ (modTreeFn ch f 𝒯.ξ 𝒯.T) x) ^ r := by
  set T := 𝒯.T with hTdef
  set ξ := 𝒯.ξ with hξ
  set T' := T.filter (fun P => pred P.I.k) with hT'
  set S : Finset ℤ := T'.image (fun P => P.I.k) with hS
  have hC23 : 0 < C₂ - C₃ := by linarith [hC.lt₁]
  obtain ⟨N₀, hN₀⟩ := pow_unbounded_of_one_lt (2 * C₁ / (C₂ - C₃)) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨B, hB⟩ : ∃ B : ℤ, ∀ P ∈ T, P.I.k ≤ B := by
    obtain ⟨B, hB⟩ := (T.image (fun P => P.I.k)).bddAbove
    exact ⟨B, fun P hP => hB (Finset.mem_image_of_mem _ hP)⟩
  set top : ℤ := max B ℓ₀ + N₀ + 1 with htop
  have htopk : ∀ P ∈ T, P.I.k < top := fun P hP => by
    have := hB P hP
    have : B ≤ max B ℓ₀ := le_max_left _ _
    omega
  have htopgap : ∀ P ∈ T, 2 * C₁ / (C₂ - C₃) ≤ (2 : ℝ) ^ (top - P.I.k) := by
    intro P hP
    have h1 : (N₀ : ℤ) ≤ top - P.I.k := by
      have := hB P hP
      have : B ≤ max B ℓ₀ := le_max_left _ _
      omega
    calc 2 * C₁ / (C₂ - C₃) ≤ (2 : ℝ) ^ N₀ := hN₀.le
      _ = (2 : ℝ) ^ (N₀ : ℤ) := (zpow_natCast _ _).symm
      _ ≤ (2 : ℝ) ^ (top - P.I.k) := zpow_le_zpow_right₀ (by norm_num) h1
  have hSsub : ∀ s ∈ S, ∃ P ∈ T', P.I.k = s := fun s hs => by
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hs
    exact ⟨P, hP, rfl⟩
  have hT'T : T' ⊆ T := Finset.filter_subset _ _
  have hStop : ∀ s ∈ S, s < top := fun s hs => by
    obtain ⟨P, hP, rfl⟩ := hSsub s hs
    exact htopk P (hT'T hP)
  have hℓ₀top : ℓ₀ ≤ top := by
    have : ℓ₀ ≤ max B ℓ₀ := le_max_right _ _
    omega
  -- the demodulated blocks and the tail
  set G : ℤ → ℂ := fun s => ∑ P ∈ T'.filter (fun P => P.I.k = s),
    P.coeff ch f * modPacket ch ξ P x with hG
  set A : ℤ → ℂ := fun ℓ => schwartzAvg ψ ℓ (modTreeFn ch f ξ T) x with hA
  have hfib : ∀ ℓ : ℤ, ∑ P ∈ T'.filter (fun P => ℓ ≤ P.I.k), P.coeff ch f * modPacket ch ξ P x =
      ∑ s ∈ S.filter (fun s => ℓ ≤ s), G s := by
    intro ℓ
    rw [← Finset.sum_fiberwise_of_maps_to (s := T'.filter (fun P => ℓ ≤ P.I.k))
      (t := S.filter (fun s => ℓ ≤ s)) (g := fun P => P.I.k) (f := fun P =>
        P.coeff ch f * modPacket ch ξ P x) (fun P hP => by
        have := Finset.mem_filter.1 hP
        exact Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ this.1, this.2⟩)]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' := (Finset.mem_filter.1 hs).2
    rw [hG, Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun P _ => ?_) fun _ _ => rfl
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hs', h⟩
  have hH : ∀ ℓ ∈ insert top S, A ℓ = ∑ s ∈ S.filter (fun s => ℓ ≤ s), G s := by
    intro ℓ hℓ
    have hgap : ∀ P ∈ T, ℓ ≤ P.I.k ∨ 2 * C₁ / (C₂ - C₃) ≤ (2 : ℝ) ^ (ℓ - P.I.k) := by
      intro P hP
      rcases Finset.mem_insert.1 hℓ with rfl | hℓS
      · exact Or.inr (htopgap P hP)
      · obtain ⟨P₀, hP₀, rfl⟩ := hSsub ℓ hℓS
        by_cases hle : P₀.I.k ≤ P.I.k
        · exact Or.inl hle
        · exact Or.inr (scale_gap_of_separation hC hsep.scales hP (hT'T hP₀) (by omega))
    have hloc := schwartzAvg_modTreeFn hC hρ hψ ch f ξ T hov hgap
    have hfil : T.filter (fun P => ℓ ≤ P.I.k) = T'.filter (fun P => ℓ ≤ P.I.k) := by
      rcases Finset.mem_insert.1 hℓ with rfl | hℓS
      · have e1 : T.filter (fun P => top ≤ P.I.k) = ∅ :=
          Finset.filter_eq_empty_iff.2 fun P hP => not_le.2 (htopk P hP)
        have e2 : T'.filter (fun P => top ≤ P.I.k) = ∅ :=
          Finset.filter_eq_empty_iff.2 fun P hP => not_le.2 (htopk P (hT'T hP))
        rw [e1, e2]
      · obtain ⟨P₀, hP₀, rfl⟩ := hSsub ℓ hℓS
        have hp0 : pred P₀.I.k := (Finset.mem_filter.1 hP₀).2
        ext P
        simp only [hT', Finset.mem_filter]
        constructor
        · rintro ⟨hP, hle⟩
          exact ⟨⟨hP, hpred _ _ hle hp0⟩, hle⟩
        · rintro ⟨⟨hP, -⟩, hle⟩
          exact ⟨hP, hle⟩
    rw [hA]
    simp only
    rw [hloc]
    unfold modTreeFn
    rw [hfil, hfib]
  -- the blocks
  set blk : Fin L.K → Finset (Multitile ρ) := fun k => T'.filter (fun P =>
      L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh) with hblk
  set Q : Fin L.K → Finset ℤ := fun k => (blk k).image (fun P => P.I.k) with hQ
  have hblkT : ∀ k, blk k ⊆ T' := fun k => Finset.filter_subset _ _
  have hQS : ∀ k, Q k ⊆ S := fun k => Finset.image_subset_image (hblkT k)
  have hclos : ∀ k, ∀ P ∈ T', P.I.k ∈ Q k → P ∈ blk k := by
    intro k P hP hk
    obtain ⟨P', hP', hkk⟩ := Finset.mem_image.1 hk
    have hP'm := Finset.mem_filter.1 hP'
    have hωu : P'.ωu = P.ωu :=
      Multitile.ωu_eq_of_k_eq_of_tree hC hρ hT hsep.prop2 (hT'T hP'm.1) (hT'T hP) hkk
    refine Finset.mem_filter.2 ⟨hP, ?_, ?_⟩
    · have : P.ωl = P'.ωl := by unfold Multitile.ωl; rw [hωu]
      rw [this]; exact hP'm.2.1
    · have : P.ωh = P'.ωh := by unfold Multitile.ωh; rw [hωu]
      rw [this]; exact hP'm.2.2
  set 𝒦 := Finset.univ.filter (fun k : Fin L.K => (Q k).Nonempty) with h𝒦
  have hdisj : ∀ k ∈ 𝒦, ∀ k' ∈ 𝒦, k ≠ k' → Disjoint (Q k) (Q k') := by
    intro k _ k' _ hkk'
    refine Finset.disjoint_left.2 fun s hs hs' => ?_
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hs
    have hPk := (Finset.mem_filter.1 hP).2
    have hP'' : P ∈ blk k' := hclos k' P (Finset.mem_filter.1 hP).1 hs'
    have hPk' := (Finset.mem_filter.1 hP'').2
    have e1 : L.ξ k.castSucc x < L.ξ k'.succ x := P.lt_of_mem_ωl_of_mem_ωh hPk.1 hPk'.2
    have e2 : L.ξ k'.castSucc x < L.ξ k.succ x := P.lt_of_mem_ωl_of_mem_ωh hPk'.1 hPk.2
    rcases lt_or_gt_of_ne hkk' with h | h
    · have : L.ξ k.succ x ≤ L.ξ k'.castSucc x := (L.strictMono_ξ x).monotone (by
        rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; exact Fin.lt_def.1 h)
      linarith
    · have : L.ξ k'.succ x ≤ L.ξ k.castSucc x := (L.strictMono_ξ x).monotone (by
        rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; exact Fin.lt_def.1 h)
      linarith
  have hconv : ∀ k ∈ 𝒦, ∀ s ∈ S, ∀ s₁ ∈ Q k, ∀ s₂ ∈ Q k, s₁ ≤ s → s ≤ s₂ → s ∈ Q k := by
    intro k _ s hs s₁ hs₁ s₂ hs₂ h1 h2
    obtain ⟨P₁, hP₁, rfl⟩ := Finset.mem_image.1 hs₁
    obtain ⟨P₂, hP₂, rfl⟩ := Finset.mem_image.1 hs₂
    obtain ⟨P, hP, rfl⟩ := hSsub s hs
    have hP₁m := Finset.mem_filter.1 hP₁
    have hP₂m := Finset.mem_filter.1 hP₂
    obtain ⟨hl, hh⟩ := block_convex hC hρ hT hsep hjc (hT'T hP₁m.1) (hT'T hP₂m.1) (hT'T hP) h1 h2
      hP₁m.2.1 hP₂m.2.1 hP₁m.2.2 hP₂m.2.2
    exact Finset.mem_image.2 ⟨P, Finset.mem_filter.2 ⟨hP, hl, hh⟩, rfl⟩
  have hbsum : ∀ k, ∑ s ∈ Q k, G s = ∑ P ∈ blk k, P.coeff ch f * modPacket ch ξ P x := by
    intro k
    rw [← Finset.sum_fiberwise_of_maps_to (s := blk k) (t := Q k) (g := fun P => P.I.k)
      (f := fun P => P.coeff ch f * modPacket ch ξ P x)
      (fun P hP => Finset.mem_image_of_mem _ hP)]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hG]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext P
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hP, hk⟩
      exact ⟨hclos k P hP (hk ▸ hs), hk⟩
    · rintro ⟨hP, hk⟩
      exact ⟨hblkT k hP, hk⟩
  have hwin := sum_blocks_le_rVariationOn hr 𝒦 S top hStop G A hH Q (fun k _ => hQS k)
    (fun k hk => (Finset.mem_filter.1 hk).2) hdisj hconv
  have hterm : ∀ k : Fin L.K, ‖∑ P ∈ T.filter (fun P => pred P.I.k ∧
        L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh),
          P.coeff ch f * P.wavePacket ch x‖ₑ = ‖∑ s ∈ Q k, G s‖ₑ := by
    intro k
    rw [hbsum k]
    have hfe : T.filter (fun P => pred P.I.k ∧ L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh) =
        blk k := by
      ext P
      simp only [hblk, hT', Finset.mem_filter, and_assoc]
    rw [hfe]
    have : ∑ P ∈ blk k, P.coeff ch f * modPacket ch ξ P x =
        (∑ P ∈ blk k, P.coeff ch f * P.wavePacket ch x) * e (-(x * ξ)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun P _ => ?_
      unfold modPacket
      ring
    rw [this, enorm_mul]
    have h1 : ‖e (-(x * ξ))‖ₑ = 1 := by
      rw [← ofReal_norm, norm_e, ENNReal.ofReal_one]
    rw [h1, mul_one]
  have hsum : ∑ k : Fin L.K, ‖∑ P ∈ T.filter (fun P => pred P.I.k ∧
        L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh),
          P.coeff ch f * P.wavePacket ch x‖ₑ ^ r = ∑ k ∈ 𝒦, ‖∑ s ∈ Q k, G s‖ₑ ^ r := by
    simp only [hterm]
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun k _ hk => ?_).symm
    have : ¬ (Q k).Nonempty := fun h => hk (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    rw [Finset.not_nonempty_iff_eq_empty.1 this, Finset.sum_empty, enorm_zero,
      ENNReal.zero_rpow_of_pos hr]
  rw [hsum]
  have hsubset : ((↑) '' (↑(insert top S) : Set ℤ) : Set ℝ) ⊆ (↑) '' {ℓ : ℤ | ℓ₀ ≤ ℓ} := by
    rintro _ ⟨ℓ, hℓ, rfl⟩
    refine ⟨ℓ, ?_, rfl⟩
    rcases Finset.mem_insert.1 (Finset.mem_coe.1 hℓ) with rfl | hℓS
    · exact hℓ₀top
    · obtain ⟨P, hP, rfl⟩ := hSsub ℓ hℓS
      exact hℓ₀ P (hT'T hP) (Finset.mem_filter.1 hP).2
  exact hwin.trans (ENNReal.rpow_le_rpow (rVariationOn_mono_set hsubset _) hr.le)

end VariationInScale

end PrimeCarleson.Proof.Oplus

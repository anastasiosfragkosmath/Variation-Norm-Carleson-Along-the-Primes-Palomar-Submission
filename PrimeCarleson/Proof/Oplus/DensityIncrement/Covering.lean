module

public import PrimeCarleson.Proof.Oplus.DensityIncrement.Truncation

/-!
# The covering selection and the sum over `ℓ` ([O+] L1942-L1967)

Source: [O+] `densityincrementprop`, L1942–L1954; [O+] `densityincrementprop`, L1955–L1966
(L1942-L1967): for each `ℓ` let
`𝒯^{(ℓ)} = {T_j : ℓ_j = ℓ}`;
choose `T^{(ℓ)}_{k+1}` of maximal `|I|` in what is left, and `𝒯^{(ℓ)}_{k+1}` the elements of what is
left whose rectangle `2^ℓ I_T × ω_T` meets
`2^ℓ I_{T^{(ℓ)}_{k+1}} × ω_{T^{(ℓ)}_{k+1}}`. "Using the fact that the tiles `I_{T_j} × ω_{T_j}` are
pairwise disjoint, and (twice) the fact that `|I_T| ≤ |I_{T^{(ℓ)}_j}|` for every `T ∈ 𝒯^{(ℓ)}_j`,
we see that for each `j`, `∑_{T ∈ 𝒯^{(ℓ)}_j} |I_T| ≲ 2^ℓ |I_{T^{(ℓ)}_j}|`." Then by
(trunctreehaslargedensity) and the disjointness of the rectangles `2^ℓ I_{T^{(ℓ)}_j} ×
ω_{T^{(ℓ)}_j}` the sum is at most `2^{-2ℓ} den^{-r'} |E|`.

* `covering_local_count`: the local count; the `T` with rectangle meeting that of `T_{j₀}` have
  their `I_T` in an interval of length `2^{ℓ+2}|I_{T_{j₀}}|` and `ω_T` containing one of the two
  end points of `ω_{T_{j₀}}`, and the tiles through a common frequency have disjoint time intervals;
* `exists_covering_rep`: the greedy selection, by recursion on the cardinality of the finite family
  (the source's `𝒯 = ⋃_j 𝒯_j` is the equation `∑_s ≤ 2^{ℓ+3} ∑_{rep}`; the representatives have
  pairwise disjoint rectangles, which the source states only at the point of use, L1966);
* `sum_indicator_tailSum_le_one`, `sum_lintegral_le_volume`: the counting function is at most `1`
  and the Tonelli step, using `∑_k |a_k(x)|^{r'} = 1`;
* `covering_fiber_bound`: `8^ℓ den^{r'} ∑_{𝒯^{(ℓ)}} |I_T| ≤ 2^{ℓ+3} 2^{8+r'} |E|`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section Covering

variable {ρ : Idx} {C₂ : ℝ}

/-- The tile `I_T × ω_T` of a tree. -/
def MultitileTree.tile (C₂ : ℝ) (𝒯 : MultitileTree ρ) : Set (ℝ × ℝ) := 𝒯.I.toSet ×ˢ 𝒯.ωT C₂

/-- The dilated rectangle `2^ℓ I_T × ω_T`. -/
def MultitileTree.dilTile (C₂ : ℝ) (ℓ : ℕ) (𝒯 : MultitileTree ρ) : Set (ℝ × ℝ) :=
  𝒯.I.dilate ((2 : ℝ) ^ ℓ) ×ˢ 𝒯.ωT C₂

/-- The Lebesgue measure of the time intervals of trees with a common frequency and disjoint tiles
is at most that of a set containing them. -/
theorem sum_length_le_volume_of_common {ι : Type*} (s : Finset ι) (T : ι → MultitileTree ρ)
    (η : ℝ) (hη : ∀ j ∈ s, η ∈ (T j).ωT C₂)
    (hdisj : ∀ j ∈ s, ∀ j' ∈ s, j ≠ j' → Disjoint ((T j).tile C₂) ((T j').tile C₂)) {B : Set ℝ}
    (hB : ∀ j ∈ s, (T j).I.toSet ⊆ B) :
    ∑ j ∈ s, ENNReal.ofReal (T j).I.length ≤ volume B := by
  have hpw : (s : Set ι).PairwiseDisjoint fun j => (T j).I.toSet := by
    intro j hj j' hj' hne
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    exact Set.disjoint_left.1 (hdisj j hj j' hj' hne) (show (x, η) ∈ (T j).tile C₂ from
      ⟨hx, hη j hj⟩) (show (x, η) ∈ (T j').tile C₂ from ⟨hx', hη j' hj'⟩)
  classical
  calc ∑ j ∈ s, ENNReal.ofReal (T j).I.length = ∑ j ∈ s, volume (T j).I.toSet := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Dyadic.volume_toSet]
    _ = volume (⋃ j ∈ s, (T j).I.toSet) :=
        (measure_biUnion_finset hpw fun j _ => (T j).I.measurableSet_toSet).symm
    _ ≤ volume B := measure_mono (Set.iUnion₂_subset hB)

open Classical in
/-- **The local count** (L1951-L1954): if `|I_{T_j}| ≤ |I_{T_{j₀}}|` for `j ∈ s` and the tiles
`I_{T_j} × ω_{T_j}` are pairwise disjoint, then
`∑ {|I_{T_j}| : j ∈ s, (2^ℓ I_{T_j} × ω_{T_j}) ∩ (2^ℓ I_{T_{j₀}} × ω_{T_{j₀}}) ≠ ∅} ≤
2^{ℓ+3} |I_{T_{j₀}}|`. The `j` in question have `I_{T_j}` in an interval of length `≤ 2^{ℓ+2}
|I_{T_{j₀}}|`, and `ω_{T_j}` (of length at least that of `ω_{T_{j₀}}`) contains one of the two end
points of `ω_{T_{j₀}}`; the tiles through one of these two frequencies have disjoint time
intervals. -/
theorem covering_local_count (hC₂ : 1 < C₂) (ℓ : ℕ) (T : ℕ → MultitileTree ρ) (s : Finset ℕ)
    (j₀ : ℕ) (hmax : ∀ j ∈ s, (T j).I.length ≤ (T j₀).I.length)
    (hdisj : ∀ j ∈ s, ∀ j' ∈ s, j ≠ j' → Disjoint ((T j).tile C₂) ((T j').tile C₂)) :
    ∑ j ∈ s.filter (fun j => ¬ Disjoint ((T j).dilTile C₂ ℓ) ((T j₀).dilTile C₂ ℓ)),
      ENNReal.ofReal (T j).I.length ≤ ENNReal.ofReal (2 ^ (ℓ + 3) * (T j₀).I.length) := by
  classical
  set F := s.filter (fun j => ¬ Disjoint ((T j).dilTile C₂ ℓ) ((T j₀).dilTile C₂ ℓ)) with hF
  have hl₀ := (T j₀).I.length_pos
  set l₀ := (T j₀).I.length with hl₀def
  set c₀ := (T j₀).I.center with hc₀
  set r₀ : ℝ := (C₂ - 1) / (4 * l₀) with hr₀
  set q : ℝ := (2 : ℝ) ^ ℓ with hq
  have hq1 : 1 ≤ q := one_le_pow₀ (by norm_num)
  set B : Set ℝ := Icc (c₀ - (q + 1 / 2) * l₀) (c₀ + (q + 1 / 2) * l₀) with hB
  have hBvol : volume B ≤ ENNReal.ofReal (2 ^ (ℓ + 2) * l₀) := by
    rw [hB, Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    rw [pow_add]
    nlinarith
  have hjF : ∀ j ∈ F, (T j).I.toSet ⊆ B ∧
      ((T j₀).ξ - r₀ ∈ (T j).ωT C₂ ∨ (T j₀).ξ + r₀ ∈ (T j).ωT C₂) := by
    intro j hj
    obtain ⟨hjs, hnd⟩ := Finset.mem_filter.1 hj
    obtain ⟨⟨x, η⟩, ⟨hx1, hη1⟩, ⟨hx2, hη2⟩⟩ := Set.not_disjoint_iff.1 hnd
    have hlj := hmax j hjs
    have hljpos := (T j).I.length_pos
    have hqlj : q * (T j).I.length ≤ q * l₀ := mul_le_mul_of_nonneg_left hlj (by linarith)
    constructor
    · intro y hy
      simp only [Dyadic.dilate, mem_Ico] at hx1 hx2
      have hy' := hy
      rw [Dyadic.mem_toSet, (T j).I.right_eq] at hy'
      have hcj := (T j).I.center_eq
      simp only [hB, mem_Icc]
      constructor <;> nlinarith [hx1.1, hx1.2, hx2.1, hx2.2, hy'.1, hy'.2]
    · set rj : ℝ := (C₂ - 1) / (4 * (T j).I.length) with hrjdef
      have hη1' : (T j).ξ - rj ≤ η ∧ η < (T j).ξ + rj := hη1
      have hη2' : (T j₀).ξ - r₀ ≤ η ∧ η < (T j₀).ξ + r₀ := hη2
      have hrj : r₀ ≤ rj := by
        rw [hr₀, hrjdef]
        exact div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
      have hr0 : 0 < r₀ := by rw [hr₀]; apply div_pos <;> linarith
      change (T j₀).ξ - r₀ ∈ Ico ((T j).ξ - rj) ((T j).ξ + rj) ∨
        (T j₀).ξ + r₀ ∈ Ico ((T j).ξ - rj) ((T j).ξ + rj)
      by_cases hc : (T j).ξ - rj ≤ (T j₀).ξ - r₀
      · left; exact ⟨hc, by linarith [hη1'.2, hη2'.1]⟩
      · right
        rw [not_le] at hc
        exact ⟨by linarith [hη1'.1, hη2'.2], by linarith⟩
  set F₁ := F.filter (fun j => (T j₀).ξ - r₀ ∈ (T j).ωT C₂) with hF₁
  set F₂ := F.filter (fun j => (T j₀).ξ + r₀ ∈ (T j).ωT C₂) with hF₂
  have hdisj' : ∀ {G : Finset ℕ}, G ⊆ s → ∀ j ∈ G, ∀ j' ∈ G, j ≠ j' →
      Disjoint ((T j).tile C₂) ((T j').tile C₂) := fun hG j hj j' hj' hne =>
    hdisj j (hG hj) j' (hG hj') hne
  have hFs : F ⊆ s := Finset.filter_subset _ _
  have h1 : ∑ j ∈ F₁, ENNReal.ofReal (T j).I.length ≤ volume B :=
    sum_length_le_volume_of_common F₁ T _ (fun j hj => (Finset.mem_filter.1 hj).2)
      (hdisj' ((Finset.filter_subset _ _).trans hFs))
      (fun j hj => (hjF j (Finset.mem_filter.1 hj).1).1)
  have h2 : ∑ j ∈ F₂, ENNReal.ofReal (T j).I.length ≤ volume B :=
    sum_length_le_volume_of_common F₂ T _ (fun j hj => (Finset.mem_filter.1 hj).2)
      (hdisj' ((Finset.filter_subset _ _).trans hFs))
      (fun j hj => (hjF j (Finset.mem_filter.1 hj).1).1)
  have hsub : F ⊆ F₁ ∪ F₂ := by
    intro j hj
    rcases (hjF j hj).2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hj, h⟩)
  calc ∑ j ∈ F, ENNReal.ofReal (T j).I.length
      ≤ ∑ j ∈ F₁ ∪ F₂, ENNReal.ofReal (T j).I.length := Finset.sum_le_sum_of_subset hsub
    _ ≤ ∑ j ∈ F₁, ENNReal.ofReal (T j).I.length + ∑ j ∈ F₂, ENNReal.ofReal (T j).I.length := by
        rw [← Finset.sum_union_inter]
        exact le_self_add
    _ ≤ volume B + volume B := add_le_add h1 h2
    _ ≤ ENNReal.ofReal (2 ^ (ℓ + 2) * l₀) + ENNReal.ofReal (2 ^ (ℓ + 2) * l₀) :=
        add_le_add hBvol hBvol
    _ = ENNReal.ofReal (2 ^ (ℓ + 3) * l₀) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

open Classical in
/-- **The covering selection** (L1942-L1954): a finite family `s` of trees with pairwise disjoint
tiles `I_T × ω_T` has a subfamily `rep` (the `T^{(ℓ)}_j`) with
`∑_{s} |I_T| ≤ 2^{ℓ+3} ∑_{rep} |I_T|` (by the local count) and such that the rectangles
`2^ℓ I_T × ω_T`, `T ∈ rep`, are pairwise disjoint. The recursion is on the cardinality of `s`. -/
theorem exists_covering_rep (hC₂ : 1 < C₂) (ℓ : ℕ) (T : ℕ → MultitileTree ρ) (s : Finset ℕ)
    (hdisj : ∀ j ∈ s, ∀ j' ∈ s, j ≠ j' → Disjoint ((T j).tile C₂) ((T j').tile C₂)) :
    ∃ rep ⊆ s, ∑ j ∈ s, ENNReal.ofReal (T j).I.length ≤
        ENNReal.ofReal (2 ^ (ℓ + 3)) * ∑ j ∈ rep, ENNReal.ofReal (T j).I.length ∧
      ∀ j ∈ rep, ∀ j' ∈ rep, j ≠ j' →
        Disjoint ((T j).dilTile C₂ ℓ) ((T j').dilTile C₂ ℓ) := by
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
    · obtain ⟨j₀, hj₀, hmax⟩ := Finset.exists_max_image s (fun j => (T j).I.length) hne
      set F := s.filter (fun j => ¬ Disjoint ((T j).dilTile C₂ ℓ) ((T j₀).dilTile C₂ ℓ))
        with hF
      have hj₀F : j₀ ∈ F := by
        refine Finset.mem_filter.2 ⟨hj₀, ?_⟩
        rw [Set.not_disjoint_iff]
        have hl := (T j₀).I.length_pos
        have hr0 : 0 < (C₂ - 1) / (4 * (T j₀).I.length) := by apply div_pos <;> linarith
        refine ⟨((T j₀).I.center, (T j₀).ξ), ?_, ?_⟩ <;>
        · refine ⟨?_, ?_⟩
          · exact (T j₀).I.toSet_subset_dilate (one_le_pow₀ (by norm_num)) (T j₀).I.center_mem_toSet
          · change (T j₀).ξ ∈ Ico _ _
            constructor <;> linarith
      have hFs : F ⊆ s := Finset.filter_subset _ _
      have hlt : s \ F ⊂ s := Finset.sdiff_ssubset hFs ⟨j₀, hj₀F⟩
      obtain ⟨rep', hsub', hsum', hdis'⟩ := ih (s \ F) hlt
        (fun j hj j' hj' hne => hdisj j (Finset.sdiff_subset hj) j' (Finset.sdiff_subset hj') hne)
      have hj₀rep : j₀ ∉ rep' := fun h => (Finset.mem_sdiff.1 (hsub' h)).2 hj₀F
      have hcount := covering_local_count hC₂ ℓ T s j₀ (fun j hj => hmax j hj) hdisj
      refine ⟨insert j₀ rep', Finset.insert_subset hj₀ (hsub'.trans Finset.sdiff_subset), ?_, ?_⟩
      · rw [Finset.sum_insert hj₀rep, ← Finset.sum_sdiff hFs]
        calc ∑ j ∈ s \ F, ENNReal.ofReal (T j).I.length + ∑ j ∈ F, ENNReal.ofReal (T j).I.length
            ≤ ENNReal.ofReal (2 ^ (ℓ + 3)) * ∑ j ∈ rep', ENNReal.ofReal (T j).I.length +
              ENNReal.ofReal (2 ^ (ℓ + 3) * (T j₀).I.length) := add_le_add hsum' hcount
          _ = _ := by
            rw [ENNReal.ofReal_mul (by positivity), mul_add, add_comm]
      · intro j hj j' hj' hne
        rw [Finset.mem_insert] at hj hj'
        rcases hj with rfl | hj <;> rcases hj' with rfl | hj'
        · exact absurd rfl hne
        · have := (Finset.mem_sdiff.1 (hsub' hj')).2
          have h2 := (Finset.mem_sdiff.1 (hsub' hj')).1
          rw [hF, Finset.mem_filter, not_and, not_not] at this
          exact (this h2).symm
        · have := (Finset.mem_sdiff.1 (hsub' hj)).2
          have h2 := (Finset.mem_sdiff.1 (hsub' hj)).1
          rw [hF, Finset.mem_filter, not_and, not_not] at this
          exact this h2
        · exact hdis' j hj j' hj' hne

/-- `∑_k |a_k(x)|^{r'} = 1` in `ℝ≥0∞`. -/
theorem Linearization.sum_enorm_rpow_eq_one {r : ℝ} (hr : 1 < r) (L : Linearization r)
    (x : ℝ) : ∑ k : Fin L.K, ‖L.a k x‖ₑ ^ Real.conjExponent r = 1 := by
  have hp : 0 ≤ Real.conjExponent r := by
    unfold Real.conjExponent
    exact (div_pos (by linarith) (by linarith)).le
  have h := L.sum_norm_rpow x
  have : ∀ k : Fin L.K, ‖L.a k x‖ₑ ^ Real.conjExponent r =
      ENNReal.ofReal (‖L.a k x‖ ^ Real.conjExponent r) := fun k => by
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp, ofReal_norm]
  simp only [this]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity), h, ENNReal.ofReal_one]

/-- At most one of finitely many pairwise disjoint sets contains a given point. -/
theorem sum_indicator_prod_le_one {ι : Type*} (s : Finset ι) (R : ι → Set (ℝ × ℝ))
    (hR : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (R i) (R j)) (z : ℝ × ℝ) :
    ∑ i ∈ s, (R i).indicator (fun _ => (1 : ℝ≥0∞)) z ≤ 1 := by
  classical
  simp only [Set.indicator_apply]
  rw [Finset.sum_boole]
  have : (s.filter (fun i => z ∈ R i)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hne
    exact Set.disjoint_left.1 (hR a (Finset.mem_filter.1 ha).1 b (Finset.mem_filter.1 hb).1 hne)
      (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2
  exact_mod_cast this

/-- **The disjointness of the dilated rectangles bounds the counting function by one**
(L1957-L1966): `∑_{T ∈ rep} 1_{2^ℓ I_T}(x) ∑_{k : ξ_{k-1}(x) ∈ ω_T} |a_k(x)|^{r'} ≤ 1`. -/
theorem sum_indicator_tailSum_le_one {r : ℝ} (hr : 1 < r) (L : Linearization r) (ℓ : ℕ)
    (T : ℕ → MultitileTree ρ) (rep : Finset ℕ)
    (hrect : ∀ j ∈ rep, ∀ j' ∈ rep, j ≠ j' →
      Disjoint ((T j).dilTile C₂ ℓ) ((T j').dilTile C₂ ℓ)) (x : ℝ) :
    ∑ j ∈ rep, ((T j).I.dilate ((2 : ℝ) ^ ℓ)).indicator (L.tailSum ((T j).ωT C₂)) x ≤ 1 := by
  have h1 : ∀ j, ((T j).I.dilate ((2 : ℝ) ^ ℓ)).indicator (L.tailSum ((T j).ωT C₂)) x =
      ∑ k : Fin L.K, ‖L.a k x‖ₑ ^ Real.conjExponent r *
        ((T j).dilTile C₂ ℓ).indicator (fun _ => (1 : ℝ≥0∞)) (x, L.ξ k.castSucc x) := fun j => by
    by_cases hx : x ∈ (T j).I.dilate ((2 : ℝ) ^ ℓ)
    · rw [Set.indicator_of_mem hx]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : L.ξ k.castSucc x ∈ (T j).ωT C₂
      · have : (x, L.ξ k.castSucc x) ∈ (T j).dilTile C₂ ℓ := ⟨hx, hk⟩
        rw [Set.indicator_of_mem hk, Set.indicator_of_mem this]
      · have : (x, L.ξ k.castSucc x) ∉ (T j).dilTile C₂ ℓ := fun h => hk h.2
        rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem this]
    · rw [Set.indicator_of_notMem hx]
      symm
      refine Finset.sum_eq_zero fun k _ => ?_
      have : (x, L.ξ k.castSucc x) ∉ (T j).dilTile C₂ ℓ := fun h => hx h.1
      rw [Set.indicator_of_notMem this, mul_zero]
  simp only [h1]
  rw [Finset.sum_comm]
  calc ∑ k : Fin L.K, ∑ j ∈ rep, ‖L.a k x‖ₑ ^ Real.conjExponent r *
        ((T j).dilTile C₂ ℓ).indicator (fun _ => (1 : ℝ≥0∞)) (x, L.ξ k.castSucc x)
      = ∑ k : Fin L.K, ‖L.a k x‖ₑ ^ Real.conjExponent r * ∑ j ∈ rep,
        ((T j).dilTile C₂ ℓ).indicator (fun _ => (1 : ℝ≥0∞)) (x, L.ξ k.castSucc x) :=
        Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ k : Fin L.K, ‖L.a k x‖ₑ ^ Real.conjExponent r * 1 :=
        Finset.sum_le_sum fun k _ => mul_le_mul' le_rfl (sum_indicator_prod_le_one rep _ hrect _)
    _ = 1 := by simp only [mul_one]; exact L.sum_enorm_rpow_eq_one hr x

/-- **The integral of the counting function** (L1957-L1966): for trees with pairwise disjoint
rectangles `2^ℓ I_T × ω_T`, `∑_{T} ∫_{E ∩ 2^ℓ I_T} ∑_{k : ξ_{k-1}(x) ∈ ω_T} |a_k(x)|^{r'} dx ≤
|E|` (using `∑_k |a_k(x)|^{r'} = 1`, Tonelli for the finite sum). -/
theorem sum_lintegral_le_volume {r : ℝ} (hr : 1 < r) (L : Linearization r) (E : Set ℝ) (ℓ : ℕ)
    (T : ℕ → MultitileTree ρ) (rep : Finset ℕ)
    (hrect : ∀ j ∈ rep, ∀ j' ∈ rep, j ≠ j' →
      Disjoint ((T j).dilTile C₂ ℓ) ((T j').dilTile C₂ ℓ)) :
    ∑ j ∈ rep, ∫⁻ x in E ∩ (T j).I.dilate ((2 : ℝ) ^ ℓ), L.tailSum ((T j).ωT C₂) x ≤
      volume E := by
  have hG : ∀ j, Measurable (L.tailSum ((T j).ωT C₂)) := fun j =>
    L.measurable_tailSum_of_measurableSet measurableSet_Ico
  have hD : ∀ j, MeasurableSet ((T j).I.dilate ((2 : ℝ) ^ ℓ)) := fun j => measurableSet_Ico
  calc ∑ j ∈ rep, ∫⁻ x in E ∩ (T j).I.dilate ((2 : ℝ) ^ ℓ), L.tailSum ((T j).ωT C₂) x
      = ∑ j ∈ rep, ∫⁻ x in E, ((T j).I.dilate ((2 : ℝ) ^ ℓ)).indicator
          (L.tailSum ((T j).ωT C₂)) x := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_indicator (hD j), Measure.restrict_restrict (hD j), Set.inter_comm]
    _ = ∫⁻ x in E, ∑ j ∈ rep, ((T j).I.dilate ((2 : ℝ) ^ ℓ)).indicator
          (L.tailSum ((T j).ωT C₂)) x :=
        (lintegral_finsetSum' _ fun j _ => ((hG j).indicator (hD j)).aemeasurable).symm
    _ ≤ ∫⁻ x in E, 1 := lintegral_mono fun x => sum_indicator_tailSum_le_one hr L ℓ T rep hrect x
    _ = volume E := by simp

/-- **For each `ℓ`: `∑_{T ∈ 𝒯^{(ℓ)}} |I_T| ≲ 2^{-2ℓ} den^{-r'} |E|`** (L1955-L1966), written without
negative powers: if the tiles `I_T × ω_T`, `T ∈ s`, are pairwise disjoint and every `T ∈ s`
satisfies the truncated density bound (trunctreehaslargedensity) with this `ℓ`, then
`8^ℓ den^{r'} ∑_{s} |I_T| ≤ 2^{ℓ+3} 2^{8+r'} |E|`. -/
theorem covering_fiber_bound {r : ℝ} (hr : 1 < r) (hC₂ : 1 < C₂) (L : Linearization r)
    (E : Set ℝ) (ℓ : ℕ) (T : ℕ → MultitileTree ρ) {den : ℝ} (s : Finset ℕ)
    (hdisj : ∀ j ∈ s, ∀ j' ∈ s, j ≠ j' → Disjoint ((T j).tile C₂) ((T j').tile C₂))
    (htrunc : ∀ j ∈ s, ENNReal.ofReal (8 ^ ℓ * den ^ Real.conjExponent r) *
        ENNReal.ofReal (T j).I.length ≤ ENNReal.ofReal (2 ^ (8 + Real.conjExponent r)) *
          ∫⁻ x in E ∩ (T j).I.dilate ((2 : ℝ) ^ ℓ), L.tailSum ((T j).ωT C₂) x) :
    ENNReal.ofReal (8 ^ ℓ * den ^ Real.conjExponent r) * ∑ j ∈ s, ENNReal.ofReal (T j).I.length ≤
      ENNReal.ofReal (2 ^ (ℓ + 3)) *
        (ENNReal.ofReal (2 ^ (8 + Real.conjExponent r)) * volume E) := by
  obtain ⟨rep, hsub, hsum, hrect⟩ := exists_covering_rep hC₂ ℓ T s hdisj
  calc ENNReal.ofReal (8 ^ ℓ * den ^ Real.conjExponent r) *
        ∑ j ∈ s, ENNReal.ofReal (T j).I.length
      ≤ ENNReal.ofReal (8 ^ ℓ * den ^ Real.conjExponent r) *
        (ENNReal.ofReal (2 ^ (ℓ + 3)) * ∑ j ∈ rep, ENNReal.ofReal (T j).I.length) :=
        mul_le_mul' le_rfl hsum
    _ = ENNReal.ofReal (2 ^ (ℓ + 3)) * (ENNReal.ofReal (8 ^ ℓ * den ^ Real.conjExponent r) *
        ∑ j ∈ rep, ENNReal.ofReal (T j).I.length) := by ring
    _ ≤ ENNReal.ofReal (2 ^ (ℓ + 3)) * (ENNReal.ofReal (2 ^ (8 + Real.conjExponent r)) *
        volume E) := by
        refine mul_le_mul' le_rfl ?_
        calc ENNReal.ofReal (8 ^ ℓ * den ^ Real.conjExponent r) *
              ∑ j ∈ rep, ENNReal.ofReal (T j).I.length
            = ∑ j ∈ rep, ENNReal.ofReal (8 ^ ℓ * den ^ Real.conjExponent r) *
                ENNReal.ofReal (T j).I.length := Finset.mul_sum _ _ _
          _ ≤ ∑ j ∈ rep, ENNReal.ofReal (2 ^ (8 + Real.conjExponent r)) *
                ∫⁻ x in E ∩ (T j).I.dilate ((2 : ℝ) ^ ℓ), L.tailSum ((T j).ωT C₂) x :=
              Finset.sum_le_sum fun j hj => htrunc j (hsub hj)
          _ = ENNReal.ofReal (2 ^ (8 + Real.conjExponent r)) *
                ∑ j ∈ rep, ∫⁻ x in E ∩ (T j).I.dilate ((2 : ℝ) ^ ℓ),
                  L.tailSum ((T j).ωT C₂) x := (Finset.mul_sum _ _ _).symm
          _ ≤ ENNReal.ofReal (2 ^ (8 + Real.conjExponent r)) * volume E :=
              mul_le_mul' le_rfl (sum_lintegral_le_volume hr L E ℓ T rep hrect)

end Covering

end PrimeCarleson.Proof.Oplus

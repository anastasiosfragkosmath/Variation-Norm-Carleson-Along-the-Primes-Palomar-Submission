module

public import PrimeCarleson.Proof.Oplus.Decomposition.WavePacketRep
public import PrimeCarleson.Proof.Oplus.Decomposition.ModelOperator
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Sorting into the ten classes and the multitile form ([O+] L1040-L1090)

[O+] L1059-L1067: "It now follows that `𝒮''[f] =
∑_{ρ ∈ R} 𝒮^ρ[f]` where `𝒮^ρ[f](x) = ∑_{k=1}^K (∑_{(I×J) ∈ 𝔓, J ∈ 𝒥_{ξ_{k-1}(x),ξ_k(x),ρ}}
⟨f, φ_{I×J}⟩ φ_{I×J}) a_k(x)`"; L1085-L1090: "`𝒮^ρ[f](x) = ∑_{P ∈ 𝒫_ρ} ⟨f, φ_P⟩ φ_P(x) a_P(x)`
where, for each `ρ`-multitile `P`, `φ_P(x) = √|I| 𝓕⁻¹[√φ_{ω_u,i(ρ)}](x - c(I))` and `𝒫_ρ` denotes
the set of all `ρ`-multitiles for which `I × ω_u` belongs to `𝔓`". Source: [O+], L1059–L1067; [O+],
L1085–L1090 (the latter with an amendment: the identification with the class operator holds for
`ρ ∈ R` with the profile `√ν_{i(ρ)}`; `Defs/Multitile.lean` allows every index and every profile).

* `classTerm ρ f ξ ξ' P x`, `classOp ρ L 𝔓 f x = 𝒮^ρ[f](x)` for a finite family `𝔓` of tiles;
* `tileTerm_eq_sum_classTerm` (tile by tile) and `waveOp_eq_sum_classOp`: **`𝒮''[f] =
  ∑_{ρ ∈ R} 𝒮^ρ[f]`** when `Ξ` contains no number `n 2^m` (the standing assumption of
  L897-L899; it is used through `IsWhitney.exists_inClass`, `nbrIdx_of_inClass` of
  `Whitney.lean`);
* `inClass_iff_mem`, `Multitile.ofTiles`, `Multitile.sum_ofTiles` and `classOp_eq_modelOp`:
  **`𝒮^ρ[f](x) = ∑_{P ∈ 𝒫_ρ} ⟨f, φ_P⟩ φ_P(x) a_P(x)`** (`modelOp ρ.choice`, `ρ.choice` the
  profile `ν_{i(ρ)}`), no assumption on `Ξ`;
* the forms used downstream: `waveOp_eq_sum_modelOp`, `measurable_waveOp` and
  `eLpNorm_op_le_liminf_waveOp` (Fatou: `‖𝒮'[f]‖_{L^p} ≤ liminf_n ‖𝒮''_{𝔓_n}[f]‖_{L^p}`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap ContDiff ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- The ten elements of `R` as a finite set. -/
def RIdx.finset : Finset RIdx :=
  {.r121L, .r122L, .r131L, .r132L, .r211L, .r211R, .r221R, .r341L, .r331R, .r342L}

instance : Fintype RIdx := ⟨RIdx.finset, fun ρ => by cases ρ <;> decide⟩

/-- The profile choice of `ρ ∈ R`: `ν_{i(ρ)}` (plain), as used for the packets of the multitiles of
class `ρ` ([O+] L1088-L1089). -/
def RIdx.choice (ρ : RIdx) : ProfileChoice :=
  ⟨ρ.i, (RIdx.i_mem ρ).1, (RIdx.i_mem ρ).2, Orientation.plain⟩

/-- The contribution `1_{J ∈ 𝒥_{ξ,ξ',ρ}} ⟨f, φ_P⟩ φ_P(x)` of the tile `P = I × J`, with the packet
of index `i(ρ)`. -/
def classTerm (ρ : RIdx) (f : ℝ → ℂ) (ξ ξ' : ℝ) (P : Tile) (x : ℝ) : ℂ :=
  {P : Tile | InClass ρ.toIdx ξ ξ' P.J}.indicator
    (fun P => pairing f (P.wavePacket ρ.i) * P.wavePacket ρ.i x) P

/-- **The class operator `𝒮^ρ` of a finite family of tiles** ([O+] L1059-L1067):
`𝒮^ρ[f](x) = ∑_k (∑_{(I × J) ∈ 𝔓, J ∈ 𝒥_{ξ_{k-1}(x),ξ_k(x),ρ}} ⟨f, φ_{I×J}⟩ φ_{I×J}(x)) a_k(x)`,
with the packets of the index `i(ρ)`. -/
def classOp (ρ : RIdx) {r : ℝ} (L : Linearization r) (𝔓 : Finset Tile) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ k : Fin L.K, (∑ P ∈ 𝔓, classTerm ρ f (L.ξ k.castSucc x) (L.ξ k.succ x) P x) * L.a k x

/-- **Tile by tile, the sorting**: for `ξ` avoiding the dyadic end points,
`1_{J ∈ 𝒥_{ξ,ξ'}} ⟨f, φ_P^{(i(J))}⟩ φ_P^{(i(J))}(x) = ∑_{ρ ∈ R} 1_{J ∈ 𝒥_{ξ,ξ',ρ}} ⟨f, φ_P^{(i(ρ))}⟩
φ_P^{(i(ρ))}(x)`. -/
theorem tileTerm_eq_sum_classTerm {ξ ξ' : ℝ} (hξ : ∀ n m : ℤ, ξ ≠ n * 2 ^ m) (f : ℝ → ℂ)
    (P : Tile) (x : ℝ) : tileTerm f ξ ξ' P x = ∑ ρ : RIdx, classTerm ρ f ξ ξ' P x := by
  by_cases hw : P.J.IsWhitney ξ ξ'
  · obtain ⟨ρ₀, hρ₀, huniq⟩ := hw.existsUnique_inClass hξ
    rw [Finset.sum_eq_single ρ₀]
    · unfold tileTerm classTerm
      rw [Set.indicator_of_mem (show P ∈ {P : Tile | P.J.IsWhitney ξ ξ'} from hw),
        Set.indicator_of_mem (show P ∈ {P : Tile | InClass ρ₀.toIdx ξ ξ' P.J} from hρ₀),
        Dyadic.nbrIdx_of_inClass hξ ρ₀ hρ₀]
    · intro ρ _ hne
      unfold classTerm
      refine Set.indicator_of_notMem (show P ∉ {P : Tile | InClass ρ.toIdx ξ ξ' P.J} from ?_) _
      intro h
      exact hne (huniq ρ h)
    · intro h; exact absurd (Finset.mem_univ ρ₀) h
  · unfold tileTerm
    rw [Set.indicator_of_notMem (show P ∉ {P : Tile | P.J.IsWhitney ξ ξ'} from hw)]
    symm
    refine Finset.sum_eq_zero fun ρ _ => ?_
    unfold classTerm
    exact Set.indicator_of_notMem (show P ∉ {P : Tile | InClass ρ.toIdx ξ ξ' P.J} from fun h =>
      hw (Dyadic.isWhitney_of_inClass hξ ρ h)) _

/-- **Sorting into classes** ([O+] L1059-L1067): if `Ξ` contains no
dyadic end points, then `𝒮''[f] = ∑_{ρ ∈ R} 𝒮^ρ[f]` for every finite family of tiles. -/
theorem waveOp_eq_sum_classOp {r : ℝ} (L : Linearization r)
    (hΞ : AvoidsDyadicEndpoints (L.Ξ : Set ℝ)) (𝔓 : Finset Tile) (f : ℝ → ℂ) (x : ℝ) :
    waveOp L 𝔓 f x = ∑ ρ : RIdx, classOp ρ L 𝔓 f x := by
  unfold waveOp classOp
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun P _ => ?_
  exact tileTerm_eq_sum_classTerm (hΞ _ (Finset.mem_coe.2 (L.ξ_mem k.castSucc x))) f P x

/-- Every point of `ω_h` is at least the right end point of `ω_u` (`b ≤ ξ'`). -/
theorem Idx.right_le_of_mem_ωh (ρ : Idx) (u : Dyadic) {b : ℝ} (hb : b ∈ ρ.ωh u) : u.right ≤ b := by
  have hL := u.length_pos
  have hn : (0 : ℝ) ≤ ρ.n := Nat.cast_nonneg _
  have hr := u.right_eq
  unfold Idx.ωh at hb
  cases h : ρ.typ <;> rw [h] at hb
  · simp only [Dyadic.toSet, Dyadic.left_shift, mem_Ico] at hb
    push_cast at hb
    nlinarith [hb.1]
  · simp only [mem_Ici] at hb
    nlinarith
  · simp only [Dyadic.toSet, Dyadic.left_shift, mem_Ico] at hb
    push_cast at hb
    nlinarith [hb.1]

/-- `J ∈ 𝒥_{ξ,ξ',ρ}` iff `J` is a `side`-child with `ξ ∈ ω_l(J)` and `ξ' ∈ ω_h(J)` (the interval
`J ⊂ (ξ, ξ')` is then automatic): the reading of `𝒥_{ξ,ξ',ρ}` as `ρ`-multitiles
([O+] L1074-L1082). -/
theorem inClass_iff_mem (ρ : Idx) (ξ ξ' : ℝ) (J : Dyadic) :
    InClass ρ ξ ξ' J ↔ J.side = ρ.side ∧ ξ ∈ ρ.ωl J ∧ ξ' ∈ ρ.ωh J := by
  unfold InClass
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h1, h2, h3⟩
    rw [Dyadic.toSet_subset_Ioo_iff]
    exact ⟨ρ.lt_left_of_mem_ωl J h2, ρ.right_le_of_mem_ωh J h3⟩

/-- The `ρ`-multitiles over a finite family of tiles `𝔓` (`𝒫_ρ` of [O+] L1090), as a finite set. -/
def Multitile.ofTiles (ρ : Idx) (𝔓 : Finset Tile) : Finset (Multitile ρ) :=
  (Multitile.finite_family (ρ := ρ) (𝔓.finite_toSet)).toFinset

theorem Multitile.mem_ofTiles {ρ : Idx} {𝔓 : Finset Tile} {Q : Multitile ρ} :
    Q ∈ Multitile.ofTiles ρ 𝔓 ↔ Q.tile ∈ 𝔓 := by
  unfold Multitile.ofTiles
  rw [Set.Finite.mem_toFinset]
  rfl

/-- The sum over the `ρ`-multitiles over `𝔓` is the sum over the tiles of `𝔓` whose frequency
interval is a `side`-child. -/
theorem Multitile.sum_ofTiles {ρ : Idx} (𝔓 : Finset Tile) {M : Type*} [AddCommMonoid M]
    (F : Tile → M) :
    ∑ Q ∈ Multitile.ofTiles ρ 𝔓, F Q.tile = ∑ P ∈ 𝔓.filter (fun P => P.J.side = ρ.side), F P := by
  classical
  refine Finset.sum_nbij (fun Q => Q.tile) (fun Q hQ => ?_) (fun Q _ Q' _ h =>
    Multitile.tile_injective h) (fun P hP => ?_) (fun _ _ => rfl)
  · exact Finset.mem_filter.2 ⟨Multitile.mem_ofTiles.1 hQ, Q.side_eq⟩
  · obtain ⟨hP1, hP2⟩ := Finset.mem_filter.1 hP
    exact ⟨⟨P.I, P.J, P.area, hP2⟩, Multitile.mem_ofTiles.2 hP1, rfl⟩

/-- **The multitile form** ([O+] L1085-L1090): for `ρ ∈ R`,
`𝒮^ρ[f](x) = ∑_{P ∈ 𝒫_ρ} ⟨f, φ_P⟩ φ_P(x) a_P(x)`, where `𝒫_ρ` is the set of `ρ`-multitiles with
`I × ω_u ∈ 𝔓` and the packets `φ_P` are those of the profile `√ν_{i(ρ)}`. -/
theorem classOp_eq_modelOp (ρ : RIdx) {r : ℝ} (L : Linearization r) (𝔓 : Finset Tile)
    (f : ℝ → ℂ) (x : ℝ) :
    classOp ρ L 𝔓 f x = modelOp ρ.choice L (Multitile.ofTiles ρ.toIdx 𝔓) f x := by
  classical
  have key := Multitile.sum_ofTiles (ρ := ρ.toIdx) 𝔓 (fun P : Tile =>
    (pairing f (P.wavePacket ρ.i) * P.wavePacket ρ.i x) *
      ∑ k : Fin L.K, if L.ξ k.castSucc x ∈ ρ.toIdx.ωl P.J ∧ L.ξ k.succ x ∈ ρ.toIdx.ωh P.J
        then L.a k x else 0)
  have hmodel : modelOp ρ.choice L (Multitile.ofTiles ρ.toIdx 𝔓) f x =
      ∑ P ∈ 𝔓.filter (fun P => P.J.side = ρ.toIdx.side),
        (pairing f (P.wavePacket ρ.i) * P.wavePacket ρ.i x) *
          ∑ k : Fin L.K, if L.ξ k.castSucc x ∈ ρ.toIdx.ωl P.J ∧ L.ξ k.succ x ∈ ρ.toIdx.ωh P.J
            then L.a k x else 0 := by
    unfold modelOp
    exact key
  rw [hmodel]
  unfold classOp
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun P _ => ?_
  by_cases hs : P.J.side = ρ.toIdx.side
  · simp only [hs, ↓reduceIte]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold classTerm
    by_cases hc : L.ξ k.castSucc x ∈ ρ.toIdx.ωl P.J ∧ L.ξ k.succ x ∈ ρ.toIdx.ωh P.J
    · rw [Set.indicator_of_mem (show P ∈ {P : Tile | InClass ρ.toIdx (L.ξ k.castSucc x)
        (L.ξ k.succ x) P.J} from (inClass_iff_mem _ _ _ _).2 ⟨hs, hc⟩)]
      simp only [hc.1, hc.2, and_self, ↓reduceIte]
    · rw [Set.indicator_of_notMem (show P ∉ {P : Tile | InClass ρ.toIdx (L.ξ k.castSucc x)
        (L.ξ k.succ x) P.J} from fun h => hc (((inClass_iff_mem _ _ _ _).1 h).2))]
      simp only [hc]
      simp
  · simp only [hs, ↓reduceIte]
    refine Finset.sum_eq_zero fun k _ => ?_
    unfold classTerm
    rw [Set.indicator_of_notMem (show P ∉ {P : Tile | InClass ρ.toIdx (L.ξ k.castSucc x)
      (L.ξ k.succ x) P.J} from fun h => hs (((inClass_iff_mem _ _ _ _).1 h).1))]
    simp

/-- **`𝒮'' = ∑_{ρ ∈ R} 𝒮^ρ` with `𝒮^ρ` in multitile form**: for `Ξ` without dyadic end points,
`𝒮''_𝔓[f](x) = ∑_{ρ ∈ R} ∑_{P ∈ 𝒫_ρ} ⟨f, φ_P⟩ φ_P(x) a_P(x)`. -/
theorem waveOp_eq_sum_modelOp {r : ℝ} (L : Linearization r)
    (hΞ : AvoidsDyadicEndpoints (L.Ξ : Set ℝ)) (𝔓 : Finset Tile) (f : ℝ → ℂ) (x : ℝ) :
    waveOp L 𝔓 f x = ∑ ρ : RIdx, modelOp ρ.choice L (Multitile.ofTiles ρ.toIdx 𝔓) f x := by
  rw [waveOp_eq_sum_classOp L hΞ]
  exact Finset.sum_congr rfl fun ρ _ => classOp_eq_modelOp ρ L 𝔓 f x

/-- `𝒮''_𝔓[f]` is measurable (for `Ξ` without dyadic end points). -/
theorem measurable_waveOp {r : ℝ} (L : Linearization r)
    (hΞ : AvoidsDyadicEndpoints (L.Ξ : Set ℝ)) (𝔓 : Finset Tile) (f : ℝ → ℂ) :
    Measurable (waveOp L 𝔓 f) := by
  have : waveOp L 𝔓 f = fun x => ∑ ρ : RIdx,
      modelOp ρ.choice L (Multitile.ofTiles ρ.toIdx 𝔓) f x :=
    funext fun x => waveOp_eq_sum_modelOp L hΞ 𝔓 f x
  rw [this]
  exact Finset.measurable_sum _ fun ρ _ => measurable_modelOp ρ.choice L _ f

/-- **Fatou for the finite-family operators** ([O+] L1026-L1038): for an exhausting sequence `𝔓_n`
of finite families, `‖𝒮'[f]‖_{L^p} ≤ liminf_n ‖𝒮''_{𝔓_n}[f]‖_{L^p}`. -/
theorem eLpNorm_op_le_liminf_waveOp {r : ℝ} (L : Linearization r)
    (hΞ : AvoidsDyadicEndpoints (L.Ξ : Set ℝ)) (f : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport (𝓕 (⇑f))) (hs : ∀ ζ ∈ L.Ξ, ζ ∉ tsupport (𝓕 (⇑f)))
    (𝔓 : ℕ → Finset Tile) (hmono : Monotone 𝔓) (hcov : ∀ P : Tile, ∃ n, P ∈ 𝔓 n) (p : ℝ≥0∞) :
    eLpNorm (L.op f) p volume ≤ atTop.liminf fun n => eLpNorm (waveOp L (𝔓 n) f) p volume := by
  have hmeas := fun n => (measurable_waveOp L hΞ (𝔓 n) f).aestronglyMeasurable (μ := volume)
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun n => waveOp L (𝔓 n) f x) atTop (𝓝 (L.op f x)) :=
    Filter.Eventually.of_forall fun x => tendsto_waveOp_nat L f hc hs 𝔓 hmono hcov x
  exact Lp.eLpNorm_lim_le_liminf_eLpNorm hmeas _
    (aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim) hlim

end PrimeCarleson.Proof.Oplus

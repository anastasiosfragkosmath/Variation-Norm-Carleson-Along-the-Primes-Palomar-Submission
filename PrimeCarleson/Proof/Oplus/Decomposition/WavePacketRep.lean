module

public import PrimeCarleson.Proof.Oplus.Decomposition.PartitionOfUnity
public import PrimeCarleson.Proof.Oplus.Decomposition.Expansion

/-!
# The wave-packet representation of `𝒮'` and the finite-family operator `𝒮''` ([O+] L1019-L1038)

[O+] L1019-L1038: "This in turn yields the representation of
`𝒮'[f]` in terms of wave packets: `𝒮'[f](x) = ∑_{k=1}^K (∑_{J ∈ 𝒥_{ξ_{k-1}(x),ξ_k(x)}}
∑_{|I| = 1/(2|J|)} ⟨f, φ_{I×J}⟩ φ_{I×J}) a_k(x)`. [...] Therefore it suffices, for any finite
family `𝔓` of tiles, to consider the operator `𝒮''[f](x) = ∑_{k=1}^K (∑_{(I,J) ∈ 𝔓,
J ∈ 𝒥_{ξ_{k-1}(x),ξ_k(x)}} ⟨f, φ_{I×J}⟩ φ_{I×J}(x))
a_k(x)`". Source: [O+], L1021–L1024; [O+], L1026–L1038 (in the form used here:
`𝒮''_{𝔓_n}[f](x) → 𝒮'[f](x)` for every `x`, along any exhausting sequence of finite families,
followed by Fatou).

* `Tile.ofDual J m`, `Tile.equivProd : Tile ≃ Dyadic × ℤ`: a tile is a frequency interval `J` and
  a position `m` of the time interval of length `1/(2|J|)`;
* `tileTerm f ξ ξ' P x`: the contribution `1_{J ∈ 𝒥_{ξ,ξ'}} ⟨f, φ_P⟩ φ_P(x)` of the tile
  `P = I × J` to the pair `(ξ, ξ')`, with the packet of index `i(J)` (`nbrIdx ξ ξ' J`);
* `hasSum_tileTerm_dual` (for a Whitney `J`: the sum over `I` is the inverse Fourier transform of
  `φ_J f̂`), `hasSum_tileTerm_pair` (for one pair `ξ < ξ'`: the sum over all tiles is
  `∫_{(ξ,ξ')} f̂ e(ηx) dη`, from the partition of unity, the finiteness of the relevant `J` and
  the expansion);
* `waveTerm`, `waveOp L 𝔓 f x = 𝒮''[f](x)`, `hasSum_waveTerm` (`𝒮'[f](x) = ∑_P waveTerm P x`, the
  wave-packet representation) and `tendsto_waveOp`, `tendsto_waveOp_nat` (convergence of `𝒮''`
  along the finite families, pointwise in `x`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

/-- The tile with frequency interval `J` and time interval at position `m`. -/
def Tile.ofDual (J : Dyadic) (m : ℤ) : Tile := ⟨J.dual m, J, Dyadic.dual_k J m⟩

/-- Tiles are the pairs `(J, m)`. -/
def Tile.equivProd : Tile ≃ Dyadic × ℤ where
  toFun P := (P.J, P.I.m)
  invFun p := Tile.ofDual p.1 p.2
  left_inv P := by
    have hk : P.I.k = -1 - P.J.k := by have := P.area; omega
    refine Tile.ext ?_ rfl
    exact Dyadic.ext hk.symm rfl
  right_inv p := rfl

@[simp] theorem Tile.equivProd_ofDual (J : Dyadic) (m : ℤ) :
    Tile.equivProd (Tile.ofDual J m) = (J, m) := rfl

/-- The contribution `1_{J ∈ 𝒥_{ξ,ξ'}} ⟨f, φ_P⟩ φ_P(x)` of the tile `P = I × J` to the sum at `x`,
with the packet of index `i = i(J)` of the Whitney neighbour. -/
def tileTerm (f : ℝ → ℂ) (ξ ξ' : ℝ) (P : Tile) (x : ℝ) : ℂ :=
  {P : Tile | P.J.IsWhitney ξ ξ'}.indicator (fun P =>
    pairing f (P.wavePacket (Dyadic.nbrIdx ξ ξ' P.J)) * P.wavePacket (Dyadic.nbrIdx ξ ξ' P.J) x) P

theorem tileTerm_ofDual_of_isWhitney {f : ℝ → ℂ} {ξ ξ' : ℝ} {J : Dyadic}
    (hJ : J.IsWhitney ξ ξ') (m : ℤ) (x : ℝ) :
    tileTerm f ξ ξ' (Tile.ofDual J m) x =
      pairing f (wavePacketOf (nuFamily (Dyadic.nbrIdx ξ ξ' J)) (J.dual m) J) *
        wavePacketOf (nuFamily (Dyadic.nbrIdx ξ ξ' J)) (J.dual m) J x := by
  unfold tileTerm
  rw [Set.indicator_of_mem (show Tile.ofDual J m ∈ {P : Tile | P.J.IsWhitney ξ ξ'} from hJ)]
  rfl

theorem tileTerm_ofDual_of_not_isWhitney {f : ℝ → ℂ} {ξ ξ' : ℝ} {J : Dyadic}
    (hJ : ¬ J.IsWhitney ξ ξ') (m : ℤ) (x : ℝ) : tileTerm f ξ ξ' (Tile.ofDual J m) x = 0 := by
  unfold tileTerm
  exact Set.indicator_of_notMem (show Tile.ofDual J m ∉ {P : Tile | P.J.IsWhitney ξ ξ'} from hJ) _

/-- The profile `ν_{i(J)}` of a Whitney interval is a profile. -/
theorem isProfile_nbrIdx {ξ ξ' : ℝ} {J : Dyadic} (hJ : J.IsWhitney ξ ξ') :
    IsProfile (nuFamily (Dyadic.nbrIdx ξ ξ' J)) :=
  isProfile_nuFamily (Dyadic.nbrIdx_mem hJ).1 (Dyadic.nbrIdx_mem hJ).2

/-- For a Whitney interval `J`, the wave packets `φ_{I×J}` (`I` of length `1/(2|J|)`) sum to the
inverse Fourier transform of `φ_J f̂` ([O+] L1019-L1024). -/
theorem hasSum_tileTerm_dual (f : 𝓢(ℝ, ℂ)) {ξ ξ' : ℝ} {J : Dyadic} (hJ : J.IsWhitney ξ ξ')
    (x : ℝ) :
    HasSum (fun m : ℤ => tileTerm f ξ ξ' (Tile.ofDual J m) x)
      (∫ η, ((phiW ξ ξ' J η : ℝ) : ℂ) * 𝓕 (⇑f) η * e (η * x)) := by
  have h := hasSum_wavePacket_series (isProfile_nbrIdx hJ) f J x
  simp_rw [tileTerm_ofDual_of_isWhitney hJ]
  convert h using 3 with η
  rw [phiW, phiDyadic_eq_nuFamily]

theorem continuous_phiW (ξ ξ' : ℝ) (J : Dyadic) : Continuous (phiW ξ ξ' J) := by
  have : phiW ξ ξ' J = fun η => nuFamily (Dyadic.nbrIdx ξ ξ' J) ((η - J.center) / J.length) :=
    funext fun η => phiDyadic_eq_nuFamily J _ η
  rw [this]
  exact (contDiff_nuFamily _).continuous.comp ((continuous_id.sub continuous_const).div_const _)

theorem abs_phiW_le_one (ξ ξ' : ℝ) (J : Dyadic) (η : ℝ) : |phiW ξ ξ' J η| ≤ 1 := by
  unfold phiW phiDyadic phiJi
  have h1 := nu_nonneg ((η - J.left) / (2 ^ (Dyadic.nbrIdx ξ ξ' J) * (J.right - J.left)))
  have h2 := nu_le_one ((η - J.left) / (2 ^ (Dyadic.nbrIdx ξ ξ' J) * (J.right - J.left)))
  have h3 := nu_nonneg ((η - J.right) / (J.right - J.left))
  have h4 := nu_le_one ((η - J.right) / (J.right - J.left))
  rw [abs_le]
  constructor <;> linarith

theorem integrable_phiW_mul (f : 𝓢(ℝ, ℂ)) (ξ ξ' : ℝ) (J : Dyadic) (x : ℝ) :
    Integrable (fun η => ((phiW ξ ξ' J η : ℝ) : ℂ) * 𝓕 (⇑f) η * e (η * x)) := by
  have h1 := integrable_fourier_mul_e f x
  have h2 := h1.bdd_mul (f := fun η => ((phiW ξ ξ' J η : ℝ) : ℂ)) (c := 1)
    (Complex.continuous_ofReal.comp (continuous_phiW ξ ξ' J)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun η => by simpa using abs_phiW_le_one ξ ξ' J η)
  refine h2.congr (Filter.Eventually.of_forall fun η => ?_)
  simp only; ring

/-- The coefficients of an irrelevant Whitney interval vanish. -/
theorem pairing_dual_eq_zero (f : 𝓢(ℝ, ℂ)) {ξ ξ' : ℝ} {J : Dyadic} (hJ : J.IsWhitney ξ ξ')
    (hrel : ∀ η, ((phiW ξ ξ' J η : ℝ) : ℂ) * 𝓕 (⇑f) η = 0) (m : ℤ) :
    pairing f (wavePacketOf (nuFamily (Dyadic.nbrIdx ξ ξ' J)) (J.dual m) J) = 0 := by
  rw [pairing_wavePacketOf_eq (isProfile_nbrIdx hJ)]
  have h0 : ∀ η, multJ (nuFamily (Dyadic.nbrIdx ξ ξ' J)) J f η = 0 := by
    intro η
    have h := hrel η
    unfold multJ
    rcases mul_eq_zero.1 h with h' | h'
    · have h1 : phiW ξ ξ' J η = 0 := by exact_mod_cast h'
      have h2 : nuFamily (Dyadic.nbrIdx ξ ξ' J) ((η - J.center) / J.length) = 0 := by
        rw [← phiDyadic_eq_nuFamily]; exact h1
      simp [freqProfile, h2]
    · simp [h']
  simp [h0]

/-- **The wave-packet representation for one pair `ξ < ξ'`** ([O+] L930-L1024): if `f̂` has compact
support missing `ξ, ξ'`, then for every `x`,
`∫_{(ξ,ξ')} f̂(η) e(ηx) dη = ∑_{J ∈ 𝒥_{ξ,ξ'}} ∑_{|I| = 1/(2|J|)} ⟨f, φ_{I×J}⟩ φ_{I×J}(x)`, the sum
over all tiles `P = I × J` (unconditional convergence). -/
theorem hasSum_tileTerm_pair (f : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (𝓕 (⇑f))) {ξ ξ' : ℝ}
    (hξ : ξ ∉ tsupport (𝓕 (⇑f))) (hξ' : ξ' ∉ tsupport (𝓕 (⇑f))) (x : ℝ) :
    HasSum (fun P : Tile => tileTerm f ξ ξ' P x) (∫ η in Ioo ξ ξ', 𝓕 (⇑f) η * e (η * x)) := by
  classical
  have hfin := Dyadic.finite_relevant hc hξ hξ'
  set R := hfin.toFinset with hR
  have hRmem : ∀ J, J ∈ R ↔ J.IsWhitney ξ ξ' ∧ ∃ η, ((phiW ξ ξ' J η : ℝ) : ℂ) * 𝓕 (⇑f) η ≠ 0 :=
    fun J => hfin.mem_toFinset
  -- the partition of unity restricted to the relevant intervals
  have hpt : ∀ η, (Ioo ξ ξ').indicator (fun _ => (1 : ℂ)) η * 𝓕 (⇑f) η =
      ∑ J ∈ R, ((phiW ξ ξ' J η : ℝ) : ℂ) * 𝓕 (⇑f) η := by
    intro η
    have h1 := Dyadic.hasSum_phiW_mul (ξ := ξ) (ξ' := ξ') (𝓕 (⇑f)) η
    have h2 : HasSum ({J : Dyadic | J.IsWhitney ξ ξ'}.indicator
        (fun J => ((phiW ξ ξ' J η : ℝ) : ℂ) * 𝓕 (⇑f) η))
        (∑ J ∈ R, {J : Dyadic | J.IsWhitney ξ ξ'}.indicator
          (fun J => ((phiW ξ ξ' J η : ℝ) : ℂ) * 𝓕 (⇑f) η) J) :=
      hasSum_sum_of_ne_finset_zero (fun J hJ => by
        by_cases hw : J.IsWhitney ξ ξ'
        · rw [Set.indicator_of_mem (show J ∈ {J : Dyadic | J.IsWhitney ξ ξ'} from hw)]
          by_contra hne
          exact hJ ((hRmem J).2 ⟨hw, η, hne⟩)
        · exact Set.indicator_of_notMem (show J ∉ {J : Dyadic | J.IsWhitney ξ ξ'} from hw) _)
    rw [h1.unique h2]
    refine Finset.sum_congr rfl fun J hJ => ?_
    exact Set.indicator_of_mem (show J ∈ {J : Dyadic | J.IsWhitney ξ ξ'} from
      ((hRmem J).1 hJ).1) _
  -- the integral
  have hint : ∫ η in Ioo ξ ξ', 𝓕 (⇑f) η * e (η * x) =
      ∑ J ∈ R, ∫ η, ((phiW ξ ξ' J η : ℝ) : ℂ) * 𝓕 (⇑f) η * e (η * x) := by
    rw [← integral_indicator measurableSet_Ioo, ← integral_finsetSum R
      (fun J _ => integrable_phiW_mul f ξ ξ' J x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    simp only
    rw [← Finset.sum_mul, ← hpt η]
    by_cases hη : η ∈ Ioo ξ ξ' <;> simp [hη]
  rw [hint]
  -- the sum over tiles
  rw [← Equiv.hasSum_iff Tile.equivProd.symm]
  set G : Dyadic × ℤ → ℂ := fun p => tileTerm f ξ ξ' (Tile.ofDual p.1 p.2) x with hG
  have hGdec : G = fun p => ∑ J ∈ R, if p.1 = J then G p else 0 := by
    funext p
    by_cases hp : p.1 ∈ R
    · rw [Finset.sum_eq_single p.1]
      · simp
      · intro J _ hJ; simp [Ne.symm hJ]
      · intro h; exact absurd hp h
    · rw [Finset.sum_eq_zero (fun J hJ => by
        have : p.1 ≠ J := fun h => hp (h ▸ hJ)
        simp [this])]
      by_cases hw : p.1.IsWhitney ξ ξ'
      · have hrel : ∀ η, ((phiW ξ ξ' p.1 η : ℝ) : ℂ) * 𝓕 (⇑f) η = 0 := by
          intro η
          by_contra hne
          exact hp ((hRmem p.1).2 ⟨hw, η, hne⟩)
        simp only [hG]
        rw [tileTerm_ofDual_of_isWhitney hw, pairing_dual_eq_zero f hw hrel]
        simp
      · simp only [hG]
        exact tileTerm_ofDual_of_not_isWhitney hw _ _
  have hparts : ∀ J ∈ R, HasSum (fun p : Dyadic × ℤ => if p.1 = J then G p else 0)
      (∫ η, ((phiW ξ ξ' J η : ℝ) : ℂ) * 𝓕 (⇑f) η * e (η * x)) := by
    intro J hJR
    have hw := ((hRmem J).1 hJR).1
    have hinj : Function.Injective (fun m : ℤ => (J, m)) := fun a b h => (Prod.mk.inj h).2
    rw [← hinj.hasSum_iff (fun p hp => ?_)]
    · simpa [Function.comp_def, hG] using hasSum_tileTerm_dual f hw x
    · have : p.1 ≠ J := fun h => hp ⟨p.2, by rw [← h]⟩
      simp [this]
  have := hasSum_sum hparts
  rw [← hGdec] at this
  exact this

/-- The term of the tile `P` in the finite-family operator at `x`:
`∑_k 1_{J ∈ 𝒥_{ξ_{k-1}(x), ξ_k(x)}} ⟨f, φ_P⟩ φ_P(x) a_k(x)` (the packet of the index `i(J)`
determined by the pair `(ξ_{k-1}(x), ξ_k(x))`). -/
def waveTerm {r : ℝ} (L : Linearization r) (f : ℝ → ℂ) (P : Tile) (x : ℝ) : ℂ :=
  ∑ k : Fin L.K, tileTerm f (L.ξ k.castSucc x) (L.ξ k.succ x) P x * L.a k x

/-- **The operator `𝒮''` of a finite family `𝔓` of tiles** ([O+] L1031-L1038):
`𝒮''[f](x) = ∑_k (∑_{(I,J) ∈ 𝔓, J ∈ 𝒥_{ξ_{k-1}(x),ξ_k(x)}} ⟨f, φ_{I×J}⟩ φ_{I×J}(x)) a_k(x)`, with
`φ_{I×J} = φ_{I×J}^{(i(J))}` the packet of the index `i(J)` of the Whitney neighbour of `J` in
`𝒥_{ξ_{k-1}(x),ξ_k(x)}` ([O+] L964). -/
def waveOp {r : ℝ} (L : Linearization r) (𝔓 : Finset Tile) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ k : Fin L.K, (∑ P ∈ 𝔓, tileTerm f (L.ξ k.castSucc x) (L.ξ k.succ x) P x) * L.a k x

theorem waveOp_eq_sum {r : ℝ} (L : Linearization r) (𝔓 : Finset Tile) (f : ℝ → ℂ) (x : ℝ) :
    waveOp L 𝔓 f x = ∑ P ∈ 𝔓, waveTerm L f P x := by
  unfold waveOp waveTerm
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

/-- **The wave-packet representation** ([O+] L1021-L1024): for Schwartz `f`
with `f̂` compactly supported in `ℝ ∖ Ξ`, `𝒮'[f](x) = ∑_k (∑_{J ∈ 𝒥_{ξ_{k-1}(x),ξ_k(x)}}
∑_{|I| = 1/(2|J|)} ⟨f, φ_{I×J}⟩ φ_{I×J}(x)) a_k(x)`; the sum over all tiles converges
unconditionally for every `x`. -/
theorem hasSum_waveTerm {r : ℝ} (L : Linearization r) (f : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport (𝓕 (⇑f))) (hΞ : ∀ ζ ∈ L.Ξ, ζ ∉ tsupport (𝓕 (⇑f))) (x : ℝ) :
    HasSum (fun P : Tile => waveTerm L f P x) (L.op f x) := by
  have h := hasSum_sum (s := Finset.univ) (fun (k : Fin L.K) _ =>
    (hasSum_tileTerm_pair f hc (hΞ _ (L.ξ_mem k.castSucc x)) (hΞ _ (L.ξ_mem k.succ x)) x).mul_right
      (L.a k x))
  have h2 : L.op f x = ∑ k : Fin L.K, (∫ η in Ioo (L.ξ k.castSucc x) (L.ξ k.succ x),
      𝓕 (⇑f) η * e (η * x)) * L.a k x := by
    unfold Linearization.op
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [partialFourierIntegral_sub_eq_integral_Ioo f (L.ξ_castSucc_lt k x).le x]
  rw [h2]
  exact h

/-- **`𝒮''_𝔓[f](x) → 𝒮'[f](x)` along the finite families** ([O+] L1031-L1038): the limit
along the net of all finite families of tiles. -/
theorem tendsto_waveOp {r : ℝ} (L : Linearization r) (f : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport (𝓕 (⇑f))) (hΞ : ∀ ζ ∈ L.Ξ, ζ ∉ tsupport (𝓕 (⇑f))) (x : ℝ) :
    Tendsto (fun 𝔓 : Finset Tile => waveOp L 𝔓 f x) atTop (𝓝 (L.op f x)) := by
  have h := hasSum_waveTerm L f hc hΞ x
  simp_rw [waveOp_eq_sum]
  exact h

/-- The same along an exhausting sequence `𝔓_1 ⊆ 𝔓_2 ⊆ …` of finite families of tiles. -/
theorem tendsto_waveOp_nat {r : ℝ} (L : Linearization r) (f : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport (𝓕 (⇑f))) (hΞ : ∀ ζ ∈ L.Ξ, ζ ∉ tsupport (𝓕 (⇑f)))
    (𝔓 : ℕ → Finset Tile) (hmono : Monotone 𝔓) (hcov : ∀ P : Tile, ∃ n, P ∈ 𝔓 n) (x : ℝ) :
    Tendsto (fun n => waveOp L (𝔓 n) f x) atTop (𝓝 (L.op f x)) :=
  (tendsto_waveOp L f hc hΞ x).comp (tendsto_atTop_finset_of_monotone hmono hcov)

/-- `‖a_k(x)‖ ≤ 1` -/
theorem Linearization.norm_a_le_one {r : ℝ} (hr : 1 < r) (L : Linearization r) (k : Fin L.K)
    (x : ℝ) : ‖L.a k x‖ ≤ 1 := by
  have h := L.norm_rpow_le_one k x
  have hp : 0 < Real.conjExponent r := by
    unfold Real.conjExponent; exact div_pos (by linarith) (by linarith)
  by_contra hlt
  rw [not_le] at hlt
  exact absurd h (not_le.2 (Real.one_lt_rpow hlt hp))

end PrimeCarleson.Proof.Oplus

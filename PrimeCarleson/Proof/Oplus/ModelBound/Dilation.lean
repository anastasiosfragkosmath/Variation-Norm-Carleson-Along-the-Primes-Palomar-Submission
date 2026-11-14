module

public import PrimeCarleson.Proof.Oplus.Conclusion.Main

/-!
# Rescaling: `halfgbound` for every measurable `E` ([O+] L1155-L1158)

Source: [O+] `halfgbound`, L1155–L1158: "after possibly rescaling, we may assume that
`1 ≤ |E| ≤ 2`".

The dilation `x ↦ 2^j x` acts on all the objects of the model operator:

* `Dyadic.dil`, `Multitile.dil`: `(I, ω_u) ↦ (2^j I, 2^{-j} ω_u)` (the area `|I||ω_u| = 1/2`,
  the side of `ω_u` and the set of `ρ`-multitiles are preserved), `Multitile.dil_injective`;
* `Idx.mem_ωl_dil`, `Idx.mem_ωh_dil`: `ω_l(2^{-j} u) = 2^{-j} ω_l(u)` for every index;
* `Linearization.dil`: `ξ'_k(y) = 2^{-j} ξ_k(2^{-j} y)`, `a'_k(y) = a_k(2^{-j} y)`, `Ξ' = 2^{-j} Ξ`,
  with `Multitile.aP_dil`;
* `wavePacketOf_dil`, `Multitile.wavePacket_dil`: `φ_{P^j}(2^j y) = 2^{-j/2} φ_P(y)`;
  `Multitile.coeff_dil`: `⟨f(2^{-j} ·), φ_{P^j}⟩ = 2^{j/2} ⟨f, φ_P⟩`;
* `Multitile.modelOp_dil`: `𝒮^ρ_{P^j}[f(2^{-j} ·)](2^j x) = 𝒮^ρ_P[f](x)`;
* `Separated.dil`: the separation assumptions (separationofscales), (separationprop2) are
  preserved.

`halfgbound_separated` is `mainargumentsection` (`1 ≤ |E| ≤ 2`) for every measurable `E` with
`0 < |E| < ∞`, with the same constant: `j` is chosen with `1 ≤ 2^j |E| ≤ 2`, `F` and `E` are
replaced by `2^j F` and `2^j E` (`|F|/|E|` is invariant), the family by its dilate. The trivial
cases `|E| = 0` and `|E| = ∞` are not covered (and are not needed: the level set argument uses
subsets of finite positive measure).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

namespace Dyadic

variable (I : Dyadic) (j : ℤ)

/-- The dilation `x ↦ 2^j x` of a dyadic interval:
`[2^k m, 2^k (m+1)) ↦ [2^{k+j} m, 2^{k+j}(m+1))`. -/
def dil : Dyadic := ⟨I.k + j, I.m⟩

@[simp] theorem dil_k : (I.dil j).k = I.k + j := rfl
@[simp] theorem dil_m : (I.dil j).m = I.m := rfl

/-- The length of `2^j I` is `2^j |I|`. -/
theorem length_dil : (I.dil j).length = (2 : ℝ) ^ j * I.length := by
  unfold length dil; simp only; rw [zpow_add₀ (by norm_num)]; ring

/-- The left end point of `2^j I` is `2^j` times that of `I`. -/
theorem left_dil : (I.dil j).left = (2 : ℝ) ^ j * I.left := by
  unfold left dil; simp only; rw [zpow_add₀ (by norm_num)]; ring

/-- The right end point of `2^j I` is `2^j` times that of `I`. -/
theorem right_dil : (I.dil j).right = (2 : ℝ) ^ j * I.right := by
  unfold right dil; simp only; rw [zpow_add₀ (by norm_num)]; ring

/-- The center of `2^j I` is `2^j` times that of `I`. -/
theorem center_dil : (I.dil j).center = (2 : ℝ) ^ j * I.center := by
  unfold center dil; simp only; rw [zpow_add₀ (by norm_num)]; ring

@[simp] theorem side_dil : (I.dil j).side = I.side := rfl

/-- `x ∈ 2^j I` iff `2^{-j} x ∈ I`. -/
theorem mem_toSet_dil {x : ℝ} : x ∈ (I.dil j).toSet ↔ ((2 : ℝ) ^ j)⁻¹ * x ∈ I.toSet := by
  have hs : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) _
  simp only [mem_toSet, left_dil, right_dil]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [le_inv_mul_iff₀ hs]; exact h1
    · rw [inv_mul_lt_iff₀ hs]; exact h2
  · rintro ⟨h1, h2⟩
    constructor
    · rw [le_inv_mul_iff₀ hs] at h1; exact h1
    · rw [inv_mul_lt_iff₀ hs] at h2; exact h2

/-- `x ∈ C (2^j I)` iff `2^{-j} x ∈ C I`. -/
theorem mem_dilate_dil (C : ℝ) {x : ℝ} :
    x ∈ (I.dil j).dilate C ↔ ((2 : ℝ) ^ j)⁻¹ * x ∈ I.dilate C := by
  have hs : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) _
  simp only [dilate, mem_Ico, center_dil, length_dil]
  have e1 : (2 : ℝ) ^ j * I.center - C * ((2 : ℝ) ^ j * I.length) / 2 =
      (2 : ℝ) ^ j * (I.center - C * I.length / 2) := by ring
  have e2 : (2 : ℝ) ^ j * I.center + C * ((2 : ℝ) ^ j * I.length) / 2 =
      (2 : ℝ) ^ j * (I.center + C * I.length / 2) := by ring
  rw [e1, e2]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [le_inv_mul_iff₀ hs]; exact h1
    · rw [inv_mul_lt_iff₀ hs]; exact h2
  · rintro ⟨h1, h2⟩
    constructor
    · rw [le_inv_mul_iff₀ hs] at h1; exact h1
    · rw [inv_mul_lt_iff₀ hs] at h2; exact h2

end Dyadic

namespace Idx

/-- `ζ ∈ (2^j u) + a |2^j u|` iff `2^{-j} ζ ∈ u + a |u|`. -/
theorem mem_shift_dil_toSet (u : Dyadic) (j a : ℤ) (ζ : ℝ) :
    ζ ∈ ((u.dil j).shift a).toSet ↔ ((2 : ℝ) ^ j)⁻¹ * ζ ∈ (u.shift a).toSet := by
  have hs : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) _
  rw [Dyadic.mem_shift_toSet, Dyadic.mem_shift_toSet, Dyadic.mem_toSet_dil, Dyadic.length_dil]
  have : ((2 : ℝ) ^ j)⁻¹ * (ζ - a * ((2 : ℝ) ^ j * u.length)) =
      ((2 : ℝ) ^ j)⁻¹ * ζ - a * u.length := by field_simp
  rw [this]

/-- `ζ ∈ ω_l(2^j u)` iff `2^{-j} ζ ∈ ω_l(u)`. -/
theorem mem_ωl_dil (ρ : Idx) (u : Dyadic) (j : ℤ) (ζ : ℝ) :
    ζ ∈ ρ.ωl (u.dil j) ↔ ((2 : ℝ) ^ j)⁻¹ * ζ ∈ ρ.ωl u := by
  have hs : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) _
  unfold ωl
  cases ρ.typ
  · exact mem_shift_dil_toSet u j _ ζ
  · exact mem_shift_dil_toSet u j _ ζ
  · simp only [mem_Iio, Dyadic.right_dil, Dyadic.length_dil]
    rw [inv_mul_lt_iff₀ hs]
    constructor <;> intro h <;> linarith

/-- `ζ ∈ ω_h(2^j u)` iff `2^{-j} ζ ∈ ω_h(u)`. -/
theorem mem_ωh_dil (ρ : Idx) (u : Dyadic) (j : ℤ) (ζ : ℝ) :
    ζ ∈ ρ.ωh (u.dil j) ↔ ((2 : ℝ) ^ j)⁻¹ * ζ ∈ ρ.ωh u := by
  have hs : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) _
  unfold ωh
  cases ρ.typ
  · exact mem_shift_dil_toSet u j _ ζ
  · simp only [mem_Ici, Dyadic.left_dil, Dyadic.length_dil]
    rw [le_inv_mul_iff₀ hs]
    constructor <;> intro h <;> linarith
  · exact mem_shift_dil_toSet u j _ ζ

end Idx

/-- `𝓕⁻[g(s ·)](t) = s⁻¹ 𝓕⁻[g](t/s)` for `s > 0`. -/
theorem fourierInv_comp_mul_left (g : ℝ → ℂ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    𝓕⁻ (fun ξ => g (s * ξ)) t = ((s⁻¹ : ℝ) : ℂ) * 𝓕⁻ g (s⁻¹ * t) := by
  rw [fourierInv_eq_integral_e, fourierInv_eq_integral_e]
  have h := Measure.integral_comp_mul_left (fun η : ℝ => e (η * (s⁻¹ * t)) * g η) s
  have h1 : ∀ ξ : ℝ, e (ξ * t) * g (s * ξ) = e ((s * ξ) * (s⁻¹ * t)) * g (s * ξ) := by
    intro ξ
    have : (s * ξ) * (s⁻¹ * t) = ξ * t := by field_simp
    rw [this]
  simp_rw [h1]
  rw [h, abs_inv, abs_of_pos hs, Complex.real_smul]

/-- The frequency profile of `2^{-j} J` is that of `J` evaluated at `2^j ξ`. -/
theorem freqProfile_dil (χ : ℝ → ℝ) (J : Dyadic) (j : ℤ) (ξ : ℝ) :
    freqProfile χ (J.dil (-j)) ξ = freqProfile χ J ((2 : ℝ) ^ j * ξ) := by
  have hs : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) _
  unfold freqProfile
  rw [Dyadic.center_dil, Dyadic.length_dil, zpow_neg]
  congr 3
  field_simp

/-- **Dilation of a wave packet**: `φ_{2^j I × 2^{-j} J}(2^j y) = 2^{-j/2} φ_{I × J}(y)`. -/
theorem wavePacketOf_dil (χ : ℝ → ℝ) (I J : Dyadic) (j : ℤ) (y : ℝ) :
    wavePacketOf χ (I.dil j) (J.dil (-j)) ((2 : ℝ) ^ j * y) =
      (((√((2 : ℝ) ^ j))⁻¹ : ℝ) : ℂ) * wavePacketOf χ I J y := by
  have hs : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) _
  set s : ℝ := (2 : ℝ) ^ j with hsdef
  have hfun : freqProfile χ (J.dil (-j)) = fun ξ => freqProfile χ J (s * ξ) :=
    funext (freqProfile_dil χ J j)
  unfold wavePacketOf
  rw [hfun, fourierInv_comp_mul_left _ hs, Dyadic.length_dil, Dyadic.center_dil]
  have e1 : s⁻¹ * (s * y - s * I.center) = y - I.center := by field_simp
  rw [e1, Real.sqrt_mul hs.le]
  have hsq : √s * √s = s := Real.mul_self_sqrt hs.le
  have hsq0 : 0 < √s := Real.sqrt_pos.2 hs
  push_cast
  have : (s⁻¹ : ℂ) = ((√s : ℂ))⁻¹ * ((√s : ℂ))⁻¹ := by
    rw [← mul_inv]
    congr 1
    exact_mod_cast hsq.symm
  rw [this]
  have hne : ((√s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsq0.ne'
  field_simp

/-- The dilation of dyadic intervals is injective. -/
theorem Dyadic.dil_injective (j : ℤ) : Function.Injective (fun I : Dyadic => I.dil j) := by
  intro I J h
  have h1 := congrArg Dyadic.k h
  have h2 := congrArg Dyadic.m h
  simp only [Dyadic.dil_k, Dyadic.dil_m] at h1 h2
  exact Dyadic.ext (by omega) h2

/-- **Dilation of a multitile**: `(I, ω_u) ↦ (2^j I, 2^{-j} ω_u)` (the area `|I||ω_u| = 1/2` and
the side of `ω_u` are preserved). -/
def Multitile.dil {ρ : Idx} (j : ℤ) (P : Multitile ρ) : Multitile ρ where
  I := P.I.dil j
  ωu := P.ωu.dil (-j)
  area := by have := P.area; simp only [Dyadic.dil_k]; omega
  side_eq := by rw [Dyadic.side_dil]; exact P.side_eq

/-- The dilation of `ρ`-multitiles is injective. -/
theorem Multitile.dil_injective (ρ : Idx) (j : ℤ) :
    Function.Injective (Multitile.dil (ρ := ρ) j) := by
  intro P Q h
  have h1 := congrArg Multitile.I h
  have h2 := congrArg Multitile.ωu h
  simp only [Multitile.dil] at h1 h2
  exact Multitile.ext (Dyadic.dil_injective j h1) (Dyadic.dil_injective (-j) h2)

namespace Multitile

variable {ρ : Idx} {r : ℝ}

/-- `ζ ∈ ω_l(P^j)` iff `2^j ζ ∈ ω_l(P)`. -/
theorem mem_ωl_dil (P : Multitile ρ) (j : ℤ) (ζ : ℝ) :
    ζ ∈ (P.dil j).ωl ↔ (2 : ℝ) ^ j * ζ ∈ P.ωl := by
  unfold ωl
  change ζ ∈ ρ.ωl (P.ωu.dil (-j)) ↔ _
  rw [Idx.mem_ωl_dil, zpow_neg, inv_inv]

/-- `ζ ∈ ω_h(P^j)` iff `2^j ζ ∈ ω_h(P)`. -/
theorem mem_ωh_dil (P : Multitile ρ) (j : ℤ) (ζ : ℝ) :
    ζ ∈ (P.dil j).ωh ↔ (2 : ℝ) ^ j * ζ ∈ P.ωh := by
  unfold ωh
  change ζ ∈ ρ.ωh (P.ωu.dil (-j)) ↔ _
  rw [Idx.mem_ωh_dil, zpow_neg, inv_inv]

end Multitile

open Classical in
/-- **Dilation of the linearizing data**: `ξ'_k(y) = 2^{-j} ξ_k(2^{-j} y)`,
`a'_k(y) = a_k(2^{-j} y)`, `Ξ' = 2^{-j} Ξ`. -/
def Linearization.dil {r : ℝ} (L : Linearization r) (j : ℤ) : Linearization r where
  K := L.K
  Ξ := L.Ξ.image (fun ζ => ((2 : ℝ) ^ j)⁻¹ * ζ)
  ξ k y := ((2 : ℝ) ^ j)⁻¹ * L.ξ k (((2 : ℝ) ^ j)⁻¹ * y)
  a k y := L.a k (((2 : ℝ) ^ j)⁻¹ * y)
  measurable_ξ k :=
    measurable_const.mul ((L.measurable_ξ k).comp (measurable_const.mul measurable_id))
  strictMono_ξ y i i' h := by
    have hs : 0 < ((2 : ℝ) ^ j)⁻¹ := inv_pos.2 (zpow_pos (by norm_num) _)
    exact mul_lt_mul_of_pos_left (L.strictMono_ξ _ h) hs
  ξ_mem k y := Finset.mem_image.2 ⟨_, L.ξ_mem _ _, rfl⟩
  measurable_a k := (L.measurable_a k).comp (measurable_const.mul measurable_id)
  sum_norm_rpow y := L.sum_norm_rpow _

namespace Multitile

variable {ρ : Idx} {r : ℝ}

/-- **The coefficient `a_P` of the dilated multitile**: `a_{P^j}(2^j x) = a_P(x)` for the dilated
data. -/
theorem aP_dil (L : Linearization r) (P : Multitile ρ) (j : ℤ) (x : ℝ) :
    (P.dil j).aP (L.dil j) ((2 : ℝ) ^ j * x) = P.aP L x := by
  classical
  have hs : (2 : ℝ) ^ j ≠ 0 := (zpow_pos (by norm_num) _).ne'
  unfold aP
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : ((2 : ℝ) ^ j)⁻¹ * ((2 : ℝ) ^ j * x) = x := by field_simp
  have e2 : ∀ ζ : ℝ, (2 : ℝ) ^ j * (((2 : ℝ) ^ j)⁻¹ * ζ) = ζ := fun ζ => by field_simp
  simp only [Linearization.dil, mem_ωl_dil, mem_ωh_dil, e, e2]

/-- **The wave packet of the dilated multitile**: `φ_{P^j}(2^j y) = 2^{-j/2} φ_P(y)`. -/
theorem wavePacket_dil (ch : ProfileChoice) (P : Multitile ρ) (j : ℤ) (y : ℝ) :
    (P.dil j).wavePacket ch ((2 : ℝ) ^ j * y) =
      (((√((2 : ℝ) ^ j))⁻¹ : ℝ) : ℂ) * P.wavePacket ch y := by
  unfold wavePacket packetOf
  exact wavePacketOf_dil ch.fn P.I P.ωu j y

/-- **The coefficient of the dilated multitile**: `⟨f(2^{-j} ·), φ_{P^j}⟩ = 2^{j/2} ⟨f, φ_P⟩`. -/
theorem coeff_dil (ch : ProfileChoice) (P : Multitile ρ) (j : ℤ) (f : ℝ → ℂ) :
    (P.dil j).coeff ch (fun y => f (((2 : ℝ) ^ j)⁻¹ * y)) =
      ((√((2 : ℝ) ^ j) : ℝ) : ℂ) * P.coeff ch f := by
  have hs : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) _
  have hsq0 : 0 < √((2 : ℝ) ^ j) := Real.sqrt_pos.2 hs
  have hsq : √((2 : ℝ) ^ j) * √((2 : ℝ) ^ j) = (2 : ℝ) ^ j := Real.mul_self_sqrt hs.le
  unfold coeff pairing
  have h := Measure.integral_comp_mul_left
    (fun y : ℝ => f (((2 : ℝ) ^ j)⁻¹ * y) * (starRingEnd ℂ) ((P.dil j).wavePacket ch y))
    ((2 : ℝ) ^ j)
  have h1 : ∀ x : ℝ, f (((2 : ℝ) ^ j)⁻¹ * ((2 : ℝ) ^ j * x)) *
      (starRingEnd ℂ) ((P.dil j).wavePacket ch ((2 : ℝ) ^ j * x)) =
      (((√((2 : ℝ) ^ j))⁻¹ : ℝ) : ℂ) * (f x * (starRingEnd ℂ) (P.wavePacket ch x)) := by
    intro x
    have e : ((2 : ℝ) ^ j)⁻¹ * ((2 : ℝ) ^ j * x) = x := by field_simp
    rw [e, wavePacket_dil, map_mul, Complex.conj_ofReal]
    ring
  simp_rw [h1] at h
  rw [integral_const_mul, abs_inv, abs_of_pos hs, Complex.real_smul] at h
  have hsq' : (((2 : ℝ) ^ j : ℝ) : ℂ) =
      ((√((2 : ℝ) ^ j) : ℝ) : ℂ) * ((√((2 : ℝ) ^ j) : ℝ) : ℂ) := by
    exact_mod_cast hsq.symm
  have hne2 : ((√((2 : ℝ) ^ j) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsq0.ne'
  have h' : ∫ y, f (((2 : ℝ) ^ j)⁻¹ * y) * (starRingEnd ℂ) ((P.dil j).wavePacket ch y) =
      (((2 : ℝ) ^ j : ℝ) : ℂ) * ((((√((2 : ℝ) ^ j))⁻¹ : ℝ) : ℂ) *
        ∫ x, f x * (starRingEnd ℂ) (P.wavePacket ch x)) := by
    rw [h, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hs.ne', Complex.ofReal_one, one_mul]
  rw [h', hsq']
  push_cast
  field_simp

/-- **The dilation identity for the model operator**:
`𝒮^ρ_{P^j}[f(2^{-j} ·)](2^j x) = 𝒮^ρ_P[f](x)`. -/
theorem modelOp_dil (ch : ProfileChoice) (L : Linearization r) (S : Finset (Multitile ρ))
    (f : ℝ → ℂ) (j : ℤ) (x : ℝ) :
    modelOp ch (L.dil j) (S.image (Multitile.dil j)) (fun y => f (((2 : ℝ) ^ j)⁻¹ * y))
      ((2 : ℝ) ^ j * x) = modelOp ch L S f x := by
  classical
  have hs : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) _
  have hsq0 : 0 < √((2 : ℝ) ^ j) := Real.sqrt_pos.2 hs
  have hne2 : ((√((2 : ℝ) ^ j) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsq0.ne'
  unfold modelOp
  rw [Finset.sum_image (fun P _ Q _ h => Multitile.dil_injective ρ j h)]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [coeff_dil, wavePacket_dil, aP_dil]
  push_cast
  field_simp

end Multitile


/-- The dilation `y ↦ a y` is quasi measure preserving for the Lebesgue measure. -/
theorem quasiMeasurePreserving_mul_left_real {a : ℝ} (ha : a ≠ 0) :
    QuasiMeasurePreserving (fun y : ℝ => a * y) volume volume := by
  refine ⟨measurable_const.mul measurable_id, ?_⟩
  rw [Real.map_volume_mul_left ha]
  exact Measure.smul_absolutelyContinuous

/-- `|{y : s⁻¹ y ∈ A}| = s |A|`. -/
theorem volume_preimage_inv_mul {s : ℝ} (hs : 0 < s) (A : Set ℝ) :
    volume ((fun y : ℝ => s⁻¹ * y) ⁻¹' A) = ENNReal.ofReal s * volume A := by
  have h := Real.volume_preimage_mul_left (inv_ne_zero hs.ne') A
  rw [inv_inv, abs_of_pos hs] at h
  exact h

/-- The separation assumptions are preserved by the dilation of multitiles. -/
theorem Separated.dil {ρ : Idx} {C₁ C₂ C₃ : ℝ} {S : Set (Multitile ρ)}
    (h : Separated C₁ C₂ C₃ S) (j : ℤ) : Separated C₁ C₂ C₃ (Multitile.dil j '' S) := by
  have hs : 0 < ((2 : ℝ) ^ (-j)) := zpow_pos (by norm_num) _
  have hlen : ∀ P : Multitile ρ, (P.dil j).ωu.length = (2 : ℝ) ^ (-j) * P.ωu.length := fun P =>
    Dyadic.length_dil P.ωu (-j)
  refine ⟨?_, ?_⟩
  · rintro _ ⟨P, hP, rfl⟩ _ ⟨Q, hQ, rfl⟩ hlt
    rw [hlen, hlen] at hlt ⊢
    have h1 : Q.ωu.length < P.ωu.length := lt_of_mul_lt_mul_left hlt hs.le
    have h2 := h.scales P hP Q hQ h1
    calc (2 : ℝ) ^ (-j) * Q.ωu.length ≤ (2 : ℝ) ^ (-j) * ((C₂ - C₃) / (2 * C₁) * P.ωu.length) :=
          mul_le_mul_of_nonneg_left h2 hs.le
      _ = (C₂ - C₃) / (2 * C₁) * ((2 : ℝ) ^ (-j) * P.ωu.length) := by ring
  · rintro _ ⟨P, hP, rfl⟩ _ ⟨Q, hQ, rfl⟩ ⟨x, hx1, hx2⟩ hl
    rw [hlen, hlen] at hl
    have hl' : P.ωu.length = Q.ωu.length := mul_left_cancel₀ hs.ne' hl
    have hx1' : ((2 : ℝ) ^ (-j))⁻¹ * x ∈ P.ωuDil C₁ := (Dyadic.mem_dilate_dil _ _ _).1 hx1
    have hx2' : ((2 : ℝ) ^ (-j))⁻¹ * x ∈ Q.ωuDil C₁ := (Dyadic.mem_dilate_dil _ _ _).1 hx2
    have := h.prop2 P hP Q hQ ⟨_, hx1', hx2'⟩ hl'
    change P.ωu.dil (-j) = Q.ωu.dil (-j)
    rw [this]

/-- The scale `s = 2^j` bringing `|E|` into `[1, 2]`. -/
theorem exists_zpow_mul_mem_Icc {e : ℝ} (he : 0 < e) :
    ∃ j : ℤ, 1 ≤ (2 : ℝ) ^ j * e ∧ (2 : ℝ) ^ j * e ≤ 2 := by
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow he (one_lt_two : (1 : ℝ) < 2)
  refine ⟨-n, ?_, ?_⟩
  · rw [zpow_neg]
    rw [← div_eq_inv_mul, le_div_iff₀ (zpow_pos (by norm_num) _)]
    linarith
  · rw [zpow_neg]
    rw [← div_eq_inv_mul, div_le_iff₀ (zpow_pos (by norm_num) _)]
    rw [zpow_add_one₀ (by norm_num)] at hn2
    linarith

/-- **`halfgbound`** ([O+] L1155-L1158): (halfgbound) for a separated family and
every measurable `E` with `0 < |E| < ∞`, from the case `1 ≤ |E| ≤ 2` (`mainargumentsection`),
with the same constant: the dilation `x ↦ 2^j x` maps multitiles to multitiles, preserves the
separation assumptions, the packets (up to the factor `2^{-j/2}` cancelled by the coefficients) and
the ratio `|F|/|E|`. -/
theorem halfgbound_separated {r p : ℝ} (hr : 2 < r) (hp1 : Real.conjExponent r ≤ p)
    (hp2 : p < 2 * r / (r - 2)) {C₁ C₂ C₃ : ℝ} (hC : AdmissibleConstants C₁ C₂ C₃)
    (hC₂ : C₂ = 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo], ρ.IsStd → ∀ (ch : ProfileChoice)
      {f : ℝ → ℂ} {F E : Set ℝ}, MeasurableSet F → volume F ≠ 0 → volume F ≠ ⊤ →
      AEStronglyMeasurable f volume → (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) →
      MeasurableSet E → volume E ≠ 0 → volume E ≠ ⊤ → ∀ (L : Linearization r)
      (𝔓 : Finset (Multitile ρ)), Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)) →
      volume {x | x ∈ E ∧ C * ((volume F).toReal / (volume E).toReal) ^ (1 / p) <
        ‖modelOp ch L 𝔓 f x‖} ≤ volume E / 2 := by
  obtain ⟨C, hC0, hmain⟩ := mainargumentsection hr hp1 hp2 hC hC₂
  refine ⟨C, hC0, ?_⟩
  intro ρ _ hρ ch f F E hF hF0 hFt hfm hfF hE hE0 hEt L 𝔓 hsep
  have hepos : 0 < (volume E).toReal := ENNReal.toReal_pos hE0 hEt
  obtain ⟨j, hj1, hj2⟩ := exists_zpow_mul_mem_Icc hepos
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = (2 : ℝ) ^ j := ⟨_, rfl⟩
  rw [← hsdef] at hj1 hj2
  have hs : 0 < s := hsdef ▸ zpow_pos (by norm_num) _
  have hsne : s ≠ 0 := hs.ne'
  have hsi : s⁻¹ ≠ 0 := inv_ne_zero hsne
  have hqmp : QuasiMeasurePreserving (fun y : ℝ => s⁻¹ * y) volume volume :=
    quasiMeasurePreserving_mul_left_real hsi
  have hscm : Measurable (fun y : ℝ => s⁻¹ * y) := measurable_const.mul measurable_id
  obtain ⟨E', hE'⟩ : ∃ E' : Set ℝ, E' = (fun y : ℝ => s⁻¹ * y) ⁻¹' E := ⟨_, rfl⟩
  obtain ⟨F', hF'⟩ : ∃ F' : Set ℝ, F' = (fun y : ℝ => s⁻¹ * y) ⁻¹' F := ⟨_, rfl⟩
  have hvE' : volume E' = ENNReal.ofReal s * volume E := by
    rw [hE']; exact volume_preimage_inv_mul hs E
  have hvF' : volume F' = ENNReal.ofReal s * volume F := by
    rw [hF']; exact volume_preimage_inv_mul hs F
  have hvE'r : (volume E').toReal = s * (volume E).toReal := by
    rw [hvE', ENNReal.toReal_mul, ENNReal.toReal_ofReal hs.le]
  have hvF'r : (volume F').toReal = s * (volume F).toReal := by
    rw [hvF', ENNReal.toReal_mul, ENNReal.toReal_ofReal hs.le]
  have hE't : volume E' ≠ ⊤ := by
    rw [hvE']; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEt
  have hE'1 : 1 ≤ volume E' := by
    rw [← ENNReal.ofReal_toReal hE't, hvE'r]
    exact ENNReal.one_le_ofReal.2 hj1
  have hE'2 : volume E' ≤ 2 := by
    rw [← ENNReal.ofReal_toReal hE't, hvE'r]
    calc ENNReal.ofReal (s * (volume E).toReal) ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hj2
      _ = 2 := by simp
  have hF'0 : volume F' ≠ 0 := by
    rw [hvF']
    exact mul_ne_zero (ENNReal.ofReal_pos.2 hs).ne' hF0
  have hF't : volume F' ≠ ⊤ := by
    rw [hvF']; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFt
  have hfm' : AEStronglyMeasurable (fun y => f (s⁻¹ * y)) volume :=
    hfm.comp_quasiMeasurePreserving hqmp
  have hfF' : ∀ᵐ y, ‖f (s⁻¹ * y)‖ ≤ F'.indicator (fun _ => (1 : ℝ)) y := by
    filter_upwards [hqmp.ae hfF] with y hy
    have hi : F'.indicator (fun _ => (1 : ℝ)) y = F.indicator (fun _ => (1 : ℝ)) (s⁻¹ * y) := by
      by_cases h : s⁻¹ * y ∈ F
      · have h' : y ∈ F' := by rw [hF']; exact h
        rw [Set.indicator_of_mem h', Set.indicator_of_mem h]
      · have h' : y ∉ F' := by rw [hF']; exact h
        rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]
    rw [hi]; exact hy
  have hsep' : Separated C₁ C₂ C₃ (((𝔓.image (Multitile.dil j)) : Finset (Multitile ρ)) :
      Set (Multitile ρ)) := by
    rw [Finset.coe_image]
    exact hsep.dil j
  have key := hmain hρ ch (by rw [hF']; exact hF.preimage hscm) hF'0 hF't hfm' hfF'
    (by rw [hE']; exact hE.preimage hscm) hE'1 hE'2 (L.dil j) (𝔓.image (Multitile.dil j)) hsep'
  have hset : {y | y ∈ E' ∧ C * ((volume F').toReal / (volume E').toReal) ^ (1 / p) <
      ‖modelOp ch (L.dil j) (𝔓.image (Multitile.dil j)) (fun y => f (s⁻¹ * y)) y‖} =
      (fun y : ℝ => s⁻¹ * y) ⁻¹' {x | x ∈ E ∧
        C * ((volume F).toReal / (volume E).toReal) ^ (1 / p) < ‖modelOp ch L 𝔓 f x‖} := by
    ext y
    have hratio : (volume F').toReal / (volume E').toReal =
        (volume F).toReal / (volume E).toReal := by
      rw [hvF'r, hvE'r, mul_div_mul_left _ _ hsne]
    have hmod : modelOp ch (L.dil j) (𝔓.image (Multitile.dil j)) (fun y => f (s⁻¹ * y)) y =
        modelOp ch L 𝔓 f (s⁻¹ * y) := by
      have := Multitile.modelOp_dil ch L 𝔓 f j (s⁻¹ * y)
      rw [← hsdef] at this
      rw [← this]
      congr 1
      field_simp
    have hmem : y ∈ E' ↔ s⁻¹ * y ∈ E := by rw [hE']; rfl
    simp only [Set.mem_ofPred_eq, mem_preimage, hmem, hratio, hmod]
  rw [hset] at key
  have hl := volume_preimage_inv_mul hs
    {x | x ∈ E ∧ C * ((volume F).toReal / (volume E).toReal) ^ (1 / p) <
        ‖modelOp ch L 𝔓 f x‖}
  rw [hl, hvE'] at key
  have hs0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.2 hs).ne'
  rw [mul_div_assoc] at key
  exact (ENNReal.mul_le_mul_iff_right hs0 ENNReal.ofReal_ne_top).1 key

end PrimeCarleson.Proof.Oplus

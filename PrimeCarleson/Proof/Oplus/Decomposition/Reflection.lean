module

public import PrimeCarleson.Proof.Oplus.Decomposition.ModelOperator

/-!
# The reflection identity: 3-indices by symmetry ([O+] L1097-L1121)

[O+] L1097-L1121: "We shall only give the proof of this
estimate for the case that `ρ` is a `1`-index or `ρ` is a `2`-index, and the case where `ρ` is a
`3`-index can be deduced by symmetry considerations. Indeed, if `P = (I, ω_u) := ([a,b), [c,d))`
and `P̃ := ([-b,a), [-d,c))` then `⟨f, φ_P⟩ φ_P = ⟨f(-·), φ̃_{P̃}⟩ φ̃_{P̃}` where, in the definition
of the `φ̃_{P̃}` the function `ν_i` in (nu-functions) is replaced with `ν_i(-·)` [...]. We then
see that the estimation of `𝒮^ρ[f]` for `ρ = (3,m,n,side)` is equivalent to the estimation of a
`𝒮^{ρ̃}[f(-·)]` where the corresponding set `{P}` of multitiles is replaced with a set `{P̃}` of
index `ρ̃ = (2,n,m,opposite side)` and the set `Ξ` is replaced with `{ξ : -ξ ∈ Ξ}`". Source: [O+],
L1099–L1118: the printed `P̃ = ([-b,a), [-d,c))` is a typo for `([-b,-a), [-d,-c))`, the identity
needs the evaluation at `-x`, and the reversed data `ξ̃_k(y) = -ξ_{K-k}(-y)`,
`ã_k(y) = a_{K+1-k}(-y)` are not written; `ρ̃ ∉ R` for the three `3`-indices of `R`
(`(2,1,4,right)`, `(2,1,3,left)`, `(2,2,4,right)`), which is why the sections 4-7 are proved for
every index and both profiles.

* `Dyadic.refl` (`[a,b) ↦ [-b,-a)`, the half-open interval with the reflected end points; the
  reflection of `[a,b)` is `(-b,-a]`, which differs from it only at the end points),
  `Idx.refl` (`(3,m,n,side) ↦ (2,n,m,opposite side)`; types `1 ↔ 1`, `2 ↔ 3`),
  `Multitile.refl : Multitile ρ → Multitile ρ.refl` (item (1)), `ProfileChoice.flip`
  (`ν_i ↔ ν_i(-·)`), `Linearization.refl` (item (3));
* `Idx.neg_mem_ωl_refl`, `Idx.neg_mem_ωh_refl`: for `ζ` outside the dyadic end points
  `-ζ ∈ ω̃_l ↔ ζ ∈ ω_h` and `-ζ ∈ ω̃_h ↔ ζ ∈ ω_l` (item (1): `-ω_h = ω̃_l`, `-ω_l = ω̃_h` up to
  end points; they are the numbers `n 2^m`);
* `wavePacketOf_refl`, `Multitile.wavePacket_refl`, `Multitile.coeff_refl` (item (2):
  `φ̃_{P̃}(-x) = φ_P(x)` and `⟨f(-·), φ̃_{P̃}⟩ = ⟨f, φ_P⟩`), `Multitile.aP_refl` (item (3):
  `a_{P̃}(-x) = a_P(x)`);
* `modelOp_refl` (item (4)): `𝒮^ρ_{ch,L}[f](x) = 𝒮^{ρ̃}_{ch~,L~}[f(-·)](-x)` for the reflected
  family `{P̃}`. Since `x ↦ -x` preserves Lebesgue measure and every Lorentz norm, every bound
  for the operator `𝒮^{ρ̃}_{ch~,L~}` transfers to `𝒮^ρ_{ch,L}`. The statement holds for every
  index type (`1 ↦ 1`, `2 ↦ 3`, `3 ↦ 2`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap ContDiff ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

namespace Dyadic

variable (I : Dyadic)

/-- The reflection `x ↦ -x` of a dyadic interval: `[a, b) ↦ [-b, -a)` (the half-open interval
with the reflected end points; the reflection of `[a, b)` itself is `(-b, -a]`, which differs from
it only at the end points, [O+] L1113-L1118). -/
def refl : Dyadic := ⟨I.k, -I.m - 1⟩

@[simp] theorem refl_k : I.refl.k = I.k := rfl

theorem length_refl : I.refl.length = I.length := rfl

theorem left_refl : I.refl.left = -I.right := by
  unfold refl left right; push_cast; ring

theorem right_refl : I.refl.right = -I.left := by
  unfold refl left right; push_cast; ring

theorem center_refl : I.refl.center = -I.center := by
  unfold refl center; push_cast; ring

theorem refl_refl : I.refl.refl = I := by
  unfold refl; ext <;> simp

theorem side_refl : I.refl.side = I.side.opp := by
  unfold side refl Side.opp
  split_ifs with h1 h2 h2 <;> simp_all <;> omega

end Dyadic

/-- Reflection in the frequency variable: `𝓕⁻[g(-·)](t) = 𝓕⁻[g](-t)`. -/
theorem fourierInv_comp_neg (g : ℝ → ℂ) (t : ℝ) : 𝓕⁻ (fun ξ => g (-ξ)) t = 𝓕⁻ g (-t) := by
  rw [fourierInv_eq_integral_e, fourierInv_eq_integral_e]
  rw [← integral_neg_eq_self (fun ξ => e (ξ * t) * g (-ξ)) volume]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [neg_neg, neg_mul, mul_neg]

variable {χ : ℝ → ℝ}

/-- **Reflection of a wave packet**: with the reflected profile `χ(-·)` and the reflected
intervals, `φ̃_{Ĩ×J̃}(-x) = φ_{I×J}(x)` ([O+] L1099-L1107). -/
theorem wavePacketOf_refl (χ : ℝ → ℝ) (I J : Dyadic) (y : ℝ) :
    wavePacketOf (fun η => χ (-η)) I.refl J.refl y = wavePacketOf χ I J (-y) := by
  unfold wavePacketOf
  rw [Dyadic.length_refl, Dyadic.center_refl]
  have : freqProfile (fun η => χ (-η)) J.refl = fun ξ => freqProfile χ J (-ξ) := by
    funext ξ
    unfold freqProfile
    rw [Dyadic.length_refl, Dyadic.center_refl]
    have h : -((ξ - -J.center) / J.length) = (-ξ - J.center) / J.length := by ring
    beta_reduce
    rw [h]
  rw [this, fourierInv_comp_neg]
  have h3 : -(y - -I.center) = -y - I.center := by ring
  rw [h3]

/-- The other orientation of the profile. -/
def Orientation.flip : Orientation → Orientation
  | .plain => .reflected
  | .reflected => .plain

/-- The reflected profile choice: `ν_i ↔ ν_i(-·)`. -/
def ProfileChoice.flip (c : ProfileChoice) : ProfileChoice :=
  ⟨c.i, c.neg_one_le, c.le_one, c.orientation.flip⟩

theorem ProfileChoice.flip_fn (c : ProfileChoice) : c.flip.fn = fun η => c.fn (-η) := by
  unfold ProfileChoice.fn ProfileChoice.flip
  cases h : c.orientation
  · simp [Orientation.flip]
  · simp [Orientation.flip]

/-- The reflected type of an index: `1 ↔ 1`, `2 ↔ 3`. -/
def IdxType.refl : IdxType → IdxType
  | .one => .one
  | .two => .three
  | .three => .two

/-- The reflected index `ρ̃ = (i~, n, m, opposite side)` of [O+] L1113-L1118 (`(3, m, n, side)`
becomes `(2, n, m, opposite side)`). -/
def Idx.refl (ρ : Idx) : Idx := ⟨ρ.typ.refl, ρ.n, ρ.m, ρ.side.opp⟩

/-- Reflection of a multitile: `P = (I, ω_u) ↦ P̃ = (Ĩ, ω̃_u)` with `[a,b) ↦ [-b,-a)`; `P̃` is a
`ρ̃`-multitile. -/
def Multitile.refl {ρ : Idx} (P : Multitile ρ) : Multitile ρ.refl where
  I := P.I.refl
  ωu := P.ωu.refl
  area := by have := P.area; simpa using this
  side_eq := by rw [Dyadic.side_refl, P.side_eq]; rfl

theorem Multitile.refl_injective (ρ : Idx) : Function.Injective (Multitile.refl (ρ := ρ)) := by
  intro P Q h
  have h1 := congrArg Dyadic.refl (congrArg Multitile.I h)
  have h2 := congrArg Dyadic.refl (congrArg Multitile.ωu h)
  simp only [Multitile.refl, Dyadic.refl_refl] at h1 h2
  exact Multitile.ext h1 h2

namespace Dyadic

/-- A number avoiding the dyadic end points differs from `u.left + j |u|`. -/
theorem ne_left_add {ζ : ℝ} (hζ : ∀ n m : ℤ, ζ ≠ n * 2 ^ m) (u : Dyadic) (j : ℤ) :
    ζ ≠ u.left + j * u.length := by
  intro h
  refine hζ (u.m + j) u.k ?_
  unfold left length at h
  push_cast
  linarith

end Dyadic

/-- **The frequency sets of the reflected multitile** (up to dyadic end points): for `ζ` avoiding
the numbers `n 2^m`, `-ζ ∈ ω̃_l` iff `ζ ∈ ω_h` ([O+] L1113-L1118; for a `3`-index `ρ = (3,m,n,side)`
and `ρ̃ = (2,n,m,opposite side)`: `-ω_h = ω̃_l` up to end points). -/
theorem Idx.neg_mem_ωl_refl (ρ : Idx) (u : Dyadic) {ζ : ℝ} (hζ : ∀ n m : ℤ, ζ ≠ n * 2 ^ m) :
    -ζ ∈ ρ.refl.ωl u.refl ↔ ζ ∈ ρ.ωh u := by
  have hL := u.length_pos
  have hr := u.right_eq
  have e1 := Dyadic.ne_left_add hζ u ((ρ.n : ℤ) + 1)
  have e2 := Dyadic.ne_left_add hζ u ((ρ.n : ℤ) + 2)
  push_cast at e1 e2
  obtain ⟨t, m, n, s⟩ := ρ
  cases t <;>
  simp only [Idx.refl, IdxType.refl, Idx.ωl, Idx.ωh, Idx.ωlDyadic, Dyadic.toSet,
    Dyadic.left_shift, Dyadic.right_shift, Dyadic.right_refl, Dyadic.left_refl, Dyadic.length_refl,
    mem_Ico, mem_Iio, mem_Ici] at e1 e2 ⊢ <;>
  push_cast <;>
  constructor <;> intro h
  · refine ⟨by linarith [h.2], lt_of_le_of_ne (by linarith [h.1]) ?_⟩
    intro h'
    apply e2
    rw [h', hr]
    ring
  · have : u.left + (↑n + 1) * u.length < ζ := lt_of_le_of_ne h.1 (Ne.symm e1)
    exact ⟨by linarith [h.2], by linarith⟩
  · linarith
  · have := lt_of_le_of_ne h (Ne.symm e1)
    linarith
  · refine ⟨by linarith [h.2], lt_of_le_of_ne (by linarith [h.1]) ?_⟩
    intro h'
    apply e2
    rw [h', hr]
    ring
  · have : u.left + (↑n + 1) * u.length < ζ := lt_of_le_of_ne h.1 (Ne.symm e1)
    exact ⟨by linarith [h.2], by linarith⟩

/-- Similarly, `-ζ ∈ ω̃_h` iff `ζ ∈ ω_l` (`-ω_l = ω̃_h` up to end points). -/
theorem Idx.neg_mem_ωh_refl (ρ : Idx) (u : Dyadic) {ζ : ℝ} (hζ : ∀ n m : ℤ, ζ ≠ n * 2 ^ m) :
    -ζ ∈ ρ.refl.ωh u.refl ↔ ζ ∈ ρ.ωl u := by
  have hL := u.length_pos
  have hr := u.right_eq
  have e1 := Dyadic.ne_left_add hζ u (-((ρ.m : ℤ) + 1))
  have e2 := Dyadic.ne_left_add hζ u (-(ρ.m : ℤ))
  push_cast at e1 e2
  obtain ⟨t, m, n, s⟩ := ρ
  cases t <;>
  simp only [Idx.refl, IdxType.refl, Idx.ωl, Idx.ωh, Idx.ωlDyadic, Dyadic.toSet,
    Dyadic.left_shift, Dyadic.right_shift, Dyadic.right_refl, Dyadic.left_refl, Dyadic.length_refl,
    mem_Ico, mem_Iio, mem_Ici] at e1 e2 ⊢ <;>
  push_cast <;>
  constructor <;> intro h
  · refine ⟨by linarith [h.2], lt_of_le_of_ne (by linarith [h.1]) ?_⟩
    intro h'
    apply e2
    rw [h', hr]
    ring
  · have : u.left + -(↑m + 1) * u.length < ζ := lt_of_le_of_ne h.1 (Ne.symm e1)
    exact ⟨by linarith [h.2], by linarith⟩
  · refine ⟨by linarith [h.2], lt_of_le_of_ne (by linarith [h.1]) ?_⟩
    intro h'
    apply e2
    rw [h', hr]
    ring
  · have : u.left + -(↑m + 1) * u.length < ζ := lt_of_le_of_ne h.1 (Ne.symm e1)
    exact ⟨by linarith [h.2], by linarith⟩
  · refine lt_of_le_of_ne (by linarith) ?_
    intro h'
    apply e2
    rw [h', hr]
    ring
  · linarith

open Classical in
/-- **The reversed linearizing data** of [O+] L1108-L1118: `ξ̃_k(y) = -ξ_{K-k}(-y)` for `k = 0..K`
and `ã_k(y) = a_{K+1-k}(-y)` for `k = 1..K` (in the indexing of `Linearization`,
`ξ̃ k y = -ξ (rev k) (-y)` and `ã k y = a (rev k) (-y)`). They are measurable, `ξ̃` is strictly
increasing with values in `-Ξ`, and `∑ |ã_k|^{r'} = 1`. -/
def Linearization.refl {r : ℝ} (L : Linearization r) : Linearization r where
  K := L.K
  Ξ := L.Ξ.image (fun ζ => -ζ)
  ξ k y := -L.ξ k.rev (-y)
  a k y := L.a k.rev (-y)
  measurable_ξ k := ((L.measurable_ξ k.rev).comp measurable_neg).neg
  strictMono_ξ y i j hij := by
    have := L.strictMono_ξ (-y) (Fin.rev_lt_rev.2 hij)
    simp only
    linarith
  ξ_mem k y := Finset.mem_image.2 ⟨_, L.ξ_mem _ _, rfl⟩
  measurable_a k := (L.measurable_a k.rev).comp measurable_neg
  sum_norm_rpow y := by
    rw [← L.sum_norm_rpow (-y)]
    exact Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)

namespace Multitile

variable {ρ : Idx} {r : ℝ}

/-- **The coefficient `a_P` of the reflected multitile**: `a_{P̃}(-x) = a_P(x)` for the reversed
data (`Ξ` without dyadic end points). -/
theorem aP_refl (L : Linearization r) (hΞ : AvoidsDyadicEndpoints (L.Ξ : Set ℝ))
    (P : Multitile ρ) (x : ℝ) : P.refl.aP L.refl (-x) = P.aP L x := by
  classical
  unfold aP
  refine Fintype.sum_equiv (Fin.revPerm (n := L.K)) _ _ (fun k' => ?_)
  have c1 : -L.ξ k'.rev.succ x ∈ P.refl.ωl ↔ L.ξ k'.rev.succ x ∈ P.ωh :=
    Idx.neg_mem_ωl_refl ρ P.ωu (hΞ _ (Finset.mem_coe.2 (L.ξ_mem _ x)))
  have c2 : -L.ξ k'.rev.castSucc x ∈ P.refl.ωh ↔ L.ξ k'.rev.castSucc x ∈ P.ωl :=
    Idx.neg_mem_ωh_refl ρ P.ωu (hΞ _ (Finset.mem_coe.2 (L.ξ_mem _ x)))
  simp only [Linearization.refl, Fin.rev_castSucc, Fin.rev_succ, neg_neg, Fin.revPerm_apply, c1,
    c2, and_comm]

/-- **The wave packet of the reflected multitile**: `φ̃_{P̃}(y) = φ_P(-y)`, with the reflected
profile `ν_i(-·)` ([O+] L1099-L1107). -/
theorem wavePacket_refl (ch : ProfileChoice) (P : Multitile ρ) (y : ℝ) :
    P.refl.wavePacket ch.flip y = P.wavePacket ch (-y) := by
  unfold wavePacket packetOf
  rw [ProfileChoice.flip_fn]
  exact wavePacketOf_refl ch.fn P.I P.ωu y

/-- **The coefficient of the reflected multitile**: `⟨f(-·), φ̃_{P̃}⟩ = ⟨f, φ_P⟩`. -/
theorem coeff_refl (ch : ProfileChoice) (P : Multitile ρ) (f : ℝ → ℂ) :
    P.refl.coeff ch.flip (fun y => f (-y)) = P.coeff ch f := by
  unfold coeff pairing
  simp_rw [wavePacket_refl]
  exact integral_neg_eq_self (fun z => f z * (starRingEnd ℂ) (P.wavePacket ch z)) volume

end Multitile

/-- The reflected index of a `3`-index is a `2`-index (so the analysis of `1`- and `2`-indices
applies to it). -/
theorem Idx.isOneOrTwo_refl_of_typ_three {ρ : Idx} (h : ρ.typ = IdxType.three) :
    ρ.refl.IsOneOrTwo := by
  unfold Idx.IsOneOrTwo Idx.refl
  rw [h]
  simp [IdxType.refl]

/-- Reflection exchanges `m` and `n`, so the range `m, n ∈ {1,…,4}` is preserved. -/
theorem Idx.isStd_refl {ρ : Idx} : ρ.refl.IsStd ↔ ρ.IsStd := by
  unfold Idx.IsStd Idx.refl
  simp only
  tauto

/-- **The reflection identity** ([O+] L1099-L1118): for a finite set `S` of `ρ`-multitiles (for a
`3`-index `ρ = (3,m,n,side)` the reflected index is `ρ̃ = (2,n,m,opposite side)`), profile `ch` and
data `L` with `Ξ` free of dyadic end points, `𝒮^ρ_{ch,L}[f](x) = 𝒮^{ρ̃}_{ch~,L~}[f(-·)](-x)` over
the reflected family `{P̃}`, with the reflected profile `ν_i(-·)` and the reversed data. -/
theorem modelOp_refl {ρ : Idx} {r : ℝ} (ch : ProfileChoice) (L : Linearization r)
    (hΞ : AvoidsDyadicEndpoints (L.Ξ : Set ℝ)) (S : Finset (Multitile ρ)) (f : ℝ → ℂ) (x : ℝ) :
    modelOp ch L S f x =
      modelOp ch.flip L.refl (S.image Multitile.refl) (fun y => f (-y)) (-x) := by
  classical
  unfold modelOp
  rw [Finset.sum_image (fun P _ Q _ h => Multitile.refl_injective ρ h)]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Multitile.coeff_refl, Multitile.wavePacket_refl, neg_neg, Multitile.aP_refl L hΞ]

end PrimeCarleson.Proof.Oplus

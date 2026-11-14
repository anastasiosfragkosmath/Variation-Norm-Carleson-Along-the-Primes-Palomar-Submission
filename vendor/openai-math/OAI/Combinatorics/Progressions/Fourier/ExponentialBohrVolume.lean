/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Fourier/ExponentialBohrVolume.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Combinatorics.Additive.Dissociation
public import Mathlib.Combinatorics.Pigeonhole
@[expose] public section

namespace OAI

section

namespace Erdos3

open AddChar Finset
open scoped BigOperators

namespace CyclicBohr

variable {N : ℕ} [NeZero N]

noncomputable def character (r : ZMod N) : AddChar (ZMod N) ℂ :=
  AddChar.zmodAddEquiv r

@[simp] lemma character_zero (r : ZMod N) : character r 0 = 1 := by
  exact AddChar.map_zero_eq_one _

@[simp] lemma character_add (r x y : ZMod N) :
    character r (x + y) = character r x * character r y := by
  exact AddChar.map_add_eq_mul _ _ _

@[simp] lemma norm_character (r x : ZMod N) : ‖character r x‖ = 1 := by
  simp [character]

lemma character_comm (r x : ZMod N) : character r x = character x r := by
  obtain ⟨r, rfl⟩ := ZMod.intCast_surjective r
  obtain ⟨x, rfl⟩ := ZMod.intCast_surjective x
  change (↑(AddChar.zmod N (r : ZMod N) (x : ZMod N)) : ℂ) =
    ↑(AddChar.zmod N (x : ZMod N) (r : ZMod N))
  rw [AddChar.zmod_intCast, AddChar.zmod_intCast]
  congr 1
  ring_nf
  rfl

@[simp] lemma character_zero_index (x : ZMod N) : character 0 x = 1 := by
  rw [character_comm, character_zero]

lemma norm_one_sub_mul_of_norm_le_one {a b : ℂ} (ha : ‖a‖ ≤ 1) :
    ‖1 - a * b‖ ≤ ‖1 - a‖ + ‖1 - b‖ := by
  calc
    ‖1 - a * b‖ = ‖(1 - a) + a * (1 - b)‖ := by ring_nf
    _ ≤ ‖1 - a‖ + ‖a * (1 - b)‖ := norm_add_le _ _
    _ ≤ ‖1 - a‖ + ‖1 - b‖ := by
      gcongr
      exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) ha)

structure Set (N : ℕ) [NeZero N] where
  frequencies : Finset (ZMod N)
  radius : ℝ
  radius_nonneg : 0 ≤ radius

namespace Set

noncomputable def carrier (B : Set N) : Finset (ZMod N) :=
  Finset.univ.filter fun x ↦
    ∀ r ∈ B.frequencies, ‖1 - character r x‖ ≤ B.radius

instance : Membership (ZMod N) (Set N) := ⟨fun B x ↦ x ∈ B.carrier⟩

@[simp] lemma mem_carrier {B : Set N} {x : ZMod N} :
    x ∈ B.carrier ↔
      ∀ r ∈ B.frequencies, ‖1 - character r x‖ ≤ B.radius := by
  simp [carrier]

lemma mem_iff {B : Set N} {x : ZMod N} :
    x ∈ B ↔ ∀ r ∈ B.frequencies, ‖1 - character r x‖ ≤ B.radius :=
  mem_carrier

def rank (B : Set N) : ℕ := B.frequencies.card

def dilate (ρ : ℝ) (B : Set N) : Set N where
  frequencies := B.frequencies
  radius := |ρ| * B.radius
  radius_nonneg := mul_nonneg (abs_nonneg _) B.radius_nonneg

def ofFrequencies (Γ : Finset (ZMod N)) (ρ : ℝ) (hρ : 0 ≤ ρ) : Set N where
  frequencies := Γ
  radius := ρ
  radius_nonneg := hρ

def meet (B C : Set N) : Set N where
  frequencies := B.frequencies ∪ C.frequencies
  radius := min B.radius C.radius
  radius_nonneg := le_min B.radius_nonneg C.radius_nonneg

@[simp] lemma frequencies_ofFrequencies (Γ : Finset (ZMod N)) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (ofFrequencies Γ ρ hρ).frequencies = Γ := rfl

@[simp] lemma radius_ofFrequencies (Γ : Finset (ZMod N)) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (ofFrequencies Γ ρ hρ).radius = ρ := rfl

@[simp] lemma rank_ofFrequencies (Γ : Finset (ZMod N)) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (ofFrequencies Γ ρ hρ).rank = Γ.card := rfl

@[simp] lemma frequencies_meet (B C : Set N) :
    (B.meet C).frequencies = B.frequencies ∪ C.frequencies := rfl

@[simp] lemma radius_meet (B C : Set N) :
    (B.meet C).radius = min B.radius C.radius := rfl

lemma rank_meet_le (B C : Set N) : (B.meet C).rank ≤ B.rank + C.rank := by
  exact Finset.card_union_le _ _

@[simp] lemma frequencies_dilate (ρ : ℝ) (B : Set N) :
    (B.dilate ρ).frequencies = B.frequencies := rfl

@[simp] lemma radius_dilate (ρ : ℝ) (B : Set N) :
    (B.dilate ρ).radius = |ρ| * B.radius := rfl

@[simp] lemma rank_dilate (ρ : ℝ) (B : Set N) :
    (B.dilate ρ).rank = B.rank := rfl

@[simp] lemma zero_mem (B : Set N) : (0 : ZMod N) ∈ B := by
  rw [mem_iff]
  intro r hr
  simp [B.radius_nonneg]

lemma carrier_nonempty (B : Set N) : B.carrier.Nonempty :=
  ⟨0, B.zero_mem⟩

lemma card_pos (B : Set N) : 0 < B.carrier.card :=
  Finset.card_pos.mpr B.carrier_nonempty

lemma neg_mem_iff (B : Set N) (x : ZMod N) : -x ∈ B ↔ x ∈ B := by
  rw [mem_iff, mem_iff]
  have hnorm (z : ℂ) : ‖1 - (starRingEnd ℂ) z‖ = ‖1 - z‖ := by
    simpa using (RCLike.norm_conj (1 - z))
  constructor
  · intro h r hr
    have hr' := h r hr
    rw [AddChar.map_neg_eq_conj, hnorm] at hr'
    exact hr'
  · intro h r hr
    rw [AddChar.map_neg_eq_conj, hnorm]
    exact h r hr

lemma add_mem_of_mem {B₁ B₂ B₃ : Set N}
    (hfreq₁ : B₃.frequencies ⊆ B₁.frequencies)
    (hfreq₂ : B₃.frequencies ⊆ B₂.frequencies)
    (hradius : B₁.radius + B₂.radius ≤ B₃.radius)
    {x y : ZMod N} (hx : x ∈ B₁) (hy : y ∈ B₂) : x + y ∈ B₃ := by
  rw [mem_iff] at hx hy ⊢
  intro r hr
  calc
    ‖1 - character r (x + y)‖ =
        ‖1 - character r x * character r y‖ := by rw [character_add]
    _ ≤ ‖1 - character r x‖ + ‖1 - character r y‖ :=
      norm_one_sub_mul_of_norm_le_one (by rw [norm_character])
    _ ≤ B₁.radius + B₂.radius := add_le_add (hx r (hfreq₁ hr)) (hy r (hfreq₂ hr))
    _ ≤ B₃.radius := hradius

lemma add_mem_dilate {B : Set N} {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    {x y : ZMod N} (hx : x ∈ B.dilate ρ) (hy : y ∈ B.dilate σ) :
    x + y ∈ B.dilate (ρ + σ) := by
  apply add_mem_of_mem (B₁ := B.dilate ρ) (B₂ := B.dilate σ)
      (B₃ := B.dilate (ρ + σ))
  · simp
  · simp
  · simp [abs_of_nonneg hρ, abs_of_nonneg hσ, abs_of_nonneg (add_nonneg hρ hσ), add_mul]
  · exact hx
  · exact hy

lemma sub_mem_dilate {B : Set N} {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    {x y : ZMod N} (hx : x ∈ B.dilate ρ) (hy : y ∈ B.dilate σ) :
    x - y ∈ B.dilate (ρ + σ) := by
  rw [sub_eq_add_neg]
  apply add_mem_dilate hρ hσ hx
  exact (B.dilate σ).neg_mem_iff y |>.2 hy

lemma carrier_mono {B₁ B₂ : Set N} (hfreq : B₂.frequencies ⊆ B₁.frequencies)
    (hradius : B₁.radius ≤ B₂.radius) : B₁.carrier ⊆ B₂.carrier := by
  intro x hx
  rw [mem_carrier] at hx ⊢
  intro r hr
  exact (hx r (hfreq hr)).trans hradius

lemma carrier_meet_subset_left (B C : Set N) : (B.meet C).carrier ⊆ B.carrier := by
  apply carrier_mono
  · exact Finset.subset_union_left
  · exact min_le_left _ _

lemma carrier_meet_subset_right (B C : Set N) : (B.meet C).carrier ⊆ C.carrier := by
  apply carrier_mono
  · exact Finset.subset_union_right
  · exact min_le_right _ _

lemma dilate_mono (B : Set N) {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hρσ : ρ ≤ σ) :
    (B.dilate ρ).carrier ⊆ (B.dilate σ).carrier := by
  apply carrier_mono
  · simp
  · have hσ : 0 ≤ σ := hρ.trans hρσ
    simp only [radius_dilate, ge_iff_le]
    rw [abs_of_nonneg hρ, abs_of_nonneg hσ]
    exact mul_le_mul_of_nonneg_right hρσ B.radius_nonneg

@[simp] lemma dilate_one (B : Set N) : B.dilate 1 = B := by
  cases B
  simp [dilate]

@[simp] lemma dilate_dilate (B : Set N) (s t : ℝ) :
    (B.dilate s).dilate t = B.dilate (t * s) := by
  cases B
  simp [dilate, abs_mul, mul_assoc]

end Set
end CyclicBohr
end Erdos3

end

section

namespace Erdos3

open AddChar Finset
open scoped BigOperators

namespace CyclicBohr

variable {N : ℕ} [NeZero N]

lemma norm_sub_le_abs_arg_sub_of_norm_eq_one {z w : ℂ}
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    ‖z - w‖ ≤ |z.arg - w.arg| := by
  have hzexp : Complex.exp (z.arg * Complex.I) = z := by
    calc
      Complex.exp (z.arg * Complex.I) =
          ‖z‖ * Complex.exp (z.arg * Complex.I) := by simp [hz]
      _ = z := Complex.norm_mul_exp_arg_mul_I z
  have hwexp : Complex.exp (w.arg * Complex.I) = w := by
    calc
      Complex.exp (w.arg * Complex.I) =
          ‖w‖ * Complex.exp (w.arg * Complex.I) := by simp [hw]
      _ = w := Complex.norm_mul_exp_arg_mul_I w
  calc
    ‖z - w‖ =
        ‖Complex.exp (z.arg * Complex.I) - Complex.exp (w.arg * Complex.I)‖ := by
      rw [hzexp, hwexp]
    _ =
        ‖Complex.exp (w.arg * Complex.I) *
          (Complex.exp ((z.arg - w.arg) * Complex.I) - 1)‖ := by
      congr 1
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      ring
    _ = ‖Complex.exp ((z.arg - w.arg) * Complex.I) - 1‖ := by
      rw [norm_mul, Complex.norm_exp]
      simp
    _ ≤ |z.arg - w.arg| := by
      simpa [mul_comm, Real.norm_eq_abs] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := z.arg - w.arg))

noncomputable def scaledArg (m : ℕ) (z : ℂ) : ℝ :=
  (z.arg + Real.pi) * m / (2 * Real.pi)

lemma norm_one_sub_character_sub (r x y : ZMod N) :
    ‖1 - character r (x - y)‖ = ‖character r x - character r y‖ := by
  have hy : character r y ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [norm_character]; norm_num)
  rw [AddChar.map_sub_eq_div, one_sub_div hy, norm_div, norm_character]
  simp [norm_sub_rev]

lemma abs_arg_character_le_two_radius (B : Set N) {x r : ZMod N}
    (hx : x ∈ B) (hr : r ∈ B.frequencies) :
    |(character r x).arg| ≤ 2 * B.radius := by
  have hnorm := Set.mem_iff.mp hx r hr
  have hangle := Complex.angle_le_mul_norm_sub
    (norm_character r x) (by norm_num : ‖(1 : ℂ)‖ = 1)
  calc
    |(character r x).arg| = InnerProductGeometry.angle (character r x) 1 :=
      (Complex.angle_one_right (norm_ne_zero_iff.mp (by
        rw [norm_character]
        norm_num))).symm
    _ ≤ Real.pi / 2 * ‖character r x - 1‖ := hangle
    _ = Real.pi / 2 * ‖1 - character r x‖ := by rw [norm_sub_rev]
    _ ≤ Real.pi / 2 * B.radius :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ ≤ 2 * B.radius := by
      apply mul_le_mul_of_nonneg_right _ B.radius_nonneg
      linarith [Real.pi_lt_four]

noncomputable def localScaledArg (B : Set N) (z : ℂ) : ℝ :=
  2 * (z.arg + 2 * B.radius) / B.radius

lemma localScaledArg_nonneg (B : Set N) {x r : ZMod N}
    (hB : 0 < B.radius) (hx : x ∈ B) (hr : r ∈ B.frequencies) :
    0 ≤ localScaledArg B (character r x) := by
  have harg := abs_arg_character_le_two_radius B hx hr
  rw [abs_le] at harg
  unfold localScaledArg
  have hsum : 0 ≤ (character r x).arg + 2 * B.radius := by linarith [harg.1]
  exact div_nonneg (mul_nonneg (by norm_num) hsum) hB.le

lemma localScaledArg_le_eight (B : Set N) {x r : ZMod N}
    (hB : 0 < B.radius) (hx : x ∈ B) (hr : r ∈ B.frequencies) :
    localScaledArg B (character r x) ≤ 8 := by
  have harg := abs_arg_character_le_two_radius B hx hr
  rw [abs_le] at harg
  unfold localScaledArg
  rw [div_le_iff₀ hB]
  linarith

noncomputable def localArgBin (B : Set N) (hB : 0 < B.radius)
    (x : ↥B.carrier) (r : ↥B.frequencies) : Fin 9 :=
  ⟨⌊localScaledArg B (character r.1 x.1)⌋₊, by
    rw [Nat.floor_lt' (by norm_num : (9 : ℕ) ≠ 0)]
    exact (localScaledArg_le_eight B hB x.2 r.2).trans_lt (by norm_num)⟩

noncomputable def localArgumentCode (B : Set N) (hB : 0 < B.radius)
    (x : ↥B.carrier) : (r : ↥B.frequencies) → Fin 9 :=
  fun r ↦ localArgBin B hB x r

@[simp] lemma card_localArgumentCodeSpace (B : Set N) :
    Fintype.card ((r : ↥B.frequencies) → Fin 9) = 9 ^ B.rank := by
  simp [Set.rank]

lemma abs_localScaledArg_sub_lt_one_of_localArgBin_eq
    (B : Set N) (hB : 0 < B.radius) {x y : ↥B.carrier}
    {r : ↥B.frequencies}
    (hbin : localArgBin B hB x r = localArgBin B hB y r) :
    |localScaledArg B (character r.1 x.1) -
      localScaledArg B (character r.1 y.1)| < 1 := by
  have hfloor :
      ⌊localScaledArg B (character r.1 x.1)⌋₊ =
        ⌊localScaledArg B (character r.1 y.1)⌋₊ :=
    congrArg Fin.val hbin
  have hfloorR :
      (⌊localScaledArg B (character r.1 x.1)⌋₊ : ℝ) =
        ⌊localScaledArg B (character r.1 y.1)⌋₊ := by
    exact_mod_cast hfloor
  have hxlow :
      (⌊localScaledArg B (character r.1 x.1)⌋₊ : ℝ) ≤
        localScaledArg B (character r.1 x.1) :=
    Nat.floor_le (localScaledArg_nonneg B hB x.2 r.2)
  have hylow :
      (⌊localScaledArg B (character r.1 y.1)⌋₊ : ℝ) ≤
        localScaledArg B (character r.1 y.1) :=
    Nat.floor_le (localScaledArg_nonneg B hB y.2 r.2)
  have hxup := Nat.lt_floor_add_one
    (localScaledArg B (character r.1 x.1))
  have hyup := Nat.lt_floor_add_one
    (localScaledArg B (character r.1 y.1))
  rw [abs_lt]
  constructor <;> nlinarith

lemma abs_arg_sub_lt_half_radius_of_localArgBin_eq
    (B : Set N) (hB : 0 < B.radius) {x y : ↥B.carrier}
    {r : ↥B.frequencies}
    (hbin : localArgBin B hB x r = localArgBin B hB y r) :
    |(character r.1 x.1).arg - (character r.1 y.1).arg| < B.radius / 2 := by
  have h := abs_localScaledArg_sub_lt_one_of_localArgBin_eq B hB hbin
  have hscale :
      |localScaledArg B (character r.1 x.1) -
        localScaledArg B (character r.1 y.1)| =
      2 * |(character r.1 x.1).arg - (character r.1 y.1).arg| / B.radius := by
    have heq :
        localScaledArg B (character r.1 x.1) -
          localScaledArg B (character r.1 y.1) =
        2 * ((character r.1 x.1).arg - (character r.1 y.1).arg) /
          B.radius := by
      unfold localScaledArg
      ring
    rw [heq, abs_div, abs_mul, abs_of_pos hB]
    norm_num
  rw [hscale] at h
  rw [div_lt_iff₀ hB] at h
  linarith

lemma sub_mem_half_dilate_of_localArgumentCode_eq
    (B : Set N) (hB : 0 < B.radius) {x y : ↥B.carrier}
    (hcode : localArgumentCode B hB x = localArgumentCode B hB y) :
    x.1 - y.1 ∈ B.dilate (1 / 2 : ℝ) := by
  rw [Set.mem_iff]
  intro r hr
  have hbin : localArgBin B hB x ⟨r, hr⟩ =
      localArgBin B hB y ⟨r, hr⟩ := congrFun hcode ⟨r, hr⟩
  calc
    ‖1 - character r (x.1 - y.1)‖ =
        ‖character r x.1 - character r y.1‖ :=
      norm_one_sub_character_sub r x.1 y.1
    _ ≤ |(character r x.1).arg - (character r y.1).arg| :=
      norm_sub_le_abs_arg_sub_of_norm_eq_one
        (norm_character r x.1) (norm_character r y.1)
    _ ≤ B.radius / 2 :=
      (abs_arg_sub_lt_half_radius_of_localArgBin_eq B hB hbin).le
    _ = (B.dilate (1 / 2 : ℝ)).radius := by
      simp [div_eq_mul_inv, mul_comm]

theorem card_carrier_le_nine_pow_rank_mul_card_half
    (B : Set N) (hB : 0 < B.radius) :
    B.carrier.card ≤ 9 ^ B.rank * (B.dilate (1 / 2 : ℝ)).carrier.card := by
  let Q := (r : ↥B.frequencies) → Fin 9
  let code : ↥B.carrier → Q := localArgumentCode B hB
  have hQ : Fintype.card Q = 9 ^ B.rank := by
    simpa [Q] using card_localArgumentCodeSpace B
  have hmain : Fintype.card ↥B.carrier ≤
      Fintype.card Q * (B.dilate (1 / 2 : ℝ)).carrier.card := by
    by_contra hbound
    rw [not_le] at hbound
    obtain ⟨q, hq⟩ :=
      Fintype.exists_lt_card_fiber_of_mul_lt_card (f := code) hbound
    let S : Finset ↥B.carrier := Finset.univ.filter fun x ↦ code x = q
    have hScard : (B.dilate (1 / 2 : ℝ)).carrier.card < S.card := by
      simpa [S] using hq
    have hSnonempty : S.Nonempty := Finset.card_pos.mp
      (lt_of_le_of_lt (Nat.zero_le _) hScard)
    obtain ⟨x₀, hx₀⟩ := hSnonempty
    let e : ↥B.carrier ↪ ZMod N :=
      ⟨fun x ↦ x.1 - x₀.1, by
        intro x y hxy
        apply Subtype.ext
        exact (Equiv.subRight x₀.1).injective hxy⟩
    have hmap : S.map e ⊆ (B.dilate (1 / 2 : ℝ)).carrier := by
      intro z hz
      rw [Finset.mem_map] at hz
      obtain ⟨x, hxS, rfl⟩ := hz
      have hcodex : code x = q := by simpa [S] using hxS
      have hcodex₀ : code x₀ = q := by simpa [S] using hx₀
      exact sub_mem_half_dilate_of_localArgumentCode_eq B hB
        (hcodex.trans hcodex₀.symm)
    have hle : S.card ≤ (B.dilate (1 / 2 : ℝ)).carrier.card := by
      calc
        S.card = (S.map e).card := (Finset.card_map e).symm
        _ ≤ (B.dilate (1 / 2 : ℝ)).carrier.card := Finset.card_le_card hmap
    omega
  rw [hQ] at hmain
  have hcardcoe : Fintype.card ↥B.carrier = B.carrier.card :=
    Fintype.card_coe B.carrier
  rw [hcardcoe] at hmain
  exact hmain

end CyclicBohr
end Erdos3

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators

variable {N : ℕ} [NeZero N]

lemma norm_one_sub_prod_le_sum {ι : Type*}
    (s : Finset ι) (f : ι → ℂ) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ‖1 - ∏ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖1 - f i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact (norm_one_sub_mul_of_norm_le_one (hf a (by simp))).trans
        (add_le_add le_rfl (ih fun i hi ↦ hf i (by simp [hi])))

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr

lemma character_eq_one_mul {N : ℕ} [NeZero N] (r x : ZMod N) :
    character r x = character 1 (r * x) := by
  change (↑(AddChar.zmod N r x) : ℂ) = ↑(AddChar.zmod N 1 (r * x))
  simp [AddChar.zmod]

lemma norm_one_sub_character_intCast {N : ℕ} [NeZero N] (t : ℤ) :
    ‖1 - character 1 (t : ZMod N)‖ ≤ 8 * |(t : ℝ)| / N := by
  change ‖1 - (↑(AddChar.zmod N 1 (t : ZMod N)) : ℂ)‖ ≤ _
  rw [show (1 : ZMod N) = ((1 : ℤ) : ZMod N) by simp]
  rw [AddChar.zmod_intCast, Circle.coe_exp, norm_sub_rev]
  simp only [Int.cast_one, one_mul]
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hnorm : ‖Complex.exp ((2 * Real.pi * ((t : ℝ) / N) : ℝ) *
      Complex.I) - 1‖ ≤ |2 * Real.pi * ((t : ℝ) / N)| := by
    simpa only [mul_comm, Real.norm_eq_abs]
      using (Real.norm_exp_I_mul_ofReal_sub_one_le
        (x := 2 * Real.pi * ((t : ℝ) / N)))
  refine hnorm.trans ?_
  rw [← mul_div_assoc, abs_div, abs_mul, abs_mul, abs_of_pos hN,
    abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  gcongr
  linarith [Real.pi_le_four]

lemma norm_one_sub_character_le_of_mul_eq_intCast {N : ℕ} [NeZero N]
    (r x : ZMod N) (t : ℤ) (h : r * x = (t : ZMod N)) :
    ‖1 - character r x‖ ≤ 8 * |(t : ℝ)| / N := by
  rw [character_eq_one_mul, h]
  exact norm_one_sub_character_intCast t

end Erdos3.CyclicBohr

end

section

namespace Erdos3.CyclicBohr

open Finset
open scoped BigOperators

variable {N : ℕ} [NeZero N]

theorem card_two_le_nine_pow_three_rank_mul_card_quarter (B : Set N) (hB : 0 < B.radius) :
    (B.dilate 2).carrier.card ≤ 9 ^ (3 * B.rank) * (B.dilate (1 / 4)).carrier.card := by
  have h₂ := card_carrier_le_nine_pow_rank_mul_card_half (B.dilate 2)
    (show 0 < (B.dilate 2).radius by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hB)
  have h₁ := card_carrier_le_nine_pow_rank_mul_card_half B hB
  have hh := card_carrier_le_nine_pow_rank_mul_card_half (B.dilate (1 / 2))
    (show 0 < (B.dilate (1 / 2)).radius by simpa using mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hB)
  simp only [Set.rank_dilate, Set.dilate_dilate] at h₂ hh
  norm_num at h₂ hh
  calc
    _ ≤ 9 ^ B.rank * B.carrier.card := h₂
    _ ≤ 9 ^ B.rank * (9 ^ B.rank * (B.dilate (1 / 2)).carrier.card) := Nat.mul_le_mul_left _ h₁
    _ ≤ 9 ^ B.rank * (9 ^ B.rank * (9 ^ B.rank * (B.dilate (1 / 4)).carrier.card)) := by
      gcongr
    _ = _ := by
      rw [← mul_assoc, ← pow_add, ← mul_assoc, ← pow_add]
      congr 2
      omega

end Erdos3.CyclicBohr

end

section

namespace Erdos3.CyclicBohr

variable {N : ℕ} [NeZero N]

theorem card_le_dyadic_dilate (B : Set N) (hB : 0 < B.radius) (k : ℕ) :
    B.carrier.card ≤ 9 ^ (k * B.rank) * (B.dilate ((1 / 2 : ℝ) ^ k)).carrier.card := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpos : 0 < (B.dilate ((1 / 2 : ℝ) ^ k)).radius := by
      simp only [Set.radius_dilate, abs_of_nonneg (pow_nonneg (by norm_num) _)]
      positivity
    have hh := card_carrier_le_nine_pow_rank_mul_card_half (B.dilate ((1 / 2 : ℝ) ^ k)) hpos
    have heq : (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k = (1 / 2 : ℝ) ^ (k + 1) := by
      rw [pow_succ, mul_comm]
    simp only [Set.rank_dilate, Set.dilate_dilate, heq] at hh
    calc
      _ ≤ 9 ^ (k * B.rank) * (B.dilate ((1 / 2 : ℝ) ^ k)).carrier.card := ih
      _ ≤ 9 ^ (k * B.rank) *
          (9 ^ B.rank * (B.dilate ((1 / 2 : ℝ) ^ (k + 1))).carrier.card) := Nat.mul_le_mul_left _ hh
      _ = _ := by simp only [Nat.add_mul, Nat.one_mul, pow_add, mul_assoc]

theorem relative_card_lower_bound (B : Set N) (hB : 0 < B.radius)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (r / 2) ^ (4 * B.rank) * (B.carrier.card : ℝ) ≤ (B.dilate r).carrier.card := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one hr hr1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  let k := n + 1
  have hk : (1 / 2 : ℝ) ^ k ≤ r := hn.le
  have hhalf : r / 2 ≤ (1 / 2 : ℝ) ^ k := by
    dsimp [k]
    rw [pow_succ]
    nlinarith
  have hd := card_le_dyadic_dilate B hB k
  have hdR : (B.carrier.card : ℝ) ≤
      (9 : ℝ) ^ (k * B.rank) * (B.dilate ((1 / 2 : ℝ) ^ k)).carrier.card := by exact_mod_cast hd
  have hcoef : ((1 / 2 : ℝ) ^ k) ^ (4 * B.rank) * 9 ^ (k * B.rank) ≤ 1 := by
    calc
      _ = ((1 / 2 : ℝ) ^ 4) ^ (k * B.rank) * 9 ^ (k * B.rank) := by
        congr 1
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring
      _ = ((1 / 2 : ℝ) ^ 4 * 9) ^ (k * B.rank) := (mul_pow _ _ _).symm
      _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc
    _ ≤ ((1 / 2 : ℝ) ^ k) ^ (4 * B.rank) * B.carrier.card :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hhalf _) (Nat.cast_nonneg _)
    _ ≤ ((1 / 2 : ℝ) ^ k) ^ (4 * B.rank) *
        (9 ^ (k * B.rank) * (B.dilate ((1 / 2 : ℝ) ^ k)).carrier.card) :=
      mul_le_mul_of_nonneg_left hdR (by positivity)
    _ ≤ 1 * ((B.dilate ((1 / 2 : ℝ) ^ k)).carrier.card : ℝ) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
    _ ≤ (B.dilate r).carrier.card := by
      rw [one_mul]
      exact_mod_cast Finset.card_le_card (B.dilate_mono (pow_nonneg (by norm_num) _) hk)

end Erdos3.CyclicBohr

end

section

namespace Erdos3.CyclicBohr.Set

end Erdos3.CyclicBohr.Set

end

end OAI

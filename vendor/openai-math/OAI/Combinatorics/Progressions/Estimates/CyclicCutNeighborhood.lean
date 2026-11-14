/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/CyclicCutNeighborhood.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Equiv.Prod
public import OAI.Combinatorics.Progressions.Estimates.BooleanCubeProduct
public import OAI.Combinatorics.Progressions.Estimates.FiniteConvolution
public import OAI.Combinatorics.Progressions.Lattices.IntegerAbsInterval
@[expose] public section

namespace OAI

section

namespace Erdos3

theorem exists_smoothing_scale {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ K : ℕ, 0 < K ∧ K ≤ N ∧ ((K - 1 : ℕ) : ℝ) ≤ δ * N ∧
      (N : ℝ) / K ≤ 2 / δ := by
  let K := max 1 ⌊δ * N⌋₊
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hfloor : (⌊δ * N⌋₊ : ℝ) ≤ δ * N := Nat.floor_le (by positivity)
  have hfloorN : ⌊δ * N⌋₊ ≤ N := by
    exact_mod_cast hfloor.trans (by nlinarith : δ * N ≤ (N : ℝ))
  have hk : 1 ≤ K := le_max_left _ _
  have hkfloor : ⌊δ * N⌋₊ ≤ K := le_max_right _ _
  have hk1 : (1 : ℝ) ≤ K := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < K := by linarith
  have hfK : (⌊δ * N⌋₊ : ℝ) ≤ K := by exact_mod_cast hkfloor
  have hlt : δ * N < (⌊δ * N⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨K, by omega, max_le (by omega) hfloorN, ?_, ?_⟩
  · have hh : K - 1 ≤ ⌊δ * N⌋₊ := by dsimp [K]; omega
    exact (Nat.cast_le.mpr hh).trans hfloor
  · apply (div_le_div_iff₀ hkpos hδ).mpr
    nlinarith

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

def finiteIndicator (I : Finset H) (x : H) : ℂ := if x ∈ I then 1 else 0

noncomputable def averagingKernel (B : Finset H) (x : H) : ℂ :=
  (Fintype.card H : ℂ) / B.card * finiteIndicator B x

noncomputable def smoothedIndicator (I B : Finset H) (x : H) : ℂ :=
  𝔼 h ∈ B, finiteIndicator I (x - h)

omit [AddCommGroup H] [Fintype H] in
theorem finiteIndicator_norm_le_one (I : Finset H) (x : H) : ‖finiteIndicator I x‖ ≤ 1 := by
  simp only [finiteIndicator]
  split_ifs <;> norm_num

omit [Fintype H] in
theorem smoothedIndicator_norm_le_one (I : Finset H) {B : Finset H} (hB : B.Nonempty) (x : H) :
    ‖smoothedIndicator I B x‖ ≤ 1 := by
  exact (RCLike.norm_expect_le (K := ℂ)).trans
    ((Finset.expect_le_expect (fun h _ => finiteIndicator_norm_le_one I (x - h))).trans_eq
      (Finset.expect_const hB 1))

theorem smoothedIndicator_eq_convolution (I B : Finset H) (x : H) :
    smoothedIndicator I B x = finiteConvolution (averagingKernel B) (finiteIndicator I) x := by
  have hn : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (fun h => averagingKernel B h * finiteIndicator I (x - h)) =
      (fun h => ((Fintype.card H : ℂ) / B.card) * restrictTo B (fun h => finiteIndicator I (x - h)) h) := by
    funext h
    by_cases hh : h ∈ B <;> simp [averagingKernel, finiteIndicator, restrictTo, hh]
  rw [finiteConvolution, he, ← Finset.mul_expect, expect_restrictTo,
    smoothedIndicator, Finset.expect_eq_sum_div_card]
  by_cases hb : (B.card : ℂ) = 0
  · simp [hb]
  · field_simp

omit [AddCommGroup H] in
theorem mean_indicator_norm_sq (I : Finset H) :
    (𝔼 x, ‖finiteIndicator I x‖ ^ 2) = (I.card : ℝ) / Fintype.card H := by
  have he (x : H) : ‖finiteIndicator I x‖ ^ 2 = if x ∈ I then (1 : ℝ) else 0 := by
    by_cases hx : x ∈ I <;> simp [finiteIndicator, hx]
  simp only [he, Fintype.expect_eq_sum_div_card]
  simp

theorem mean_averagingKernel_norm_sq {B : Finset H} (hB : B.Nonempty) :
    (𝔼 x, ‖averagingKernel B x‖ ^ 2) = (Fintype.card H : ℝ) / B.card := by
  have hn : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hb : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  simp only [averagingKernel, norm_mul, norm_div, Complex.norm_natCast, mul_pow]
  rw [← Finset.mul_expect, mean_indicator_norm_sq]
  field_simp

theorem smoothedIndicator_fourier_mass {B : Finset H} (hB : B.Nonempty) (I : Finset H) :
    (∑ χ : AddChar H ℂ, ‖finiteFourierCoeff (averagingKernel B) χ * finiteFourierCoeff (finiteIndicator I) χ‖) ≤
      (Fintype.card H : ℝ) / B.card := by
  let M := ∑ χ : AddChar H ℂ,
    ‖finiteFourierCoeff (averagingKernel B) χ * finiteFourierCoeff (finiteIndicator I) χ‖
  have hn : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hb : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hm : M ^ 2 ≤ (I.card : ℝ) / B.card := by
    have hh := finiteConvolution_fourier_mass_sq (averagingKernel B) (finiteIndicator I)
    rw [mean_averagingKernel_norm_sq hB, mean_indicator_norm_sq] at hh
    calc
      _ ≤ ((Fintype.card H : ℝ) / B.card) * ((I.card : ℝ) / Fintype.card H) := hh
      _ = _ := by field_simp
  have hi : (I.card : ℝ) ≤ Fintype.card H := by exact_mod_cast Finset.card_le_univ I
  have hbr : (B.card : ℝ) ≤ Fintype.card H := by exact_mod_cast Finset.card_le_univ B
  have hR : (1 : ℝ) ≤ (Fintype.card H : ℝ) / B.card := (le_div_iff₀ hb).mpr (by simpa using hbr)
  have hm' := hm.trans (div_le_div_of_nonneg_right hi hb.le)
  change M ≤ _
  nlinarith [sq_nonneg ((Fintype.card H : ℝ) / B.card - 1)]

end Erdos3

end

section

open scoped BigOperators symmDiff

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

omit [AddCommGroup H] in
theorem mean_finiteIndicator_difference (I J : Finset H) :
    (𝔼 x, ‖finiteIndicator I x - finiteIndicator J x‖) =
      ((I ∆ J).card : ℝ) / Fintype.card H := by
  have he (x : H) : ‖finiteIndicator I x - finiteIndicator J x‖ =
      if x ∈ I ∆ J then (1 : ℝ) else 0 := by
    by_cases hi : x ∈ I <;> by_cases hj : x ∈ J <;>
      simp [finiteIndicator, Finset.mem_symmDiff, hi, hj]
  simp only [he, Fintype.expect_eq_sum_div_card]
  simp

theorem mean_indicator_smoothing_error (I : Finset H) {B : Finset H} (hB : B.Nonempty)
    {ε : ℝ} (hshift : ∀ h ∈ B, (𝔼 x, ‖finiteIndicator I x - finiteIndicator I (x - h)‖) ≤ ε) :
    (𝔼 x, ‖finiteIndicator I x - smoothedIndicator I B x‖) ≤ ε := by
  have hpoint (x : H) : ‖finiteIndicator I x - smoothedIndicator I B x‖ ≤
      𝔼 h ∈ B, ‖finiteIndicator I x - finiteIndicator I (x - h)‖ := by
    have he : finiteIndicator I x - smoothedIndicator I B x =
        𝔼 h ∈ B, (finiteIndicator I x - finiteIndicator I (x - h)) := by
      rw [Finset.expect_sub_distrib, Finset.expect_const hB]
      rfl
    rw [he]
    exact RCLike.norm_expect_le (K := ℂ)
  calc
    _ ≤ 𝔼 x, 𝔼 h ∈ B, ‖finiteIndicator I x - finiteIndicator I (x - h)‖ :=
      Finset.expect_le_expect (fun x _ => hpoint x)
    _ = 𝔼 h ∈ B, 𝔼 x, ‖finiteIndicator I x - finiteIndicator I (x - h)‖ := Finset.expect_comm _ _ _
    _ ≤ 𝔼 _h ∈ B, ε := Finset.expect_le_expect hshift
    _ = ε := Finset.expect_const hB ε

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {H K : Type*} [AddCommGroup H] [Fintype H]
    [AddCommGroup K] [Fintype K] [DecidableEq K]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem finiteCorrelation_mul_indicator (I : Finset H) (f u : H → ℂ) :
    finiteCorrelation Finset.univ f (fun x => u x * finiteIndicator I x) =
      ((I.card : ℂ) / Fintype.card H) * finiteCorrelation I f u := by
  have he : (fun x => f x * star (u x * finiteIndicator I x)) =
      restrictTo I (fun x => f x * star (u x)) := by
    funext x
    by_cases hx : x ∈ I <;> simp [finiteIndicator, restrictTo, hx]
  unfold finiteCorrelation
  rw [he, expect_restrictTo, Finset.expect_eq_sum_div_card]
  by_cases hI : I.card = 0
  · simp [Finset.card_eq_zero.mp hI]
  · have hi : (I.card : ℂ) ≠ 0 := by exact_mod_cast hI
    have hn : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp

theorem norm_finiteCorrelation_mul_indicator (I : Finset H) (f u : H → ℂ) :
    ‖finiteCorrelation Finset.univ f (fun x => u x * finiteIndicator I x)‖ =
      ((I.card : ℝ) / Fintype.card H) * ‖finiteCorrelation I f u‖ := by
  rw [finiteCorrelation_mul_indicator, norm_mul, norm_div]
  simp only [Complex.norm_natCast]

theorem retained_restricted_correlation (I : Finset H) (f u : H → ℂ)
    {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B)
    (hf : ∀ x ∈ I, ‖f x‖ ≤ 1) (hu : ∀ x ∈ I, ‖u x‖ ≤ B)
    (hc : ρ ≤ ‖finiteCorrelation Finset.univ f (fun x => u x * finiteIndicator I x)‖) :
    I.Nonempty ∧ ρ ≤ ‖finiteCorrelation I f u‖ ∧
      ρ / B ≤ (I.card : ℝ) / Fintype.card H := by
  rw [norm_finiteCorrelation_mul_indicator] at hc
  have hI : I.Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty.mp he] at hc
    simp only [Finset.card_empty, Nat.cast_zero, zero_div, zero_mul] at hc
    linarith
  have hv0 : 0 ≤ (I.card : ℝ) / Fintype.card H := by positivity
  have hv1 : (I.card : ℝ) / Fintype.card H ≤ 1 := by
    apply (div_le_one (by exact_mod_cast Fintype.card_pos)).mpr
    exact_mod_cast Finset.card_le_univ I
  have hb := norm_finiteCorrelation_le hI f u hf hu
  refine ⟨hI, hc.trans ?_, (div_le_iff₀ hB).mpr ?_⟩
  · exact (mul_le_mul_of_nonneg_right hv1 (norm_nonneg _)).trans_eq (one_mul _)
  · exact hc.trans (mul_le_mul_of_nonneg_left hb hv0)

end Erdos3

end

section

open scoped BigOperators symmDiff

namespace Erdos3

variable {N : ℕ}

def cyclicInterval (a : ZMod N) (L : ℕ) : Finset (ZMod N) :=
  (Finset.range L).image (fun k : ℕ => a + (k : ZMod N))

theorem mem_cyclicInterval_shift (a t x : ZMod N) (L : ℕ) :
    x - t ∈ cyclicInterval a L ↔ x ∈ cyclicInterval (a + t) L := by
  simp only [cyclicInterval, Finset.mem_image]
  constructor
  · rintro ⟨k, hk, he⟩
    refine ⟨k, hk, ?_⟩
    calc
      a + t + k = (a + k) + t := by ring
      _ = x := by rw [he]; ring
  · rintro ⟨k, hk, he⟩
    refine ⟨k, hk, ?_⟩
    rw [← he]
    ring

theorem cyclicInterval_sdiff_next (a : ZMod N) (L : ℕ) :
    cyclicInterval a L \ cyclicInterval (a + 1) L ⊆ {a} := by
  intro x hx
  obtain ⟨hx, hn⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
  have hk' := Finset.mem_range.mp hk
  cases k with
  | zero => simp
  | succ k =>
    exfalso
    apply hn
    refine Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), ?_⟩
    push_cast
    ring

theorem cyclicInterval_next_sdiff (a : ZMod N) (L : ℕ) :
    cyclicInterval (a + 1) L \ cyclicInterval a L ⊆ {a + L} := by
  intro x hx
  obtain ⟨hx, hn⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
  have hk' := Finset.mem_range.mp hk
  by_cases hnext : k + 1 < L
  · exfalso
    apply hn
    refine Finset.mem_image.mpr ⟨k + 1, Finset.mem_range.mpr hnext, ?_⟩
    push_cast
    ring
  · have he : L = k + 1 := by omega
    apply Finset.mem_singleton.mpr
    rw [he]
    push_cast
    ring

theorem card_cyclicInterval_symmDiff_next (a : ZMod N) (L : ℕ) :
    (cyclicInterval a L ∆ cyclicInterval (a + 1) L).card ≤ 2 := by
  rw [Finset.symmDiff_def]
  calc
    _ ≤ (cyclicInterval a L \ cyclicInterval (a + 1) L).card +
        (cyclicInterval (a + 1) L \ cyclicInterval a L).card := Finset.card_union_le _ _
    _ ≤ ({a} : Finset (ZMod N)).card + ({a + L} : Finset (ZMod N)).card :=
      Nat.add_le_add (Finset.card_le_card (cyclicInterval_sdiff_next a L))
        (Finset.card_le_card (cyclicInterval_next_sdiff a L))
    _ = 2 := by simp

theorem cyclicInterval_unit_shift_error [NeZero N] (a : ZMod N) (L : ℕ) :
    (𝔼 x, ‖finiteIndicator (cyclicInterval a L) x - finiteIndicator (cyclicInterval a L) (x - 1)‖) ≤
      2 / (N : ℝ) := by
  have he (x : ZMod N) : finiteIndicator (cyclicInterval a L) (x - 1) =
      finiteIndicator (cyclicInterval (a + 1) L) x := by
    simp only [finiteIndicator, mem_cyclicInterval_shift]
  simp only [he]
  rw [mean_finiteIndicator_difference, ZMod.card]
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_cyclicInterval_symmDiff_next a L) (Nat.cast_nonneg N)

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem cyclicInterval_card (a : ZMod N) {L : ℕ} (hL : L ≤ N) :
    (cyclicInterval a L).card = L := by
  unfold cyclicInterval
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj he
  have hiN : i < N := (Finset.mem_range.mp hi).trans_le hL
  have hjN : j < N := (Finset.mem_range.mp hj).trans_le hL
  have hc : (i : ZMod N) = (j : ZMod N) := add_left_cancel he
  have hv := congrArg ZMod.val hc
  simpa only [ZMod.val_natCast_of_lt hiN, ZMod.val_natCast_of_lt hjN] using hv

omit [NeZero N] in
theorem cyclicInterval_nonempty (a : ZMod N) {L : ℕ} (hL : 0 < L) :
    (cyclicInterval a L).Nonempty := by
  refine ⟨a, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hL, ?_⟩⟩
  simp

theorem cyclicInterval_nat_shift_error (a : ZMod N) (L h : ℕ) :
    (𝔼 x, ‖finiteIndicator (cyclicInterval a L) x - finiteIndicator (cyclicInterval a L) (x - h)‖) ≤
      2 * (h : ℝ) / N := by
  let u := finiteIndicator (cyclicInterval a L)
  induction h with
  | zero => simp
  | succ h ih =>
    have he (x : ZMod N) : x - ((h + 1 : ℕ) : ZMod N) = (x - h) - 1 := by
      push_cast
      ring
    have ht : (𝔼 x, ‖u (x - h) - u ((x - h) - 1)‖) = 𝔼 x, ‖u x - u (x - 1)‖ := by
      simpa only [sub_eq_add_neg] using
        (Fintype.expect_equiv (Equiv.addRight (-(h : ZMod N)))
          (fun x => ‖u (x + -(h : ZMod N)) - u ((x + -(h : ZMod N)) - 1)‖)
          (fun x => ‖u x - u (x - 1)‖) (fun _ => rfl))
    change (𝔼 x, ‖u x - u (x - ((h + 1 : ℕ) : ZMod N))‖) ≤ _
    calc
      _ ≤ (𝔼 x, ‖u x - u (x - h)‖) + (𝔼 x, ‖u (x - h) - u ((x - h) - 1)‖) := by
        rw [← Finset.expect_add_distrib]
        apply Finset.expect_le_expect
        intro x _
        rw [he]
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * (h : ℝ) / N + 2 / N := by
        rw [ht]
        exact add_le_add ih (cyclicInterval_unit_shift_error a L)
      _ = _ := by push_cast; ring

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {N : ℕ} [NeZero N]

end Erdos3

end

section

namespace Erdos3

variable {N : ℕ} [NeZero N]

theorem mem_cyclicInterval_representatives (a b : ℕ) (hab : a ≤ b) (hbN : b ≤ N) (x : ZMod N) :
    x ∈ cyclicInterval (a : ZMod N) (b - a) ↔ a ≤ x.val ∧ x.val < b := by
  constructor
  · intro hx
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hx
    have hk' := Finset.mem_range.mp hk
    have hak : a + k < b := by omega
    have he' : ((a + k : ℕ) : ZMod N) = x := by simpa only [Nat.cast_add] using he
    rw [← he', ZMod.val_natCast_of_lt (hak.trans_le hbN)]
    omega
  · intro hx
    refine Finset.mem_image.mpr ⟨x.val - a, Finset.mem_range.mpr (by omega), ?_⟩
    have he : a + (x.val - a) = x.val := Nat.add_sub_of_le hx.1
    calc
      (a : ZMod N) + (x.val - a : ℕ) = ((a + (x.val - a) : ℕ) : ZMod N) := by push_cast; rfl
      _ = x := by rw [he, ZMod.natCast_zmod_val]

end Erdos3

end

section

namespace Erdos3

variable {N : ℕ} [NeZero N]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

variable (N : I → ℕ) [∀ i, NeZero (N i)]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

def quarterLower (N : ℕ) (i : Fin 4) : ℕ := i.val * N / 4

def quarterUpper (N : ℕ) (i : Fin 4) : ℕ := (i.val + 1) * N / 4

def cyclicQuarter (N : ℕ) (i : Fin 4) : Finset (ZMod N) :=
  cyclicInterval (quarterLower N i : ZMod N) (quarterUpper N i - quarterLower N i)

theorem quarter_bounds (N : ℕ) (i : Fin 4) :
    quarterLower N i ≤ quarterUpper N i ∧ quarterUpper N i ≤ N := by
  fin_cases i <;> simp only [quarterLower, quarterUpper] <;> omega

theorem quarter_short (N : ℕ) (hN : 0 < N) (i : Fin 4) :
    2 * ((quarterUpper N i : ℤ) - quarterLower N i - 1) < N := by
  fin_cases i <;> simp only [quarterLower, quarterUpper] <;> omega

theorem quarter_diameter_lt_third (N : ℕ) (hN : 0 < N) (i : Fin 4) :
    3 * ((quarterUpper N i : ℤ) - quarterLower N i - 1) < N := by
  fin_cases i <;> simp only [quarterLower, quarterUpper] <;> omega

theorem mem_cyclicQuarter {N : ℕ} [NeZero N] (i : Fin 4) (x : ZMod N) :
    x ∈ cyclicQuarter N i ↔ quarterLower N i ≤ x.val ∧ x.val < quarterUpper N i :=
  mem_cyclicInterval_representatives _ _ (quarter_bounds N i).1 (quarter_bounds N i).2 x

theorem sum_cyclicQuarter_indicator {N : ℕ} [NeZero N] (x : ZMod N) :
    (∑ i : Fin 4, finiteIndicator (cyclicQuarter N i) x) = 1 := by
  have hx := x.val_lt
  simp only [finiteIndicator, mem_cyclicQuarter, Fin.sum_univ_succ, Fin.sum_univ_zero,
    quarterLower, quarterUpper, Fin.val_zero, Fin.val_succ, add_zero]
  split_ifs <;> norm_num at * <;> omega

end Erdos3

end

section

namespace Erdos3

def cyclicTranslationOffset {N : ℕ} (h : ZMod N) (a : ℕ) : ℤ :=
  (h.val : ℤ) - if N - h.val ≤ a then (N : ℤ) else 0

theorem cyclic_representative_add {N : ℕ} [NeZero N] (h x : ZMod N) :
    ((h + x).val : ℤ) = (x.val : ℤ) + h.val -
      if N - h.val ≤ x.val then (N : ℤ) else 0 := by
  have hh := h.val_lt
  by_cases hw : N - h.val ≤ x.val
  · have he := ZMod.val_add_val_of_le (a := h) (b := x) (by omega)
    rw [ite_eq_left hw]
    omega
  · have he := ZMod.val_add_of_lt (a := h) (b := x) (by omega)
    rw [ite_eq_right hw]
    omega

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (N : I → ℕ) [∀ i, NeZero (N i)]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

noncomputable def cyclicCutNeighborhood (N : ℕ) [NeZero N] (a : ℤ) (δ : ℝ) : Finset (ZMod N) := by
  classical
  exact Finset.univ.filter (fun x => |(x.val : ℝ) - a| ≤ δ)

theorem mem_cyclicCutNeighborhood (N : ℕ) [NeZero N] (a : ℤ) (δ : ℝ) (x : ZMod N) :
    x ∈ cyclicCutNeighborhood N a δ ↔ |(x.val : ℝ) - a| ≤ δ := by
  classical
  simp only [cyclicCutNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and]

theorem cyclicCutNeighborhood_card_le (N : ℕ) [NeZero N] (a : ℤ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((cyclicCutNeighborhood N a δ).card : ℝ) ≤ 2 * δ + 1 := by
  have hcard : (cyclicCutNeighborhood N a δ).card ≤ (integerAbsInterval δ).card := by
    apply Finset.card_le_card_of_injOn (fun x : ZMod N => (x.val : ℤ) - a)
    · intro x hx
      change (x.val : ℤ) - a ∈ integerAbsInterval δ
      rw [mem_integerAbsInterval]
      simpa only [Int.cast_sub, Int.cast_natCast] using (mem_cyclicCutNeighborhood N a δ x).mp hx
    · intro x _ y _ hxy
      apply ZMod.val_injective N
      have hv : (x.val : ℤ) = (y.val : ℤ) := by dsimp only at hxy; omega
      exact_mod_cast hv
  exact (Nat.cast_le.mpr hcard).trans (integerAbsInterval_card_le δ hδ)

end Erdos3

end

end OAI

module

public import PrimeCarleson.Proof.Paper.P9.Dense
public import PrimeCarleson.Proof.Paper.P2.Variation

/-!
# Reduction to intervals `J` of length `ℓ = c Q^{-2}`

Source: main paper `p:global-shell-var`, L1960–L1969 (the split inequality `e:split`, see
`P2/Variation.lean`, and the single-`λ` terms).

`split_reduction`: let `ρ ≥ 2`, `ℓ > 0`, `M ≥ 1/ℓ`, `a : ℤ → ℝ → ℂ` a family (`a x λ = T^Q_λ f(x)`).
Assume the **local bound** `‖V^ρ(a_·(x) : T')‖_{ℓ²_x} ≤ L` for every finite `T' ⊂ [0, 1)` contained
in an interval `[u, u + ℓ]`, and the **single-`λ` bound** `‖a_λ‖_{ℓ²} ≤ L'` for `λ ∈ [0, 1)`. Then
for every finite `T ⊂ [0, 1)`

`‖V^ρ(a_·(x) : T)‖_{ℓ²_x} ≤ 3 √M L + 2 √M L'`.

The partition of `T` is by `⌊t/ℓ⌋`; the nonempty pieces `T_m` give intervals `[min T_m, max T_m]`
with right endpoints in `T`, and `e:split` (`split_inequality_norm`) applies; the `ℓ^ρ` sums are
bounded by `ℓ²` sums (`ρ ≥ 2`) and exchanged with the `ℓ²_x` norm.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common

/-- `((∑ y^ρ)^{1/ρ})² ≤ ∑ y²` for `ρ ≥ 2` (`ℓ^ρ ≤ ℓ²`). -/
theorem sq_sum_rpow_le {ι : Type*} (S : Finset ι) (y : ι → ℝ≥0∞) {ρ : ℝ} (hρ : 2 ≤ ρ) :
    ((∑ n ∈ S, y n ^ ρ) ^ (1 / ρ)) ^ 2 ≤ ∑ n ∈ S, y n ^ 2 := by
  have h := sum_rpow_rpow_anti_exponent S (by norm_num : (0 : ℝ) < 2) hρ y
  have h2 : ∀ n, y n ^ (2 : ℝ) = y n ^ 2 := fun n => ENNReal.rpow_two (y n)
  simp_rw [h2] at h
  calc ((∑ n ∈ S, y n ^ ρ) ^ (1 / ρ)) ^ 2 ≤ ((∑ n ∈ S, y n ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = ∑ n ∈ S, y n ^ 2 := enorm_rpow_half_sq _

/-- The `ℓ²_x` norm of an `ℓ^ρ` sum of `N` sequences each of `ℓ²` norm at most `L` is at most
`√N L`. -/
theorem tsum_sq_sum_rpow_le {N : ℕ} (y : Fin N → ℤ → ℝ≥0∞) {ρ : ℝ} (hρ : 2 ≤ ρ) {L : ℝ≥0∞}
    (hL : ∀ n, (∑' x : ℤ, y n x ^ 2) ^ (1 / 2 : ℝ) ≤ L) :
    (∑' x : ℤ, ((∑ n : Fin N, y n x ^ ρ) ^ (1 / ρ)) ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt N) * L := by
  have h1 : ∑' x : ℤ, ((∑ n : Fin N, y n x ^ ρ) ^ (1 / ρ)) ^ 2 ≤
      ∑' x : ℤ, ∑ n : Fin N, y n x ^ 2 :=
    ENNReal.tsum_le_tsum fun x => sq_sum_rpow_le _ _ hρ
  have h2 : ∑' x : ℤ, ∑ n : Fin N, y n x ^ 2 = ∑ n : Fin N, ∑' x : ℤ, y n x ^ 2 :=
    Summable.tsum_finsetSum fun n _ => ENNReal.summable
  have h3 : ∀ n, ∑' x : ℤ, y n x ^ 2 ≤ L ^ 2 := by
    intro n
    calc ∑' x : ℤ, y n x ^ 2 = ((∑' x : ℤ, y n x ^ 2) ^ (1 / 2 : ℝ)) ^ 2 :=
          (enorm_rpow_half_sq _).symm
      _ ≤ L ^ 2 := by gcongr; exact hL n
  have h4 : ∑ n : Fin N, ∑' x : ℤ, y n x ^ 2 ≤ (N : ℝ≥0∞) * L ^ 2 := by
    calc ∑ n : Fin N, ∑' x : ℤ, y n x ^ 2 ≤ ∑ _n : Fin N, L ^ 2 :=
          Finset.sum_le_sum fun n _ => h3 n
      _ = (N : ℝ≥0∞) * L ^ 2 := by simp
  calc (∑' x : ℤ, ((∑ n : Fin N, y n x ^ ρ) ^ (1 / ρ)) ^ 2) ^ (1 / 2 : ℝ)
      ≤ ((N : ℝ≥0∞) * L ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (h1.trans (h2 ▸ h4)) (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt N) * L := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), enorm_sq_rpow_half]
        congr 1
        rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _)
          (by norm_num), Real.sqrt_eq_rpow]

/-- `(∑ (c f)²)^{1/2} = c (∑ f²)^{1/2}`. -/
theorem tsum_sq_const_mul (c : ℝ≥0∞) (f : ℤ → ℝ≥0∞) :
    (∑' x : ℤ, (c * f x) ^ 2) ^ (1 / 2 : ℝ) = c * (∑' x : ℤ, f x ^ 2) ^ (1 / 2 : ℝ) := by
  simp_rw [mul_pow]
  rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), enorm_sq_rpow_half]

/-- **The reduction to intervals** (Source: main paper `p:global-shell-var`, L1960–L1969): see the
module docstring. -/
theorem split_reduction {ρ : ℝ} (hρ : 2 ≤ ρ) {ℓ : ℝ} (hℓ : 0 < ℓ) {M : ℕ} (hM : 1 / ℓ ≤ M)
    (a : ℤ → ℝ → ℂ) {L L' : ℝ≥0∞}
    (hL : ∀ (u : ℝ) (T' : Set ℝ), T'.Finite → T' ⊆ Set.Ico 0 1 → T' ⊆ Set.Icc u (u + ℓ) →
      (∑' x : ℤ, rVariationOn ρ T' (a x) ^ 2) ^ (1 / 2 : ℝ) ≤ L)
    (hL' : ∀ t ∈ Set.Ico (0 : ℝ) 1, (∑' x : ℤ, ‖a x t‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤ L')
    {T : Set ℝ} (hT : T.Finite) (hT01 : T ⊆ Set.Ico 0 1) :
    (∑' x : ℤ, rVariationOn ρ T (a x) ^ 2) ^ (1 / 2 : ℝ) ≤
      3 * (ENNReal.ofReal (Real.sqrt M) * L) + 2 * (ENNReal.ofReal (Real.sqrt M) * L') := by
  classical
  have hρ1 : 1 ≤ ρ := by linarith
  set Tf : Finset ℝ := hT.toFinset with hTf
  have hTmem : ∀ t, t ∈ Tf ↔ t ∈ T := fun t => hT.mem_toFinset
  set idx : ℝ → ℕ := fun t => ⌊t / ℓ⌋₊ with hidx
  set P : Finset ℕ := Tf.image idx with hP
  have hPM : P ⊆ Finset.range M := by
    intro m hm
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hm
    have ht' := hT01 ((hTmem t).1 ht)
    rw [Finset.mem_range, hidx]
    simp only
    refine (Nat.floor_lt (div_nonneg ht'.1 hℓ.le)).2 ?_
    calc t / ℓ < 1 / ℓ := by gcongr; exact ht'.2
      _ ≤ M := hM
  have hNM : P.card ≤ M := by simpa using Finset.card_le_card hPM
  let p : Fin P.card ↪o ℕ := P.orderEmbOfFin rfl
  have hpP : ∀ n, p n ∈ P := fun n => P.orderEmbOfFin_mem rfl n
  have hpsurj : ∀ m ∈ P, ∃ n, p n = m := by
    intro m hm
    have : m ∈ Set.range p := by
      rw [show Set.range p = (P : Set ℕ) from P.range_orderEmbOfFin rfl]
      exact hm
    exact this
  let piece : ℕ → Finset ℝ := fun m => Tf.filter fun t => idx t = m
  have hne : ∀ n, (piece (p n)).Nonempty := by
    intro n
    obtain ⟨t, ht, h⟩ := Finset.mem_image.1 (hpP n)
    exact ⟨t, Finset.mem_filter.2 ⟨ht, h⟩⟩
  let A : Fin P.card → ℝ := fun n => (piece (p n)).min' (hne n)
  let B : Fin P.card → ℝ := fun n => (piece (p n)).max' (hne n)
  have hAmem : ∀ n, A n ∈ piece (p n) := fun n => Finset.min'_mem _ _
  have hBmem : ∀ n, B n ∈ piece (p n) := fun n => Finset.max'_mem _ _
  have hAB : ∀ n, A n ≤ B n := fun n => Finset.min'_le _ _ (hBmem n)
  have hidxA : ∀ n, idx (A n) = p n := fun n => (Finset.mem_filter.1 (hAmem n)).2
  have hidxB : ∀ n, idx (B n) = p n := fun n => (Finset.mem_filter.1 (hBmem n)).2
  have hBT : ∀ n, B n ∈ T := fun n => (hTmem _).1 (Finset.mem_filter.1 (hBmem n)).1
  have hpiece : ∀ n, T ∩ Set.Icc (A n) (B n) = ↑(piece (p n)) := by
    intro n
    ext t
    constructor
    · rintro ⟨htT, hA, hB'⟩
      have h1 : idx (A n) ≤ idx t := Nat.floor_le_floor (by gcongr)
      have h2 : idx t ≤ idx (B n) := Nat.floor_le_floor (by gcongr)
      rw [hidxA] at h1
      rw [hidxB] at h2
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨(hTmem t).2 htT, le_antisymm h2 h1⟩)
    · intro ht
      obtain ⟨htT, _⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 ht)
      exact ⟨(hTmem t).1 htT, Finset.min'_le _ _ (Finset.mem_coe.1 ht),
        Finset.le_max' _ _ (Finset.mem_coe.1 ht)⟩
  have hJ : T ⊆ ⋃ n, Set.Icc (A n) (B n) := by
    intro t ht
    obtain ⟨n, hn⟩ := hpsurj (idx t) (Finset.mem_image_of_mem idx ((hTmem t).2 ht))
    have : t ∈ T ∩ Set.Icc (A n) (B n) := by
      rw [hpiece n, hn]
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨(hTmem t).2 ht, rfl⟩)
    exact Set.mem_iUnion.2 ⟨n, this.2⟩
  have hdisj : Pairwise fun n n' =>
      Disjoint (T ∩ Set.Icc (A n) (B n)) (T ∩ Set.Icc (A n') (B n')) := by
    intro n n' hne
    rw [hpiece n, hpiece n', Set.disjoint_left]
    intro t h1 h2
    have e1 := (Finset.mem_filter.1 (Finset.mem_coe.1 h1)).2
    have e2 := (Finset.mem_filter.1 (Finset.mem_coe.1 h2)).2
    exact hne (p.injective (e1.symm.trans e2))
  have hsplit : ∀ x : ℤ, rVariationOn ρ T (a x) ≤
      3 * (∑ n, rVariationOn ρ (T ∩ Set.Icc (A n) (B n)) (a x) ^ ρ) ^ (1 / ρ) +
        2 * (∑ n, ‖a x (B n)‖ₑ ^ ρ) ^ (1 / ρ) := fun x =>
    split_inequality_norm hρ1 A B T hAB hBT hJ hdisj (a x)
  have hy : ∀ n, (∑' x : ℤ, rVariationOn ρ (T ∩ Set.Icc (A n) (B n)) (a x) ^ 2) ^
      (1 / 2 : ℝ) ≤ L := by
    intro n
    refine hL (p n * ℓ) _ (hT.subset Set.inter_subset_left)
      (Set.inter_subset_left.trans hT01) ?_
    rw [hpiece n]
    intro t ht
    obtain ⟨htT, hid⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 ht)
    have ht0 : 0 ≤ t / ℓ := div_nonneg (hT01 ((hTmem t).1 htT)).1 hℓ.le
    have h1 : (p n : ℝ) ≤ t / ℓ := by rw [← hid]; exact Nat.floor_le ht0
    have h2 : t / ℓ < p n + 1 := by rw [← hid]; exact Nat.lt_floor_add_one _
    constructor
    · calc (p n : ℝ) * ℓ ≤ t / ℓ * ℓ := by gcongr
        _ = t := div_mul_cancel₀ _ hℓ.ne'
    · have : t < (p n + 1) * ℓ := by rwa [div_lt_iff₀ hℓ] at h2
      linarith
  have hz : ∀ n, (∑' x : ℤ, ‖a x (B n)‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤ L' := fun n =>
    hL' _ (hT01 (hBT n))
  have hU := tsum_sq_sum_rpow_le (fun n x => rVariationOn ρ (T ∩ Set.Icc (A n) (B n)) (a x)) hρ hy
  have hW := tsum_sq_sum_rpow_le (fun n x => ‖a x (B n)‖ₑ) hρ hz
  have hsqrt : ENNReal.ofReal (Real.sqrt P.card) ≤ ENNReal.ofReal (Real.sqrt M) :=
    ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (by exact_mod_cast hNM))
  calc (∑' x : ℤ, rVariationOn ρ T (a x) ^ 2) ^ (1 / 2 : ℝ)
      ≤ (∑' x : ℤ, (3 * (∑ n, rVariationOn ρ (T ∩ Set.Icc (A n) (B n)) (a x) ^ ρ) ^ (1 / ρ) +
          2 * (∑ n, ‖a x (B n)‖ₑ ^ ρ) ^ (1 / ρ)) ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum fun x => by gcongr; exact hsplit x)
          (by norm_num)
    _ ≤ (∑' x : ℤ, (3 * (∑ n, rVariationOn ρ (T ∩ Set.Icc (A n) (B n)) (a x) ^ ρ) ^ (1 / ρ)) ^ 2)
          ^ (1 / 2 : ℝ) + (∑' x : ℤ, (2 * (∑ n, ‖a x (B n)‖ₑ ^ ρ) ^ (1 / ρ)) ^ 2) ^ (1 / 2 : ℝ) :=
        tsum_sq_add_le _ _
    _ = 3 * (∑' x : ℤ, ((∑ n, rVariationOn ρ (T ∩ Set.Icc (A n) (B n)) (a x) ^ ρ) ^ (1 / ρ)) ^ 2)
          ^ (1 / 2 : ℝ) +
        2 * (∑' x : ℤ, ((∑ n, ‖a x (B n)‖ₑ ^ ρ) ^ (1 / ρ)) ^ 2) ^ (1 / 2 : ℝ) := by
        rw [tsum_sq_const_mul, tsum_sq_const_mul]
    _ ≤ 3 * (ENNReal.ofReal (Real.sqrt P.card) * L) +
          2 * (ENNReal.ofReal (Real.sqrt P.card) * L') := by gcongr
    _ ≤ _ := by gcongr

end PrimeCarleson.Proof.Paper

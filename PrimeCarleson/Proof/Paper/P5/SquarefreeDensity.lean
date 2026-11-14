module

public import PrimeCarleson.Proof.Paper.P5.BlocksExist
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Density of the squarefree integers in `(Q/2, Q]`

The paper's block partition (`e:kappa`, L2083-L2086) needs about `Q^κ` squarefree integers in
`(Q/2, Q]`. `card_sqfreeSet_ge`: `Q ≤ 24 · #{squarefree n ∈ (Q/2, Q]}` for `Q = 2^j`.

Proof for `Q ≥ 144`: an `n ∈ (Q/2, Q]` that is not squarefree is divisible by some `m²`,
`2 ≤ m ≤ ⌊√Q⌋`; there are at most `Q/(2 m²) + 1` multiples of `m²` in `(Q/2, Q]` and
`∑_{m ≥ 2} m^{-2} ≤ 2/3` (telescoping `m^{-2} ≤ 2/(2m-1) - 2/(2m+1)`), so at most
`Q/3 + √Q ≤ 5Q/12` integers are not squarefree and at least `Q/12` are. For `Q < 144` the
finitely many cases are checked by kernel computation.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

/-- `∑_{m=2}^{M+1} m^{-2} ≤ 2/3 - 2/(2M+3)`. -/
theorem sum_inv_sq_le (M : ℕ) :
    ∑ m ∈ Finset.Icc 2 (M + 1), (1 : ℝ) / (m : ℝ) ^ 2 ≤ 2 / 3 - 2 / (2 * ((M : ℝ) + 1) + 1) := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [show M + 1 + 1 = (M + 1) + 1 by rfl, Finset.sum_Icc_succ_top (by omega)]
    have h1 : (1 : ℝ) / ((M + 1 + 1 : ℕ) : ℝ) ^ 2 ≤
        2 / (2 * ((M : ℝ) + 1) + 1) - 2 / (2 * (((M + 1 : ℕ) : ℝ) + 1) + 1) := by
      push_cast
      have h2 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      have e : (2 : ℝ) / (2 * ((M : ℝ) + 1) + 1) - 2 / (2 * (((M : ℝ) + 1) + 1) + 1) =
          4 / ((2 * ((M : ℝ) + 1) + 1) * (2 * (((M : ℝ) + 1) + 1) + 1)) := by
        field_simp
        ring
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (M : ℝ)]
    linarith

theorem sum_inv_sq_le_two_thirds (M : ℕ) :
    ∑ m ∈ Finset.Icc 2 M, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 2 / 3 := by
  rcases M with _ | M
  · norm_num
  · have := sum_inv_sq_le M
    have h2 : (0 : ℝ) ≤ 2 / (2 * ((M : ℝ) + 1) + 1) := by positivity
    linarith

/-- The number of multiples of `m²` in `(Q/2, Q]` is at most `Q/(2m²) + 1` (`Q = 2H`). -/
theorem card_mult_le (H m : ℕ) (hm : 0 < m * m) :
    (((Finset.Ioc H (2 * H)).filter (fun n => m * m ∣ n)).card : ℝ) ≤
      (2 * H : ℝ) / (2 * ((m : ℝ) * m)) + 1 := by
  have hunion : (Finset.Ioc 0 (2 * H)).filter (fun n => m * m ∣ n) =
      (Finset.Ioc 0 H).filter (fun n => m * m ∣ n) ∪
        (Finset.Ioc H (2 * H)).filter (fun n => m * m ∣ n) := by
    rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le H) (by omega)]
  have hdisj : Disjoint ((Finset.Ioc 0 H).filter (fun n => m * m ∣ n))
      ((Finset.Ioc H (2 * H)).filter (fun n => m * m ∣ n)) := by
    refine Finset.disjoint_filter_filter ?_
    exact Finset.disjoint_left.2 fun x hx hy => by
      rw [Finset.mem_Ioc] at hx hy
      omega
  have hcard := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisj, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.Ioc_filter_dvd_card_eq_div] at hcard
  have hmR : (0 : ℝ) < (m : ℝ) * m := by exact_mod_cast hm
  have h1 : ((2 * H) / (m * m) : ℕ) ≤ (2 * H : ℝ) / ((m : ℝ) * m) := by
    have := Nat.floor_le (show (0 : ℝ) ≤ ((2 * H : ℕ) : ℝ) / (((m * m : ℕ)) : ℝ) by positivity)
    rw [Nat.floor_div_eq_div] at this
    push_cast at this
    exact this
  have h2 : (H : ℝ) / ((m : ℝ) * m) < ((H / (m * m) : ℕ) : ℝ) + 1 := by
    have := Nat.lt_floor_add_one (((H : ℕ) : ℝ) / (((m * m : ℕ)) : ℝ))
    rw [Nat.floor_div_eq_div] at this
    push_cast at this
    exact this
  have h3 : (((Finset.Ioc H (2 * H)).filter (fun n => m * m ∣ n)).card : ℝ) =
      (((2 * H) / (m * m) : ℕ) : ℝ) - ((H / (m * m) : ℕ) : ℝ) := by
    have : ((H / (m * m) : ℕ) : ℝ) +
        (((Finset.Ioc H (2 * H)).filter (fun n => m * m ∣ n)).card : ℝ) =
        (((2 * H) / (m * m) : ℕ) : ℝ) := by exact_mod_cast hcard.symm
    linarith
  rw [h3]
  have h4 : (2 * H : ℝ) / (2 * ((m : ℝ) * m)) = (H : ℝ) / ((m : ℝ) * m) := by
    field_simp
  rw [h4]
  have h5 : (2 * H : ℝ) / ((m : ℝ) * m) = 2 * ((H : ℝ) / ((m : ℝ) * m)) := by
    field_simp
  linarith

/-- At most `Q/3 + √Q` integers in `(Q/2, Q]` are not squarefree (`Q = 2H`, `H ≥ 1`). -/
theorem card_nonsqfree_le (H : ℕ) :
    ((((Finset.Ioc H (2 * H)).filter (fun n => ¬ Squarefree n)).card : ℕ) : ℝ) ≤
      (2 * H : ℝ) / 3 + (Nat.sqrt (2 * H) : ℝ) := by
  classical
  set M : ℕ := Nat.sqrt (2 * H) with hM
  set T : Finset ℕ := Finset.Ioc H (2 * H) with hT
  have hsub : T.filter (fun n => ¬ Squarefree n) ⊆
      (Finset.Icc 2 M).biUnion (fun m => T.filter (fun n => m * m ∣ n)) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnT, hns⟩ := hn
    have hnT' := Finset.mem_Ioc.1 hnT
    have hn0 : n ≠ 0 := by omega
    unfold Squarefree at hns
    push Not at hns
    obtain ⟨x, hxn, hxu⟩ := hns
    have hx1 : x ≠ 1 := fun h => hxu (by simp [h])
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hn0 (zero_dvd_iff.1 (by simpa using hxn))
    rw [Finset.mem_biUnion]
    refine ⟨x, Finset.mem_Icc.2 ⟨by omega, ?_⟩, Finset.mem_filter.2 ⟨hnT, hxn⟩⟩
    rw [hM, Nat.le_sqrt]
    exact (Nat.le_of_dvd (by omega) hxn).trans hnT'.2
  calc ((((T.filter (fun n => ¬ Squarefree n)).card : ℕ)) : ℝ)
      ≤ (((Finset.Icc 2 M).biUnion (fun m => T.filter (fun n => m * m ∣ n))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((∑ m ∈ Finset.Icc 2 M, (T.filter (fun n => m * m ∣ n)).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ m ∈ Finset.Icc 2 M, ((H : ℝ) * (1 / (m : ℝ) ^ 2) + 1) := by
        push_cast
        refine Finset.sum_le_sum fun m hm => ?_
        have hm2 : 2 ≤ m := (Finset.mem_Icc.1 hm).1
        have h := card_mult_le H m (by nlinarith)
        have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
        refine h.trans (le_of_eq ?_)
        field_simp
    _ = (H : ℝ) * ∑ m ∈ Finset.Icc 2 M, (1 / (m : ℝ) ^ 2) + ((Finset.Icc 2 M).card : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
    _ ≤ (2 * H : ℝ) / 3 + M := by
        have h1 := sum_inv_sq_le_two_thirds M
        have h2 : ((Finset.Icc 2 M).card : ℝ) ≤ M := by
          rw [Nat.card_Icc]
          have : M + 1 - 2 ≤ M := by omega
          exact_mod_cast this
        have h3 : (H : ℝ) * ∑ m ∈ Finset.Icc 2 M, (1 / (m : ℝ) ^ 2) ≤ (H : ℝ) * (2 / 3) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg H)
        linarith

/-- **Density of the squarefree integers in `(Q/2, Q]`**: `Q ≤ 24 · #{squarefree n ∈ (Q/2, Q]}`,
`Q = 2^j`. -/
theorem card_sqfreeSet_ge (j : ℕ) : (2 : ℝ) ^ j ≤ 24 * ((sqfreeSet j).card : ℝ) := by
  by_cases hj : j ≤ 7
  · have h : 2 ^ j ≤ 24 * (sqfreeSet j).card := by
      interval_cases j <;> unfold sqfreeSet <;> decide +kernel
    exact_mod_cast h
  · push Not at hj
    obtain ⟨H, hH⟩ : ∃ H : ℕ, 2 ^ j = 2 * H := ⟨2 ^ (j - 1), by
      rw [← pow_succ']
      congr 1
      omega⟩
    have hH2 : 2 ^ j / 2 = H := by omega
    have hQ : (2 : ℝ) ^ j = 2 * H := by exact_mod_cast hH
    have hQ144 : (144 : ℝ) ≤ 2 * H := by
      rw [← hQ]
      calc (144 : ℝ) ≤ 2 ^ 8 := by norm_num
        _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
    have hcard : (sqfreeSet j).card +
        ((Finset.Ioc H (2 * H)).filter (fun n => ¬ Squarefree n)).card = H := by
      have := Finset.card_filter_add_card_filter_not (s := Finset.Ioc H (2 * H))
        (fun n => Squarefree n)
      rw [Nat.card_Ioc] at this
      unfold sqfreeSet
      have h2H : 2 * H / 2 = H := by omega
      rw [hH, h2H]
      have h3 : 2 * H - H = H := by omega
      rw [h3] at this
      exact this
    have hN := card_nonsqfree_le H
    have hMsq : ((Nat.sqrt (2 * H) : ℕ) : ℝ) ^ 2 ≤ 2 * H := by
      have := Nat.sqrt_le' (2 * H)
      exact_mod_cast this
    have hM12 : ((Nat.sqrt (2 * H) : ℕ) : ℝ) ≤ (2 * H) / 12 := by
      have hM0 : (0 : ℝ) ≤ (Nat.sqrt (2 * H) : ℕ) := Nat.cast_nonneg _
      by_contra hcon
      push Not at hcon
      nlinarith
    have hS : ((sqfreeSet j).card : ℝ) + (((Finset.Ioc H (2 * H)).filter
        (fun n => ¬ Squarefree n)).card : ℝ) = H := by exact_mod_cast hcard
    rw [hQ]
    linarith

end PrimeCarleson.Proof.Paper

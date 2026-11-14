module

public import PrimeCarleson.Proof.Common.Variation
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Variation norms on dyadic grids and the Jones–Seeger–Wright split inequality

Two inequalities of `sources/Variational_Carleson.tex` that the paper quotes from the literature,
proved here for the `PrimeCarleson.rVariationOn`, with absolute constants.

* Rademacher–Menshov for the `2`-variation (paper L906-L922, lemma `l:RMvariation`, quoted from
  the literature; used in the proof of `l:crudeV2lambda`, L1024-L1042):
  - `rVariationOn_two_le_sum_dyadic`: for every `J`, every progression `x₀ + h j` with `0 < h`
    and every `a : ℝ → ℂ`,
    `V²(a : {x₀ + h j : 0 ≤ j ≤ 2^J}) ≤ 2 ∑_{m=0}^J S_m(a)`,
    `S_m(a)² = ∑_{s < 2^{J-m}} |a(x₀ + h (s+1) 2^m) - a(x₀ + h s 2^m)|²`;
  - `rVariationOn_two_le_sum_dyadic_grid`: the case `x₀ = 0`, `h = 2^{-J}` (the dyadic grid
    `{j / 2^J}`) in the form `S_m(a)² = ∑_{s < K} |a((s+1)/K) - a(s/K)|²`, `K = 2^{J-m}`.
  The proof telescopes `a` along the dyadic scales (the martingale differences `b_m - b_{m+1}`),
  bounds the squared increments of the level-`m` difference along a chain by `4 S_m²`, and uses
  Minkowski over the scales (`rVariationOn_sum_le`).
* Jones–Seeger–Wright split inequality (paper L898-L904, display `e:split`, quoted from the
  literature; used in the proof of `e:embed`, L1110-L1115):
  - `rVariationOn_iUnion_le`: for ordered blocks `Jₙ` (`n < n'` implies `Jₙ < Jₙ'`) with one
    reference point `pₙ ∈ Jₙ` each,
    `V^r(a : ⋃ Jₙ) ≤ 3 (∑ₙ V^r(a : Jₙ)^r)^{1/r} + V^r(a_{pₙ} : n)` for `1 ≤ r`;
  - `rVariationOn_range_le`: `V^r(a_{pₙ} : n) ≤ 2 (∑ₙ |a(pₙ)|^r)^{1/r}` (second line of `e:split`);
  - `rVariationOn_iUnion_le_norm`: the combination of the two;
  - `rVariationOn_split_Icc`: the printed form
    `Jₙ = J ∩ [Aₙ, Bₙ]` with the right endpoints `Bₙ ∈ J` as reference points.
  The key tool is `sum_le_rVariationOn_rpow`: the `r`-th power sum of the increments of a monotone
  sequence over any set of steps whose endpoints lie in `S` is at most `V^r(S)^r`; the split
  follows from the decomposition of a step between two blocks into three pieces and Minkowski
  in `ℓ^r`, for an absolute constant independent of `r`.

All statements are in `ℝ≥0∞`; no finiteness hypothesis is needed.
-/

@[expose] public noncomputable section

open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Common

open PrimeCarleson PrimeCarleson.Proof.MswTransference

/-- A finite chain `t₀, …, t_K`, extended to a `ℕ`-indexed sequence that is constant after the
last point. -/
private def extendChain {α : Type*} {K : ℕ} (t : Fin (K + 1) → α) (i : ℕ) : α :=
  t ⟨min i K, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The extension agrees with the chain at the points `0, …, K - 1`. -/
private theorem extendChain_castSucc {α : Type*} {K : ℕ} (t : Fin (K + 1) → α) (i : Fin K) :
    extendChain t i = t i.castSucc := by
  unfold extendChain
  congr 1
  ext
  simp

/-- The extension agrees with the chain at the points `1, …, K`. -/
private theorem extendChain_succ {α : Type*} {K : ℕ} (t : Fin (K + 1) → α) (i : Fin K) :
    extendChain t (i + 1) = t i.succ := by
  unfold extendChain
  congr 1
  ext
  simp

/-- The extension of a monotone chain is monotone. -/
private theorem monotone_extendChain {α : Type*} [Preorder α] {K : ℕ} {t : Fin (K + 1) → α}
    (ht : Monotone t) : Monotone (extendChain t) := by
  intro i j hij
  refine ht ?_
  simp only [Fin.le_def]
  exact min_le_min_right _ hij

/-- A sum over the steps of a chain, as a sum over `Finset.range K` of the extension. -/
private theorem sum_fin_eq_sum_range_extendChain {α : Type*} {K : ℕ} (t : Fin (K + 1) → α)
    (F : α → α → ℝ≥0∞) :
    ∑ i : Fin K, F (t i.castSucc) (t i.succ) =
      ∑ i ∈ Finset.range K, F (extendChain t i) (extendChain t (i + 1)) := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => F (extendChain t i) (extendChain t (i + 1))) K]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [extendChain_castSucc, extendChain_succ]


/-! ### Rademacher–Menshov for the 2-variation -/

/-- Sum of squared increments of `G` along a monotone sequence of indices bounded by `N`:
at most `4 ∑_{k ≤ N} |G k|²`. -/
private theorem sum_enorm_sq_sub_le {G : ℕ → ℂ} {q : ℕ → ℕ} (hq : Monotone q) {K N : ℕ}
    (hN : ∀ i, q i ≤ N) :
    ∑ i ∈ Finset.range K, ‖G (q i) - G (q (i + 1))‖ₑ ^ (2 : ℝ) ≤
      4 * ∑ k ∈ Finset.range (N + 1), ‖G k‖ₑ ^ (2 : ℝ) := by
  classical
  set T := (Finset.range K).filter fun i => q i < q (i + 1) with hT
  have hpt : ∀ i ∈ Finset.range K, ‖G (q i) - G (q (i + 1))‖ₑ ^ (2 : ℝ) ≤
      if q i < q (i + 1) then 2 * (‖G (q i)‖ₑ ^ (2 : ℝ) + ‖G (q (i + 1))‖ₑ ^ (2 : ℝ)) else 0 := by
    intro i _
    split_ifs with h
    · calc ‖G (q i) - G (q (i + 1))‖ₑ ^ (2 : ℝ)
          ≤ (‖G (q i)‖ₑ + ‖G (q (i + 1))‖ₑ) ^ (2 : ℝ) := by
            gcongr
            exact enorm_sub_le
        _ ≤ 2 ^ ((2 : ℝ) - 1) * (‖G (q i)‖ₑ ^ (2 : ℝ) + ‖G (q (i + 1))‖ₑ ^ (2 : ℝ)) :=
            ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (by norm_num)
        _ = 2 * (‖G (q i)‖ₑ ^ (2 : ℝ) + ‖G (q (i + 1))‖ₑ ^ (2 : ℝ)) := by norm_num
    · have : q i = q (i + 1) := le_antisymm (hq (Nat.le_succ i)) (not_lt.1 h)
      rw [this, sub_self, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
  have hinj1 : Set.InjOn q T := by
    intro i hi i' hi' hii
    simp only [hT, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi hi'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hq (show _ + 1 ≤ _ from hlt)
      omega
    · have := hq (show _ + 1 ≤ _ from hlt)
      omega
  have hinj2 : Set.InjOn (fun i => q (i + 1)) T := by
    intro i hi i' hi' hii
    simp only [hT, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi hi'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hq (show _ + 1 ≤ _ from hlt)
      simp only at hii
      omega
    · have := hq (show _ + 1 ≤ _ from hlt)
      simp only at hii
      omega
  have hsub : ∀ f : ℕ → ℝ≥0∞, ∀ φ : ℕ → ℕ, Set.InjOn φ T → (∀ i, φ i ≤ N) →
      ∑ i ∈ T, f (φ i) ≤ ∑ k ∈ Finset.range (N + 1), f k := by
    intro f φ hφ hφN
    rw [← Finset.sum_image hφ]
    refine Finset.sum_le_sum_of_subset fun k hk => ?_
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hk
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (hφN i))
  calc ∑ i ∈ Finset.range K, ‖G (q i) - G (q (i + 1))‖ₑ ^ (2 : ℝ)
      ≤ ∑ i ∈ Finset.range K, if q i < q (i + 1) then
          2 * (‖G (q i)‖ₑ ^ (2 : ℝ) + ‖G (q (i + 1))‖ₑ ^ (2 : ℝ)) else 0 :=
        Finset.sum_le_sum hpt
    _ = ∑ i ∈ T, 2 * (‖G (q i)‖ₑ ^ (2 : ℝ) + ‖G (q (i + 1))‖ₑ ^ (2 : ℝ)) :=
        (Finset.sum_filter _ _).symm
    _ = 2 * ∑ i ∈ T, ‖G (q i)‖ₑ ^ (2 : ℝ) + 2 * ∑ i ∈ T, ‖G (q (i + 1))‖ₑ ^ (2 : ℝ) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * ∑ k ∈ Finset.range (N + 1), ‖G k‖ₑ ^ (2 : ℝ) +
          2 * ∑ k ∈ Finset.range (N + 1), ‖G k‖ₑ ^ (2 : ℝ) := by
        gcongr
        · exact hsub (fun k => ‖G k‖ₑ ^ (2 : ℝ)) q hinj1 hN
        · exact hsub (fun k => ‖G k‖ₑ ^ (2 : ℝ)) (fun i => q (i + 1)) hinj2 fun i => hN _
    _ = 4 * ∑ k ∈ Finset.range (N + 1), ‖G k‖ₑ ^ (2 : ℝ) := by
        rw [← two_mul, ← mul_assoc]
        norm_num


/-- The dyadic martingale difference of a sequence `b` at level `m`, evaluated at the dyadic
cell index `q`: `b(q 2^m) - b(⌊q/2⌋ 2^{m+1})`. It vanishes for even `q` and equals the increment
of `b` over the cell `[(q-1) 2^m, q 2^m]` for odd `q`. -/
private def mgDiff (b : ℕ → ℂ) (m q : ℕ) : ℂ := b (q * 2 ^ m) - b (q / 2 * 2 ^ (m + 1))

/-- The martingale difference vanishes at the cell index `0`. -/
private theorem mgDiff_zero (b : ℕ → ℂ) (m : ℕ) : mgDiff b m 0 = 0 := by
  simp [mgDiff]

/-- At odd cell index the martingale difference is a dyadic increment, at even index it
vanishes. -/
private theorem enorm_mgDiff_succ_le (b : ℕ → ℂ) (m s : ℕ) :
    ‖mgDiff b m (s + 1)‖ₑ ≤ ‖b ((s + 1) * 2 ^ m) - b (s * 2 ^ m)‖ₑ := by
  rcases Nat.even_or_odd' s with ⟨k, rfl | rfl⟩
  · have h1 : (2 * k + 1) / 2 = k := by omega
    have h2 : k * 2 ^ (m + 1) = 2 * k * 2 ^ m := by ring
    simp only [mgDiff, h1, h2]
    exact le_rfl
  · have h1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have h2 : (k + 1) * 2 ^ (m + 1) = (2 * k + 1 + 1) * 2 ^ m := by ring
    simp only [mgDiff, h1, h2, sub_self, enorm_zero]
    exact zero_le

/-- Telescoping along the dyadic scales: `b j = b 0 + ∑_{m ≤ J} (b_m(j) - b_{m+1}(j))` for
`j < 2^{J+1}`. -/
private theorem eq_add_sum_mgDiff (b : ℕ → ℂ) (J j : ℕ) (hj : j < 2 ^ (J + 1)) :
    b j = b 0 + ∑ m ∈ Finset.range (J + 1), mgDiff b m (j / 2 ^ m) := by
  have h : ∀ m, mgDiff b m (j / 2 ^ m) =
      b (j / 2 ^ m * 2 ^ m) - b (j / 2 ^ (m + 1) * 2 ^ (m + 1)) := by
    intro m
    unfold mgDiff
    rw [Nat.div_div_eq_div_mul, ← pow_succ]
  simp_rw [h]
  rw [Finset.sum_range_sub' (fun m => b (j / 2 ^ m * 2 ^ m))]
  simp [Nat.div_eq_of_lt hj]

/-- The level-`m` contribution along a monotone chain of grid indices bounded by `2^J`. -/
private theorem sum_mgDiff_le (b : ℕ → ℂ) {J m : ℕ} (hm : m ≤ J) {K : ℕ} {jj : ℕ → ℕ}
    (hjj : Monotone jj) (hJ : ∀ i, jj i ≤ 2 ^ J) :
    ∑ i ∈ Finset.range K, ‖mgDiff b m (jj i / 2 ^ m) - mgDiff b m (jj (i + 1) / 2 ^ m)‖ₑ ^
        (2 : ℝ) ≤
      4 * ∑ s ∈ Finset.range (2 ^ (J - m)),
        ‖b ((s + 1) * 2 ^ m) - b (s * 2 ^ m)‖ₑ ^ (2 : ℝ) := by
  have hq : Monotone fun i => jj i / 2 ^ m := fun i i' h => Nat.div_le_div_right (hjj h)
  have hN : ∀ i, jj i / 2 ^ m ≤ 2 ^ (J - m) := fun i => by
    rw [← Nat.pow_div hm two_pos]
    exact Nat.div_le_div_right (hJ i)
  refine (sum_enorm_sq_sub_le (G := mgDiff b m) hq hN).trans ?_
  gcongr
  rw [Finset.sum_range_succ', mgDiff_zero, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num),
    add_zero]
  refine Finset.sum_le_sum fun s _ => ?_
  gcongr
  exact enorm_mgDiff_succ_le b m s

private theorem four_mul_rpow_half (X : ℝ≥0∞) : (4 * X) ^ (1 / 2 : ℝ) = 2 * X ^ (1 / 2 : ℝ) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  congr 1
  rw [show (4 : ℝ≥0∞) = 2 ^ (2 : ℝ) by rw [ENNReal.rpow_two]; norm_num, ← ENNReal.rpow_mul]
  norm_num


/-- The `r`-variation of a constant family vanishes. -/
private theorem rVariationOn_fun_const_eq_zero {r : ℝ} (hr : 0 < r) (S : Set ℝ) (c : ℂ) :
    rVariationOn r S (fun _ => c) = 0 := by
  refine le_antisymm (rVariationOn_le fun J t _ _ => ?_) zero_le
  simp [ENNReal.zero_rpow_of_pos hr, hr]

/-- **Rademacher–Menshov for the square variation** (lemma `l:RMvariation`). For every `J`,
every arithmetic progression `x₀ + h j`, `0 < h`, and every `a : ℝ → ℂ`, the `2`-variation of
`a` over `{x₀ + h j : 0 ≤ j ≤ 2^J}` is at most
`2 ∑_{m=0}^J S_m(a)`, where `S_m(a)² = ∑_{s < 2^{J-m}} |a(x₀ + h(s+1)2^m) - a(x₀ + h s 2^m)|²`.
The constant `2` is absolute. -/
theorem rVariationOn_two_le_sum_dyadic (J : ℕ) {h : ℝ} (hh : 0 < h) (x₀ : ℝ) (a : ℝ → ℂ) :
    rVariationOn 2 ((fun j : ℕ => x₀ + h * j) '' Set.Iic (2 ^ J)) a ≤
      2 * ∑ m ∈ Finset.range (J + 1),
        (∑ s ∈ Finset.range (2 ^ (J - m)),
          ‖a (x₀ + h * ((s + 1) * 2 ^ m)) - a (x₀ + h * (s * 2 ^ m))‖ₑ ^ (2 : ℝ)) ^
            (1 / 2 : ℝ) := by
  set S : Set ℝ := (fun j : ℕ => x₀ + h * j) '' Set.Iic (2 ^ J) with hS
  set b : ℕ → ℂ := fun j => a (x₀ + h * j) with hb
  set D : ℕ → ℝ → ℂ := fun m x => mgDiff b m (⌊(x - x₀) / h⌋₊ / 2 ^ m) with hD
  have hfloor : ∀ j : ℕ, ⌊(x₀ + h * j - x₀) / h⌋₊ = j := fun j => by
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hh.ne', Nat.floor_natCast]
  have hdec : ∀ x ∈ S, a x = a x₀ + ∑ m ∈ Finset.range (J + 1), D m x := by
    rintro x ⟨j, hj, rfl⟩
    have hj' : j < 2 ^ (J + 1) :=
      lt_of_le_of_lt (Set.mem_Iic.1 hj) (Nat.pow_lt_pow_right (by norm_num) (by omega))
    have := eq_add_sum_mgDiff b J j hj'
    simp only [hD, hfloor]
    simpa [hb] using this
  have hlevel : ∀ m ∈ Finset.range (J + 1), rVariationOn 2 S (D m) ≤
      2 * (∑ s ∈ Finset.range (2 ^ (J - m)),
          ‖a (x₀ + h * ((s + 1) * 2 ^ m)) - a (x₀ + h * (s * 2 ^ m))‖ₑ ^ (2 : ℝ)) ^
            (1 / 2 : ℝ) := by
    intro m hm
    have hmJ : m ≤ J := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    refine rVariationOn_le fun K t ht htS => ?_
    have htS' : ∀ i, ∃ j : ℕ, j ≤ 2 ^ J ∧ x₀ + h * j = t i := fun i => by
      obtain ⟨j, hj, hjt⟩ := htS i
      exact ⟨j, hj, hjt⟩
    choose j hj1 hj2 using htS'
    have hjmono : Monotone j := by
      intro i i' hii
      have h1 := ht.monotone hii
      rw [← hj2 i, ← hj2 i'] at h1
      have h3 : (j i : ℝ) ≤ j i' := by
        have := (mul_le_mul_iff_right₀ hh).1 (le_of_add_le_add_left h1)
        exact this
      exact_mod_cast h3
    have hjjmono : Monotone (extendChain j) := monotone_extendChain hjmono
    have hjjJ : ∀ i, extendChain j i ≤ 2 ^ J := fun i => hj1 _
    have htt : ∀ i, extendChain t i = x₀ + h * (extendChain j i : ℕ) := fun i => by
      simp only [extendChain]
      exact (hj2 _).symm
    have hconv : ∑ i : Fin K, ‖D m (t i.castSucc) - D m (t i.succ)‖ₑ ^ (2 : ℝ) =
        ∑ i ∈ Finset.range K,
          ‖D m (extendChain t i) - D m (extendChain t (i + 1))‖ₑ ^ (2 : ℝ) :=
      sum_fin_eq_sum_range_extendChain t (fun x y => ‖D m x - D m y‖ₑ ^ (2 : ℝ))
    have hD' : ∀ i, D m (extendChain t i) = mgDiff b m (extendChain j i / 2 ^ m) := fun i => by
      simp only [hD, htt, hfloor]
    have key := sum_mgDiff_le b hmJ (K := K) hjjmono hjjJ
    have hcast : ∀ s : ℕ, ‖b ((s + 1) * 2 ^ m) - b (s * 2 ^ m)‖ₑ =
        ‖a (x₀ + h * ((s + 1) * 2 ^ m)) - a (x₀ + h * (s * 2 ^ m))‖ₑ := fun s => by
      simp only [hb]
      push_cast
      rfl
    simp only [hcast] at key
    simp only [hconv, hD']
    calc (∑ i ∈ Finset.range K, ‖mgDiff b m (extendChain j i / 2 ^ m) -
            mgDiff b m (extendChain j (i + 1) / 2 ^ m)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        ≤ (4 * ∑ s ∈ Finset.range (2 ^ (J - m)),
            ‖a (x₀ + h * ((s + 1) * 2 ^ m)) - a (x₀ + h * (s * 2 ^ m))‖ₑ ^ (2 : ℝ)) ^
              (1 / 2 : ℝ) := ENNReal.rpow_le_rpow key (by norm_num)
      _ = _ := four_mul_rpow_half _
  calc rVariationOn 2 S a
      = rVariationOn 2 S (fun x => a x₀ + ∑ m ∈ Finset.range (J + 1), D m x) :=
        rVariationOn_congr hdec
    _ = rVariationOn 2 S ((fun _ => a x₀) + ∑ m ∈ Finset.range (J + 1), D m) := by
        congr 1
        ext x
        simp [Finset.sum_apply]
    _ ≤ rVariationOn 2 S (fun _ => a x₀) + rVariationOn 2 S (∑ m ∈ Finset.range (J + 1), D m) :=
        rVariationOn_add_le (by norm_num) S _ _
    _ ≤ 0 + ∑ m ∈ Finset.range (J + 1), rVariationOn 2 S (D m) :=
        add_le_add (rVariationOn_fun_const_eq_zero (by norm_num) S _).le
          (rVariationOn_sum_le _ (by norm_num) S D)
    _ ≤ ∑ m ∈ Finset.range (J + 1), 2 * (∑ s ∈ Finset.range (2 ^ (J - m)),
          ‖a (x₀ + h * ((s + 1) * 2 ^ m)) - a (x₀ + h * (s * 2 ^ m))‖ₑ ^ (2 : ℝ)) ^
            (1 / 2 : ℝ) := by
        rw [zero_add]
        exact Finset.sum_le_sum hlevel
    _ = _ := (Finset.mul_sum _ _ _).symm


/-- The Rademacher–Menshov bound on the dyadic grid `{j / 2^J : 0 ≤ j ≤ 2^J}`, in the form used
in the proof of `l:crudeV2lambda` (L1024-L1042): with `K = 2^{J-m}` the `m`-th square function is
`(∑_{s < K} |a((s+1)/K) - a(s/K)|²)^{1/2}`. -/
theorem rVariationOn_two_le_sum_dyadic_grid (J : ℕ) (a : ℝ → ℂ) :
    rVariationOn 2 ((fun j : ℕ => (j : ℝ) / 2 ^ J) '' Set.Iic (2 ^ J)) a ≤
      2 * ∑ m ∈ Finset.range (J + 1),
        (∑ s ∈ Finset.range (2 ^ (J - m)),
          ‖a (((s : ℝ) + 1) / 2 ^ (J - m)) - a ((s : ℝ) / 2 ^ (J - m))‖ₑ ^ (2 : ℝ)) ^
            (1 / 2 : ℝ) := by
  have hh : (0 : ℝ) < 1 / 2 ^ J := by positivity
  have h := rVariationOn_two_le_sum_dyadic J hh 0 a
  have hset : (fun j : ℕ => (0 : ℝ) + 1 / 2 ^ J * j) = fun j : ℕ => (j : ℝ) / 2 ^ J := by
    funext j
    ring
  rw [hset] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmJ : m ≤ J := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  have hpow : (2 : ℝ) ^ J = 2 ^ (J - m) * 2 ^ m := by
    rw [← pow_add]
    congr 1
    omega
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  have e1 : (0 : ℝ) + 1 / 2 ^ J * (((s : ℝ) + 1) * 2 ^ m) = ((s : ℝ) + 1) / 2 ^ (J - m) := by
    rw [hpow]
    field_simp
    ring
  have e2 : (0 : ℝ) + 1 / 2 ^ J * ((s : ℝ) * 2 ^ m) = (s : ℝ) / 2 ^ (J - m) := by
    rw [hpow]
    field_simp
    ring
  rw [e1, e2]


/-! ### The Jones–Seeger–Wright split inequality -/

/-- There is a strictly increasing chain in `S`, ending at `z`, whose `r`-th power sum of
increments is at least `σ`. -/
private def Reach (r : ℝ) (S : Set ℝ) (a : ℝ → ℂ) (z : ℝ) (σ : ℝ≥0∞) : Prop :=
  ∃ (J : ℕ) (t : Fin (J + 1) → ℝ), StrictMono t ∧ (∀ i, t i ∈ S) ∧ t (Fin.last J) = z ∧
    σ ≤ ∑ i : Fin J, ‖a (t i.castSucc) - a (t i.succ)‖ₑ ^ r

/-- A one-point chain. -/
private theorem reach_single {r : ℝ} {S : Set ℝ} {a : ℝ → ℂ} {z : ℝ} (hz : z ∈ S) :
    Reach r S a z 0 :=
  ⟨0, fun _ => z, fun i j hij => by
    exfalso
    have h1 := i.2
    have h2 := j.2
    rw [Fin.lt_def] at hij
    omega,
    fun _ => hz, rfl, zero_le⟩

/-- `Reach` is monotone in the carried amount. -/
private theorem reach_mono {r : ℝ} {S : Set ℝ} {a : ℝ → ℂ} {z : ℝ} {σ σ' : ℝ≥0∞} (h : σ' ≤ σ)
    (hR : Reach r S a z σ) : Reach r S a z σ' := by
  obtain ⟨J, t, h1, h2, h3, h4⟩ := hR
  exact ⟨J, t, h1, h2, h3, h.trans h4⟩

/-- Appending a point `z' ≥ z` to a chain ending at `z` adds the increment `|a z - a z'|^r`. -/
private theorem reach_append {r : ℝ} (hr : 0 < r) {S : Set ℝ} {a : ℝ → ℂ} {z z' : ℝ} {σ : ℝ≥0∞}
    (hz' : z' ∈ S) (hle : z ≤ z') (hR : Reach r S a z σ) :
    Reach r S a z' (σ + ‖a z - a z'‖ₑ ^ r) := by
  obtain ⟨J, t, hm, hS, hl, hσ⟩ := hR
  rcases hle.eq_or_lt with rfl | hlt
  · refine ⟨J, t, hm, hS, hl, ?_⟩
    simpa [ENNReal.zero_rpow_of_pos hr, hr] using hσ
  · have hlt' : t (Fin.last J) < z' := hl ▸ hlt
    have hmono : StrictMono (Fin.snoc (α := fun _ => ℝ) t z') := by
      refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hlt'
      · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hm (Fin.castSucc_lt_succ)
    refine ⟨J + 1, Fin.snoc (α := fun _ => ℝ) t z', hmono, ?_, by simp, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hz'
      · simpa using hS j
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_last, Fin.succ_castSucc]
      rw [hl]
      exact add_le_add hσ le_rfl


/-- A reachable amount is at most `V^r(S)^r`. -/
private theorem reach_le_rpow {r : ℝ} (hr : 0 < r) {S : Set ℝ} {a : ℝ → ℂ} {z : ℝ} {σ : ℝ≥0∞}
    (hR : Reach r S a z σ) : σ ≤ rVariationOn r S a ^ r := by
  obtain ⟨J, t, hm, hS, -, hσ⟩ := hR
  refine hσ.trans ?_
  rw [← ENNReal.rpow_inv_le_iff hr, ← one_div]
  exact le_rVariationOn hm hS

/-- Increments of a monotone sequence over any set of steps with endpoints in `S` have
`r`-th power sum at most `V^r(S)^r`. -/
private theorem sum_le_rVariationOn_rpow_aux {r : ℝ} (hr : 0 < r) {S : Set ℝ} (a : ℝ → ℂ)
    {u : ℕ → ℝ} (hu : Monotone u) (K : ℕ) :
    ∀ I : Finset ℕ, I ⊆ Finset.range K → (∀ i ∈ I, u i ∈ S ∧ u (i + 1) ∈ S) →
      ∑ i ∈ I, ‖a (u i) - a (u (i + 1))‖ₑ ^ r = 0 ∨
        ∃ z, z ≤ u K ∧ Reach r S a z (∑ i ∈ I, ‖a (u i) - a (u (i + 1))‖ₑ ^ r) := by
  classical
  induction K with
  | zero =>
    intro I hI _
    left
    have : I = ∅ := Finset.subset_empty.1 (by simpa using hI)
    simp [this]
  | succ K ih =>
    intro I hI hS
    by_cases hK : K ∈ I
    · have hI' : I.erase K ⊆ Finset.range K := by
        intro i hi
        have h1 := hI (Finset.mem_of_mem_erase hi)
        have h2 := Finset.ne_of_mem_erase hi
        simp only [Finset.mem_range] at h1 ⊢
        omega
      have hS' : ∀ i ∈ I.erase K, u i ∈ S ∧ u (i + 1) ∈ S := fun i hi =>
        hS i (Finset.mem_of_mem_erase hi)
      obtain ⟨hx, hy⟩ := hS K hK
      rw [← Finset.add_sum_erase I _ hK]
      right
      have hy' : u (K + 1) ≤ u (K + 1) := le_rfl
      rcases ih (I.erase K) hI' hS' with h0 | ⟨z, hz, hR⟩
      · refine ⟨u (K + 1), hy', ?_⟩
        rw [h0, add_zero]
        have := reach_append hr hy (hu (Nat.le_succ K)) (reach_single (r := r) (a := a) hx)
        simpa using this
      · refine ⟨u (K + 1), hy', ?_⟩
        have h1 := reach_append hr hx hz hR
        have h2 := reach_append hr hy (hu (Nat.le_succ K)) h1
        refine reach_mono ?_ h2
        calc ‖a (u K) - a (u (K + 1))‖ₑ ^ r + ∑ i ∈ I.erase K, ‖a (u i) - a (u (i + 1))‖ₑ ^ r
            = (∑ i ∈ I.erase K, ‖a (u i) - a (u (i + 1))‖ₑ ^ r) +
                ‖a (u K) - a (u (K + 1))‖ₑ ^ r := add_comm _ _
          _ ≤ _ := add_le_add le_self_add le_rfl
    · have hI' : I ⊆ Finset.range K := by
        intro i hi
        have h1 := hI hi
        have h2 : i ≠ K := fun h => hK (h ▸ hi)
        simp only [Finset.mem_range] at h1 ⊢
        omega
      rcases ih I hI' hS with h0 | ⟨z, hz, hR⟩
      · exact Or.inl h0
      · exact Or.inr ⟨z, hz.trans (hu (Nat.le_succ K)), hR⟩

private theorem sum_le_rVariationOn_rpow {r : ℝ} (hr : 0 < r) {S : Set ℝ} (a : ℝ → ℂ) {u : ℕ → ℝ}
    (hu : Monotone u) {K : ℕ} {I : Finset ℕ} (hI : I ⊆ Finset.range K)
    (hS : ∀ i ∈ I, u i ∈ S ∧ u (i + 1) ∈ S) :
    ∑ i ∈ I, ‖a (u i) - a (u (i + 1))‖ₑ ^ r ≤ rVariationOn r S a ^ r := by
  rcases sum_le_rVariationOn_rpow_aux hr a hu K I hI hS with h0 | ⟨z, -, hR⟩
  · rw [h0]
    exact zero_le
  · exact reach_le_rpow hr hR

private theorem enorm_sub_rpow_le {r : ℝ} (hr : 0 < r) {S : Set ℝ} (a : ℝ → ℂ) {x y : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) : ‖a x - a y‖ₑ ^ r ≤ rVariationOn r S a ^ r := by
  rcases le_total x y with hxy | hyx
  · have := reach_le_rpow hr (reach_append hr hy hxy (reach_single (r := r) (a := a) hx))
    simpa using this
  · have := reach_le_rpow hr (reach_append hr hx hyx (reach_single (r := r) (a := a) hy))
    rwa [zero_add, enorm_sub_rev] at this


/-- Minkowski's inequality for four summands. -/
private theorem Lp_add_le_four {ι : Type*} (s : Finset ι) {p : ℝ} (hp : 1 ≤ p)
    (f₁ f₂ f₃ f₄ : ι → ℝ≥0∞) :
    (∑ i ∈ s, (f₁ i + f₂ i + f₃ i + f₄ i) ^ p) ^ (1 / p) ≤
      (∑ i ∈ s, f₁ i ^ p) ^ (1 / p) + (∑ i ∈ s, f₂ i ^ p) ^ (1 / p) +
        (∑ i ∈ s, f₃ i ^ p) ^ (1 / p) + (∑ i ∈ s, f₄ i ^ p) ^ (1 / p) := by
  calc (∑ i ∈ s, (f₁ i + f₂ i + f₃ i + f₄ i) ^ p) ^ (1 / p)
      ≤ (∑ i ∈ s, (f₁ i + f₂ i + f₃ i) ^ p) ^ (1 / p) + (∑ i ∈ s, f₄ i ^ p) ^ (1 / p) :=
        ENNReal.Lp_add_le s (fun i => f₁ i + f₂ i + f₃ i) f₄ hp
    _ ≤ ((∑ i ∈ s, (f₁ i + f₂ i) ^ p) ^ (1 / p) + (∑ i ∈ s, f₃ i ^ p) ^ (1 / p)) +
          (∑ i ∈ s, f₄ i ^ p) ^ (1 / p) :=
        add_le_add (ENNReal.Lp_add_le s (fun i => f₁ i + f₂ i) f₃ hp) le_rfl
    _ ≤ (((∑ i ∈ s, f₁ i ^ p) ^ (1 / p) + (∑ i ∈ s, f₂ i ^ p) ^ (1 / p)) +
          (∑ i ∈ s, f₃ i ^ p) ^ (1 / p)) + (∑ i ∈ s, f₄ i ^ p) ^ (1 / p) :=
        add_le_add (add_le_add (ENNReal.Lp_add_le s f₁ f₂ hp) le_rfl) le_rfl

/-- A sum over a set of steps `i` with `P i`, on which an injective index map `φ` into a finite
type is used, is at most the sum of the bounds `W` over that type. -/
private theorem sum_ite_le_sum_of_injOn {N K : ℕ} (P : ℕ → Prop) [DecidablePred P] (φ : ℕ → Fin N)
    (H : ℕ → ℝ≥0∞) (W : Fin N → ℝ≥0∞)
    (hinj : ∀ i ∈ Finset.range K, ∀ i' ∈ Finset.range K, P i → P i' → φ i = φ i' → i = i')
    (hH : ∀ i, P i → H i ≤ W (φ i)) :
    ∑ i ∈ Finset.range K, (if P i then H i else 0) ≤ ∑ n, W n := by
  classical
  rw [← Finset.sum_filter]
  calc ∑ i ∈ (Finset.range K).filter P, H i
      ≤ ∑ i ∈ (Finset.range K).filter P, W (φ i) :=
        Finset.sum_le_sum fun i hi => hH i (Finset.mem_filter.1 hi).2
    _ = ∑ n ∈ ((Finset.range K).filter P).image φ, W n := by
        refine (Finset.sum_image ?_).symm
        intro i hi i' hi' hii
        have hi := Finset.mem_filter.1 hi
        have hi' := Finset.mem_filter.1 hi'
        exact hinj i hi.1 i' hi'.1 hi.2 hi'.2 hii
    _ ≤ ∑ n, W n := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

private theorem rpow_rpow_one_div {r : ℝ} (hr : 0 < r) (x : ℝ≥0∞) : (x ^ r) ^ (1 / r) = x := by
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one]

/-- **Jones–Seeger–Wright split inequality** (display `e:split`). Let `J = ⋃ₙ Jₙ` be a union of
`N` blocks which are ordered (every point of `Jₙ` lies below every point of `Jₙ'` for `n < n'`),
and let `pₙ ∈ Jₙ` be one reference point in each
block (for the printed form `Jₙ = J ∩ [Aₙ, Bₙ]`, `pₙ = Bₙ`). Then for every `1 ≤ r`
`V^r(a : J) ≤ 3 (∑ₙ V^r(a : Jₙ)^r)^{1/r} + V^r(a_{pₙ} : n)`
with an absolute constant. -/
theorem rVariationOn_iUnion_le {r : ℝ} (hr : 1 ≤ r) {N : ℕ} (Jn : Fin N → Set ℝ)
    (hord : ∀ n n' : Fin N, n < n' → ∀ x ∈ Jn n, ∀ y ∈ Jn n', x < y)
    (p : Fin N → ℝ) (hp : ∀ n, p n ∈ Jn n) (a : ℝ → ℂ) :
    rVariationOn r (⋃ n, Jn n) a ≤
      3 * (∑ n, rVariationOn r (Jn n) a ^ r) ^ (1 / r) + rVariationOn r (Set.range p) a := by
  classical
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hpmono : StrictMono p := fun n n' h => hord n n' h _ (hp n) _ (hp n')
  refine rVariationOn_le fun K t ht htS => ?_
  have htS' : ∀ i, ∃ n, t i ∈ Jn n := fun i => Set.mem_iUnion.1 (htS i)
  choose bl hbl using htS'
  set u : ℕ → ℝ := extendChain t with hu_def
  set b : ℕ → Fin N := extendChain bl with hb_def
  have hu : Monotone u := monotone_extendChain ht.monotone
  have hub : ∀ i, u i ∈ Jn (b i) := fun i => hbl _
  have hbmono : Monotone b := by
    intro i i' hii
    by_contra hlt
    have := hord _ _ (not_le.1 hlt) _ (hub i') _ (hub i)
    exact absurd (hu hii) (not_le.2 this)
  have hconv : ∑ i : Fin K, ‖a (t i.castSucc) - a (t i.succ)‖ₑ ^ r =
      ∑ i ∈ Finset.range K, ‖a (u i) - a (u (i + 1))‖ₑ ^ r :=
    sum_fin_eq_sum_range_extendChain t (fun x y => ‖a x - a y‖ₑ ^ r)
  rw [hconv]
  set W : ℝ≥0∞ := ∑ n, rVariationOn r (Jn n) a ^ r with hW
  set X1 : ℕ → ℝ≥0∞ := fun i => if b i = b (i + 1) then ‖a (u i) - a (u (i + 1))‖ₑ else 0
    with hX1
  set X2 : ℕ → ℝ≥0∞ := fun i => if b i = b (i + 1) then 0 else ‖a (u i) - a (p (b i))‖ₑ
    with hX2
  set X3 : ℕ → ℝ≥0∞ := fun i => ‖a (p (b i)) - a (p (b (i + 1)))‖ₑ with hX3
  set X4 : ℕ → ℝ≥0∞ := fun i =>
    if b i = b (i + 1) then 0 else ‖a (p (b (i + 1))) - a (u (i + 1))‖ₑ with hX4
  have hpt : ∀ i, ‖a (u i) - a (u (i + 1))‖ₑ ≤ X1 i + X2 i + X3 i + X4 i := by
    intro i
    by_cases h : b i = b (i + 1)
    · simp [hX1, hX2, hX4, h]
    · simp only [hX1, hX2, hX3, hX4, h, ↓reduceIte, zero_add]
      calc ‖a (u i) - a (u (i + 1))‖ₑ
          = ‖(a (u i) - a (p (b i))) + (a (p (b i)) - a (p (b (i + 1)))) +
              (a (p (b (i + 1))) - a (u (i + 1)))‖ₑ := by
            congr 1
            ring
        _ ≤ ‖a (u i) - a (p (b i))‖ₑ + ‖a (p (b i)) - a (p (b (i + 1)))‖ₑ +
              ‖a (p (b (i + 1))) - a (u (i + 1))‖ₑ :=
            (enorm_add_le _ _).trans (add_le_add_left (enorm_add_le _ _) _)
  have hB1 : ∑ i ∈ Finset.range K, X1 i ^ r ≤ W := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := b) (t := Finset.univ)
      (fun i _ => Finset.mem_univ _)]
    refine Finset.sum_le_sum fun n _ => ?_
    have h1 : ∑ i ∈ (Finset.range K).filter (fun i => b i = n), X1 i ^ r =
        ∑ i ∈ ((Finset.range K).filter (fun i => b i = n)).filter (fun i => b (i + 1) = n),
          ‖a (u i) - a (u (i + 1))‖ₑ ^ r := by
      refine Eq.trans (Finset.sum_congr rfl fun i hi => ?_)
        (Finset.sum_filter (fun i => b (i + 1) = n)
          (fun i => ‖a (u i) - a (u (i + 1))‖ₑ ^ r)).symm
      have hbi : b i = n := (Finset.mem_filter.1 hi).2
      simp only [hX1, hbi]
      by_cases h : b (i + 1) = n
      · simp [h]
      · have h' : ¬ n = b (i + 1) := fun h'' => h h''.symm
        simp [h', h, ENNReal.zero_rpow_of_pos hr0]
    rw [h1]
    refine sum_le_rVariationOn_rpow hr0 a hu (S := Jn n) (K := K) ?_ ?_
    · exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    · intro i hi
      have hi1 := Finset.mem_filter.1 hi
      have hi2 := Finset.mem_filter.1 hi1.1
      exact ⟨hi2.2 ▸ hub i, hi1.2 ▸ hub (i + 1)⟩
  have hB2 : ∑ i ∈ Finset.range K, X2 i ^ r ≤ W := by
    have h1 : ∀ i, X2 i ^ r = if b i ≠ b (i + 1) then ‖a (u i) - a (p (b i))‖ₑ ^ r else 0 := by
      intro i
      by_cases h : b i = b (i + 1)
      · simp [hX2, h, ENNReal.zero_rpow_of_pos hr0]
      · simp [hX2, h]
    simp_rw [h1]
    refine sum_ite_le_sum_of_injOn (fun i => b i ≠ b (i + 1)) b
      (fun i => ‖a (u i) - a (p (b i))‖ₑ ^ r) (fun n => rVariationOn r (Jn n) a ^ r) ?_ ?_
    · intro i _ i' _ hi hi' hbb
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have h1 : b (i + 1) ≤ b i' := hbmono (show i + 1 ≤ i' from hlt)
        have h2 : b i ≤ b (i + 1) := hbmono (Nat.le_succ i)
        exact hi (le_antisymm h2 (h1.trans hbb.symm.le))
      · have h1 : b (i' + 1) ≤ b i := hbmono (show i' + 1 ≤ i from hlt)
        have h2 : b i' ≤ b (i' + 1) := hbmono (Nat.le_succ i')
        exact hi' (le_antisymm h2 (h1.trans hbb.le))
    · intro i _
      exact enorm_sub_rpow_le hr0 a (hub i) (hp (b i))
  have hB4 : ∑ i ∈ Finset.range K, X4 i ^ r ≤ W := by
    have h1 : ∀ i, X4 i ^ r =
        if b i ≠ b (i + 1) then ‖a (p (b (i + 1))) - a (u (i + 1))‖ₑ ^ r else 0 := by
      intro i
      by_cases h : b i = b (i + 1)
      · simp [hX4, h, ENNReal.zero_rpow_of_pos hr0]
      · simp [hX4, h]
    simp_rw [h1]
    refine sum_ite_le_sum_of_injOn (fun i => b i ≠ b (i + 1)) (fun i => b (i + 1))
      (fun i => ‖a (p (b (i + 1))) - a (u (i + 1))‖ₑ ^ r)
      (fun n => rVariationOn r (Jn n) a ^ r) ?_ ?_
    · intro i _ i' _ hi hi' hbb
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have h1 : b (i + 1) ≤ b i' := hbmono (show i + 1 ≤ i' from hlt)
        have h2 : b i' ≤ b (i' + 1) := hbmono (Nat.le_succ i')
        exact hi' (le_antisymm h2 (hbb.symm.le.trans h1))
      · have h1 : b (i' + 1) ≤ b i := hbmono (show i' + 1 ≤ i from hlt)
        have h2 : b i ≤ b (i + 1) := hbmono (Nat.le_succ i)
        exact hi (le_antisymm h2 (hbb.le.trans h1))
    · intro i _
      exact enorm_sub_rpow_le hr0 a (hp (b (i + 1))) (hub (i + 1))
  have hB3 : ∑ i ∈ Finset.range K, X3 i ^ r ≤ rVariationOn r (Set.range p) a ^ r :=
    sum_le_rVariationOn_rpow hr0 a (u := fun i => p (b i)) (hpmono.monotone.comp hbmono)
      (K := K) (I := Finset.range K) subset_rfl fun i _ => ⟨⟨b i, rfl⟩, ⟨b (i + 1), rfl⟩⟩
  calc (∑ i ∈ Finset.range K, ‖a (u i) - a (u (i + 1))‖ₑ ^ r) ^ (1 / r)
      ≤ (∑ i ∈ Finset.range K, (X1 i + X2 i + X3 i + X4 i) ^ r) ^ (1 / r) :=
        ENNReal.rpow_le_rpow (Finset.sum_le_sum fun i _ => ENNReal.rpow_le_rpow (hpt i) hr0.le)
          (by positivity)
    _ ≤ (∑ i ∈ Finset.range K, X1 i ^ r) ^ (1 / r) + (∑ i ∈ Finset.range K, X2 i ^ r) ^ (1 / r) +
          (∑ i ∈ Finset.range K, X3 i ^ r) ^ (1 / r) +
            (∑ i ∈ Finset.range K, X4 i ^ r) ^ (1 / r) :=
        Lp_add_le_four _ hr _ _ _ _
    _ ≤ W ^ (1 / r) + W ^ (1 / r) + rVariationOn r (Set.range p) a + W ^ (1 / r) := by
        have hr1 : (0 : ℝ) ≤ 1 / r := by positivity
        refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
        · exact ENNReal.rpow_le_rpow hB1 hr1
        · exact ENNReal.rpow_le_rpow hB2 hr1
        · exact (ENNReal.rpow_le_rpow hB3 hr1).trans (rpow_rpow_one_div hr0 _).le
        · exact ENNReal.rpow_le_rpow hB4 hr1
    _ = 3 * W ^ (1 / r) + rVariationOn r (Set.range p) a := by ring


/-- Second line of `e:split`: the `r`-variation along an injective finite family of points is at
most `2` times its `ℓ^r` norm, `V^r(a_{pₙ} : n) ≤ 2 (∑ₙ |a(pₙ)|^r)^{1/r}` for `1 ≤ r`. -/
theorem rVariationOn_range_le {r : ℝ} (hr : 1 ≤ r) {N : ℕ} {p : Fin N → ℝ}
    (hp : Function.Injective p) (a : ℝ → ℂ) :
    rVariationOn r (Set.range p) a ≤ 2 * (∑ n, ‖a (p n)‖ₑ ^ r) ^ (1 / r) := by
  classical
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  refine rVariationOn_le fun K t ht htS => ?_
  have hsum : ∀ s : Fin K → ℝ, Function.Injective s → (∀ i, s i ∈ Set.range p) →
      ∑ i, ‖a (s i)‖ₑ ^ r ≤ ∑ n, ‖a (p n)‖ₑ ^ r := by
    intro s hs hsr
    calc ∑ i, ‖a (s i)‖ₑ ^ r = ∑ x ∈ Finset.univ.image s, ‖a x‖ₑ ^ r :=
          (Finset.sum_image (f := fun x => ‖a x‖ₑ ^ r) (g := s)
            (fun i _ j _ h => hs h)).symm
      _ ≤ ∑ x ∈ Finset.univ.image p, ‖a x‖ₑ ^ r := by
          refine Finset.sum_le_sum_of_subset fun x hx => ?_
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hx
          obtain ⟨n, hn⟩ := hsr i
          exact Finset.mem_image.2 ⟨n, Finset.mem_univ _, hn⟩
      _ = ∑ n, ‖a (p n)‖ₑ ^ r :=
          Finset.sum_image (f := fun x => ‖a x‖ₑ ^ r) (g := p) (fun i _ j _ h => hp h)
  have hr1 : (0 : ℝ) ≤ 1 / r := by positivity
  have h1 : ∀ i : Fin K, ‖a (t i.castSucc) - a (t i.succ)‖ₑ ^ r ≤
      (‖a (t i.castSucc)‖ₑ + ‖a (t i.succ)‖ₑ) ^ r := fun i =>
    ENNReal.rpow_le_rpow enorm_sub_le hr0.le
  have h2 := ENNReal.Lp_add_le (Finset.univ : Finset (Fin K)) (fun i => ‖a (t i.castSucc)‖ₑ)
    (fun i => ‖a (t i.succ)‖ₑ) hr
  have h3 : ∑ i : Fin K, ‖a (t i.castSucc)‖ₑ ^ r ≤ ∑ n, ‖a (p n)‖ₑ ^ r :=
    hsum (fun i => t i.castSucc) (ht.injective.comp (Fin.castSucc_injective K)) fun i => htS _
  have h4 : ∑ i : Fin K, ‖a (t i.succ)‖ₑ ^ r ≤ ∑ n, ‖a (p n)‖ₑ ^ r :=
    hsum (fun i => t i.succ) (ht.injective.comp (Fin.succ_injective K)) fun i => htS _
  calc (∑ i : Fin K, ‖a (t i.castSucc) - a (t i.succ)‖ₑ ^ r) ^ (1 / r)
      ≤ (∑ i : Fin K, (‖a (t i.castSucc)‖ₑ + ‖a (t i.succ)‖ₑ) ^ r) ^ (1 / r) :=
        ENNReal.rpow_le_rpow (Finset.sum_le_sum fun i _ => h1 i) hr1
    _ ≤ (∑ i : Fin K, ‖a (t i.castSucc)‖ₑ ^ r) ^ (1 / r) +
          (∑ i : Fin K, ‖a (t i.succ)‖ₑ ^ r) ^ (1 / r) := h2
    _ ≤ (∑ n, ‖a (p n)‖ₑ ^ r) ^ (1 / r) + (∑ n, ‖a (p n)‖ₑ ^ r) ^ (1 / r) :=
        add_le_add (ENNReal.rpow_le_rpow h3 hr1) (ENNReal.rpow_le_rpow h4 hr1)
    _ = 2 * (∑ n, ‖a (p n)‖ₑ ^ r) ^ (1 / r) := (two_mul _).symm

/-- The split inequality with the `ℓ^r` norm of the reference values in place of their
variation (the second line of `e:split`, the form used in the proof of `e:embed`, L1110-L1115):
`V^r(a : J) ≤ 3 (∑ₙ V^r(a : Jₙ)^r)^{1/r} + 2 (∑ₙ |a(pₙ)|^r)^{1/r}`. -/
theorem rVariationOn_iUnion_le_norm {r : ℝ} (hr : 1 ≤ r) {N : ℕ} (Jn : Fin N → Set ℝ)
    (hord : ∀ n n' : Fin N, n < n' → ∀ x ∈ Jn n, ∀ y ∈ Jn n', x < y)
    (p : Fin N → ℝ) (hp : ∀ n, p n ∈ Jn n) (a : ℝ → ℂ) :
    rVariationOn r (⋃ n, Jn n) a ≤
      3 * (∑ n, rVariationOn r (Jn n) a ^ r) ^ (1 / r) + 2 * (∑ n, ‖a (p n)‖ₑ ^ r) ^ (1 / r) :=
  by
  have hpmono : StrictMono p := fun n n' h => hord n n' h _ (hp n) _ (hp n')
  exact (rVariationOn_iUnion_le hr Jn hord p hp a).trans
    (add_le_add_right (rVariationOn_range_le hr hpmono.injective a) _)


/-- The printed form of `e:split`: a set `J ⊆ ℝ` covered by `N` consecutive disjoint closed
intervals `[Aₙ, Bₙ]` (`Bₙ < Aₙ'` for `n < n'`) whose right endpoints `Bₙ` lie in `J`, split as
`Jₙ = J ∩ [Aₙ, Bₙ]`:
`V^r(a : J) ≤ 3 (∑ₙ V^r(a : Jₙ)^r)^{1/r} + V^r(a_{Bₙ} : n)` for `1 ≤ r`. -/
theorem rVariationOn_split_Icc {r : ℝ} (hr : 1 ≤ r) {N : ℕ} (A B : Fin N → ℝ) (J : Set ℝ)
    (hAB : ∀ n, A n ≤ B n) (hlt : ∀ n n' : Fin N, n < n' → B n < A n')
    (hJ : J ⊆ ⋃ n, Set.Icc (A n) (B n)) (hB : ∀ n, B n ∈ J) (a : ℝ → ℂ) :
    rVariationOn r J a ≤
      3 * (∑ n, rVariationOn r (J ∩ Set.Icc (A n) (B n)) a ^ r) ^ (1 / r) +
        rVariationOn r (Set.range B) a := by
  have hU : (⋃ n, J ∩ Set.Icc (A n) (B n)) = J := by
    rw [← Set.inter_iUnion]
    exact Set.inter_eq_left.2 hJ
  have h := rVariationOn_iUnion_le hr (fun n => J ∩ Set.Icc (A n) (B n))
    (fun n n' hn x hx y hy => lt_of_le_of_lt hx.2.2 (lt_of_lt_of_le (hlt n n' hn) hy.2.1))
    B (fun n => ⟨hB n, hAB n, le_rfl⟩) a
  rwa [hU] at h

end PrimeCarleson.Proof.Common

module

public import PrimeCarleson.Proof.Fplus31.Comparison.Block
public import PrimeCarleson.Proof.Fplus31.Comparison.Numeric

/-!
# The `U³` comparison of the Cramér model with the Heath-Brown model

The comparison of the Cramér model with the Heath-Brown model in the proof of [F+] Proposition 3.1:
with `L = (log N)^{1/10}`, `T = e^L`, `T' = 2^{⌊log₂ T⌋}` and `w = T' + 1` (`cramerLevel`),
`‖Λ_{C,w} - Λ_{≤T}‖_{U³[N]} ≪ exp(-c (log N)^{1/10})` (`cramer_heathBrown_U3`; `Λ_{≤T}` is the
`heathBrownModel T`, `‖·‖_{U³[N]}` the `gowersNormInterval 3 N`).

Proof (all steps in `Comparison/`):
1. `Basic`: `Λ_{C,w} - Λ_{≤T} = ∑_{q ∣ P(w), q > T'} μ(q) c_q/φ(q)` (Ramanujan identity of
   `Cramer/Ramanujan.lean`; every squarefree `q ≤ T'` divides `P(w)`);
2. split at `R = 2^{⌊log₂ ⌊N^{1/21}⌋⌋}`;
3. `Block`: `D₁` (`T' < q ≤ R`): dyadic blocks and Proposition 2.1 for arbitrary blocks,
   `≪ T'^{-1/4}`;
4. `Orth`, `Rankin`, `L2`, `Numeric`: `D₂` (`q > R`): `‖D₂‖_{U³[N]} ≤ 2 ‖D₂‖_{L²[N]}`, with
   `E|D₂|² = (S - S_R) m + S_R (1 - m) + O(R⁴/N)` (orthogonality, `Λ_{C,w}² = S Λ_{C,w}`,
   Rankin's trick, Brun's pure sieve for `m`), which is `≤ e^{-L}`;
5. here: the parameters (`L ≥ 40` for large `N`; small `N` by the trivial bound
   `‖f‖_{U³[N]} ≤ 2 sup|f|`).
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open PrimeCarleson

/-- The Cramér level `w = 2^{⌊log₂ T⌋} + 1 = T' + 1` for `T = exp((log N)^{1/10})`. -/
def cramerLevel (N : ℕ) : ℕ :=
  2 ^ Nat.log 2 ⌊Real.exp (Real.log N ^ ((1 : ℝ) / 10))⌋₊ + 1

/-- For `y ≥ 1`, `2^{⌊log₂ ⌊y⌋⌋} ≤ y < 2^{⌊log₂ ⌊y⌋⌋ + 1}`. -/
theorem two_pow_log_floor_facts {y : ℝ} (hy : 1 ≤ y) :
    (2 : ℝ) ^ Nat.log 2 ⌊y⌋₊ ≤ y ∧ y < (2 : ℝ) ^ (Nat.log 2 ⌊y⌋₊ + 1) := by
  have hm : ⌊y⌋₊ ≠ 0 := (Nat.floor_pos.2 hy).ne'
  have h1 : 2 ^ Nat.log 2 ⌊y⌋₊ ≤ ⌊y⌋₊ := Nat.pow_log_le_self 2 hm
  have h2 : ⌊y⌋₊ < 2 ^ (Nat.log 2 ⌊y⌋₊ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  refine ⟨?_, ?_⟩
  · calc (2 : ℝ) ^ Nat.log 2 ⌊y⌋₊ = ((2 ^ Nat.log 2 ⌊y⌋₊ : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ y := Nat.floor_le (by linarith)
  · calc y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
      _ ≤ ((2 ^ (Nat.log 2 ⌊y⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast h2
      _ = (2 : ℝ) ^ (Nat.log 2 ⌊y⌋₊ + 1) := by push_cast; rfl

/-- The level `w = 2^J + 1` satisfies `2 ≤ w ≤ 2 e^L` for `T = e^L`, `L ≥ 0`. -/
theorem cramerLevel_facts {L : ℝ} (hL : 0 ≤ L) :
    (2 : ℝ) ^ Nat.log 2 ⌊Real.exp L⌋₊ ≤ Real.exp L ∧
      Real.exp L < (2 : ℝ) ^ (Nat.log 2 ⌊Real.exp L⌋₊ + 1) ∧
      (2 : ℝ) ≤ (2 : ℝ) ^ Nat.log 2 ⌊Real.exp L⌋₊ + 1 ∧
      (2 : ℝ) ^ Nat.log 2 ⌊Real.exp L⌋₊ + 1 ≤ 2 * Real.exp L := by
  have hT1 : 1 ≤ Real.exp L := Real.one_le_exp hL
  obtain ⟨h1, h2⟩ := two_pow_log_floor_facts hT1
  refine ⟨h1, h2, ?_, by linarith⟩
  have : (1 : ℝ) ≤ (2 : ℝ) ^ Nat.log 2 ⌊Real.exp L⌋₊ := one_le_pow₀ (by norm_num)
  linarith


/-- The function `Λ_{C,w} - Λ_{≤T}` of the comparison, `w = cramerLevel N`,
`T = exp((log N)^{1/10})`. -/
def cramerSubHB (N : ℕ) (n : ℤ) : ℂ :=
  (cramerModel (cramerLevel N) n : ℂ) -
    heathBrownModel (Real.exp (Real.log N ^ ((1 : ℝ) / 10))) n

/-- `2 e^L ≤ e^{L^{10}/21}` for `L ≥ 40`: the cut `R ≈ N^{1/21}` lies above `T'`. -/
theorem two_exp_le_exp_div {L : ℝ} (hL : 40 ≤ L) :
    2 * Real.exp L ≤ Real.exp (L ^ 10 / 21) := by
  have hX := ten_pow_six_mul_sq_le hL
  have h1 : L + 1 ≤ L ^ 10 / 21 := by nlinarith
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  calc 2 * Real.exp L ≤ Real.exp 1 * Real.exp L := by nlinarith [Real.exp_pos L]
    _ = Real.exp (L + 1) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (L ^ 10 / 21) := Real.exp_le_exp.2 h1

/-- **`D₁ + D₂`: the large-`N` bound** (`L = (log N)^{1/10} ≥ 40`). -/
theorem exists_large_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ+, 40 ≤ Real.log N ^ ((1 : ℝ) / 10) →
      gowersNormInterval 3 N (cramerSubHB N) ≤
        K * Real.exp (-(1 / 4 : ℝ) * Real.log N ^ ((1 : ℝ) / 10)) := by
  obtain ⟨K1, hK1⟩ := exists_gowersNormInterval_dpart_le
  refine ⟨max K1 0 + 2, by positivity, fun N hL => ?_⟩
  set n0 : ℕ := (N : ℕ) with hn0
  have hn1 : 1 ≤ n0 := N.pos
  have hn1r : (1 : ℝ) ≤ n0 := by exact_mod_cast hn1
  set L : ℝ := Real.log n0 ^ ((1 : ℝ) / 10) with hLdef
  have hL0 : 0 ≤ L := by linarith
  have hlog : Real.log n0 = L ^ 10 := by
    rw [hLdef, ← Real.rpow_natCast, ← Real.rpow_mul (Real.log_nonneg hn1r)]
    norm_num
  have hNexp : (n0 : ℝ) = Real.exp (L ^ 10) := by
    rw [← hlog, Real.exp_log (by linarith)]
  obtain ⟨hJ1, hJ2, hw2r, hwL⟩ := cramerLevel_facts hL0
  set J : ℕ := Nat.log 2 ⌊Real.exp L⌋₊ with hJ
  have hw2 : 2 ≤ 2 ^ J + 1 := by have := @Nat.one_le_two_pow J; omega
  have hwL' : ((2 ^ J + 1 : ℕ) : ℝ) ≤ 2 * Real.exp L := by push_cast; exact hwL
  -- the dyadic cut `R = 2^{J'} ≈ N^{1/21}`
  have hy1 : (1 : ℝ) ≤ Real.exp (L ^ 10 / 21) := Real.one_le_exp (by positivity)
  obtain ⟨hR1, hR2⟩ := two_pow_log_floor_facts hy1
  set J' : ℕ := Nat.log 2 ⌊Real.exp (L ^ 10 / 21)⌋₊ with hJ'
  have hpow : (2 : ℝ) ^ (J' + 1) = 2 * 2 ^ J' := by ring
  have hRlo : Real.exp (L ^ 10 / 21) ≤ 2 * ((2 ^ J' : ℕ) : ℝ) := by
    push_cast; rw [hpow] at hR2; linarith
  have hRhi : ((2 ^ J' : ℕ) : ℝ) ≤ Real.exp (L ^ 10 / 21) := by push_cast; exact hR1
  have hJJ : J ≤ J' := by
    have h1 := two_exp_le_exp_div hL
    have h2 : (2 : ℝ) ^ J ≤ 2 ^ J' := by
      rw [hpow] at hR2
      linarith
    have h3 : 2 ^ J ≤ 2 ^ J' := by exact_mod_cast h2
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3
  have hN20 : ((2 : ℝ) ^ J') ^ 20 ≤ ((N : ℕ+) : ℝ) := by
    have h0 : ((N : ℕ+) : ℝ) = (n0 : ℝ) := rfl
    rw [h0, hNexp]
    calc ((2 : ℝ) ^ J') ^ 20 ≤ (Real.exp (L ^ 10 / 21)) ^ 20 :=
          pow_le_pow_left₀ (by positivity) hR1 20
      _ = Real.exp (20 * (L ^ 10 / 21)) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
      _ ≤ Real.exp (L ^ 10) := by
          refine Real.exp_le_exp.2 ?_
          have : 0 ≤ L ^ 10 := by positivity
          nlinarith
  have hP : primorialBelow (2 ^ J + 1) ≠ 0 := (primorialBelow_pos _).ne'
  have hdecomp : ∀ n : ℤ, cramerSubHB n0 n =
      dpart (primorialBelow (2 ^ J + 1)) (2 ^ J) (2 ^ J') n +
        blockWeight ((primorialBelow (2 ^ J + 1)).divisors.filter (fun q => 2 ^ J' < q)) n := by
    intro n
    have h1 := cramerModel_sub_heathBrown (2 ^ J + 1) J rfl (T := Real.exp L)
      (Real.one_le_exp hL0) (rfl : Nat.log 2 ⌊Real.exp L⌋₊ = J) n
    rw [blockWeight_filter_lt_split hP (Nat.pow_le_pow_right (by norm_num) hJJ) n] at h1
    exact h1
  have hfun : cramerSubHB n0 =
      dpart (primorialBelow (2 ^ J + 1)) (2 ^ J) (2 ^ J') +
        fun n => blockWeight ((primorialBelow (2 ^ J + 1)).divisors.filter
          (fun q => 2 ^ J' < q)) n := funext hdecomp
  obtain ⟨hadd, -, -⟩ := Paper.gowersNormInterval_three_norm_properties N
  -- the first piece
  have hD1 := hK1 (primorialBelow (2 ^ J + 1)) J J' N hJJ hN20
  have hrpow : ((2 : ℝ) ^ (J + 1)) ^ (-(1 : ℝ) / 4) ≤ Real.exp (-(1 / 4 : ℝ) * L) := by
    have h1 : ((2 : ℝ) ^ (J + 1)) ^ (-(1 : ℝ) / 4) ≤ (Real.exp L) ^ (-(1 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_nonpos (Real.exp_pos L) hJ2.le (by norm_num)
    refine h1.trans (le_of_eq ?_)
    rw [Real.rpow_def_of_pos (Real.exp_pos L), Real.log_exp]
    ring_nf
  have hD1' : gowersNormInterval 3 N (dpart (primorialBelow (2 ^ J + 1)) (2 ^ J) (2 ^ J')) ≤
      max K1 0 * Real.exp (-(1 / 4 : ℝ) * L) := by
    refine hD1.trans ?_
    calc K1 * ((2 : ℝ) ^ (J + 1)) ^ (-(1 : ℝ) / 4)
        ≤ max K1 0 * ((2 : ℝ) ^ (J + 1)) ^ (-(1 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max K1 0 * Real.exp (-(1 / 4 : ℝ) * L) :=
          mul_le_mul_of_nonneg_left hrpow (le_max_right _ _)
  -- the second piece
  have havg := avg_sq_tail_le (N := n0) (w := 2 ^ J + 1) (R := 2 ^ J') hL hNexp hw2 hwL'
    (by positivity) hRhi hRlo
  have hD2 : gowersNormInterval 3 N (fun n => blockWeight
      ((primorialBelow (2 ^ J + 1)).divisors.filter (fun q => 2 ^ J' < q)) n) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * L) := by
    refine (Common.gowersNormInterval_three_le N _).trans ?_
    have h1 : (((N : ℕ+) : ℝ)⁻¹ * ∑ n ∈ Icc (1 : ℤ) ((N : ℕ+) : ℕ),
        ‖blockWeight ((primorialBelow (2 ^ J + 1)).divisors.filter
          (fun q => 2 ^ J' < q)) n‖ ^ 2) ≤ Real.exp (-L) := havg
    have h2 : (((N : ℕ+) : ℝ)⁻¹ * ∑ n ∈ Icc (1 : ℤ) ((N : ℕ+) : ℕ),
        ‖blockWeight ((primorialBelow (2 ^ J + 1)).divisors.filter
          (fun q => 2 ^ J' < q)) n‖ ^ 2) ^ ((1 : ℝ) / 2) ≤ (Real.exp (-L)) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    have h3 : (Real.exp (-L)) ^ ((1 : ℝ) / 2) ≤ Real.exp (-(1 / 4 : ℝ) * L) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      refine Real.exp_le_exp.2 ?_
      nlinarith
    linarith
  rw [hfun]
  calc gowersNormInterval 3 N (dpart (primorialBelow (2 ^ J + 1)) (2 ^ J) (2 ^ J') +
        fun n => blockWeight ((primorialBelow (2 ^ J + 1)).divisors.filter
          (fun q => 2 ^ J' < q)) n)
      ≤ _ + _ := hadd _ _
    _ ≤ max K1 0 * Real.exp (-(1 / 4 : ℝ) * L) + 2 * Real.exp (-(1 / 4 : ℝ) * L) :=
        add_le_add hD1' hD2
    _ = (max K1 0 + 2) * Real.exp (-(1 / 4 : ℝ) * L) := by ring


/-- **Small `N`** (`L = (log N)^{1/10} < 40`): the trivial bound `‖f‖_{U³[N]} ≤ 2 sup |f|`. -/
theorem small_bound {N : ℕ+} (hN : 2 ≤ N) (hL : Real.log N ^ ((1 : ℝ) / 10) < 40) :
    gowersNormInterval 3 N (cramerSubHB N) ≤ 4 * Real.exp 45 := by
  set n0 : ℕ := (N : ℕ) with hn0
  have hn2 : 2 ≤ n0 := by exact_mod_cast hN
  have hn1r : (1 : ℝ) ≤ n0 := by exact_mod_cast (by omega : 1 ≤ n0)
  set L : ℝ := Real.log n0 ^ ((1 : ℝ) / 10) with hLdef
  have hL0 : 0 ≤ L := Real.rpow_nonneg (Real.log_nonneg hn1r) _
  obtain ⟨hJ1, hJ2, hw2r, hwL⟩ := cramerLevel_facts hL0
  set J : ℕ := Nat.log 2 ⌊Real.exp L⌋₊ with hJ
  have hw2 : 2 ≤ 2 ^ J + 1 := by have := @Nat.one_le_two_pow J; omega
  have hwL' : ((2 ^ J + 1 : ℕ) : ℝ) ≤ 2 * Real.exp L := by push_cast; exact hwL
  obtain ⟨-, hlog⟩ := log_le_of_le_two_mul_exp hw2 hwL'
  have hB : ∀ n : ℤ, ‖cramerSubHB n0 n‖ ≤ 2 * Real.exp (L + 5) := by
    intro n
    have h1 : cramerModel (2 ^ J + 1) n ≤ Real.exp (L + 5) := by
      refine (cramerModel_le _ hw2 n).trans ?_
      rw [show L + 5 = 5 + L by ring, Real.exp_add]
      exact mul_le_mul_of_nonneg_left (hlog.trans (Real.add_one_le_exp L)) (Real.exp_pos 5).le
    have h2 : ‖heathBrownModel (Real.exp L) n‖ ≤ Real.exp L := by
      rw [heathBrownModel_eq_blockWeight_Icc (Real.one_le_exp hL0)]
      refine (FplusProp21.norm_blockWeight_le_card _ n).trans ?_
      rw [Nat.card_Icc, Nat.add_sub_cancel]
      exact_mod_cast hJ1
    have h3 : ‖((cramerModel (2 ^ J + 1) n : ℝ) : ℂ)‖ ≤ Real.exp (L + 5) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cramerModel_nonneg _ n)]
      exact h1
    have h4 : Real.exp L ≤ Real.exp (L + 5) := Real.exp_le_exp.2 (by linarith)
    calc ‖cramerSubHB n0 n‖ ≤ ‖((cramerModel (2 ^ J + 1) n : ℝ) : ℂ)‖ +
          ‖heathBrownModel (Real.exp L) n‖ := norm_sub_le _ _
      _ ≤ 2 * Real.exp (L + 5) := by linarith
  refine (Common.gowersNormInterval_three_le N _).trans ?_
  have hNpos : (0 : ℝ) < ((N : ℕ+) : ℝ) := by exact_mod_cast N.pos
  have hsum : ∑ n ∈ Icc (1 : ℤ) ((N : ℕ+) : ℕ), ‖cramerSubHB n0 n‖ ^ 2 ≤
      ((N : ℕ+) : ℝ) * (2 * Real.exp (L + 5)) ^ 2 := by
    calc ∑ n ∈ Icc (1 : ℤ) ((N : ℕ+) : ℕ), ‖cramerSubHB n0 n‖ ^ 2
        ≤ ∑ _n ∈ Icc (1 : ℤ) ((N : ℕ+) : ℕ), (2 * Real.exp (L + 5)) ^ 2 :=
          Finset.sum_le_sum fun n _ => pow_le_pow_left₀ (norm_nonneg _) (hB n) 2
      _ = ((N : ℕ+) : ℝ) * (2 * Real.exp (L + 5)) ^ 2 := by
          rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
          have : (((N : ℕ+) : ℕ) : ℤ) + 1 - 1 = ((N : ℕ+) : ℕ) := by ring
          rw [this, Int.toNat_natCast]
  have h1 : (((N : ℕ+) : ℝ)⁻¹ * ∑ n ∈ Icc (1 : ℤ) ((N : ℕ+) : ℕ), ‖cramerSubHB n0 n‖ ^ 2) ≤
      (2 * Real.exp (L + 5)) ^ 2 := by
    rw [inv_mul_le_iff₀ hNpos]
    exact hsum
  have h2 : (((N : ℕ+) : ℝ)⁻¹ * ∑ n ∈ Icc (1 : ℤ) ((N : ℕ+) : ℕ), ‖cramerSubHB n0 n‖ ^ 2) ^
      ((1 : ℝ) / 2) ≤ 2 * Real.exp (L + 5) := by
    calc _ ≤ ((2 * Real.exp (L + 5)) ^ 2) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow (by positivity) h1 (by norm_num)
      _ = 2 * Real.exp (L + 5) := by
          have := Real.pow_rpow_inv_natCast (by positivity : 0 ≤ 2 * Real.exp (L + 5)) (n := 2)
            (by norm_num)
          rwa [show ((2 : ℕ) : ℝ)⁻¹ = (1 : ℝ) / 2 by norm_num] at this
  have h5 : Real.exp (L + 5) ≤ Real.exp 45 := Real.exp_le_exp.2 (by linarith)
  linarith

/-- **The `U³` comparison of the Cramér model with the Heath-Brown model**: there are `c > 0`
and `C` with `‖Λ_{C,w} - Λ_{≤T}‖_{U³[N]} ≤ C exp(-c (log N)^{1/10})` for all `N ≥ 2`, where
`T = exp((log N)^{1/10})` and `w = 2^{⌊log₂ T⌋} + 1` (`cramerLevel`). -/
theorem cramer_heathBrown_U3 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ N : ℕ+, 2 ≤ N →
      gowersNormInterval 3 N
          (fun n => ((cramerModel (cramerLevel N) n : ℝ) : ℂ) -
            heathBrownModel (Real.exp (Real.log N ^ ((1 : ℝ) / 10))) n) ≤
        C * Real.exp (-c * Real.log N ^ ((1 : ℝ) / 10)) := by
  obtain ⟨K, hK0, hK⟩ := exists_large_bound
  refine ⟨1 / 4, by norm_num, K + 4 * Real.exp 55, fun N hN => ?_⟩
  by_cases hL : 40 ≤ Real.log N ^ ((1 : ℝ) / 10)
  · have h := hK N hL
    have h' : gowersNormInterval 3 N (fun n => ((cramerModel (cramerLevel N) n : ℝ) : ℂ) -
        heathBrownModel (Real.exp (Real.log N ^ ((1 : ℝ) / 10))) n) ≤
        K * Real.exp (-(1 / 4 : ℝ) * Real.log N ^ ((1 : ℝ) / 10)) := h
    refine h'.trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith [Real.exp_pos 55]) (Real.exp_pos _).le
  · rw [not_le] at hL
    have h := small_bound hN hL
    have h' : gowersNormInterval 3 N (fun n => ((cramerModel (cramerLevel N) n : ℝ) : ℂ) -
        heathBrownModel (Real.exp (Real.log N ^ ((1 : ℝ) / 10))) n) ≤ 4 * Real.exp 45 := h
    refine h'.trans ?_
    have hL0 : 0 ≤ Real.log N ^ ((1 : ℝ) / 10) :=
      Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast N.pos)) _
    have h1 : Real.exp (-10) ≤ Real.exp (-(1 / 4 : ℝ) * Real.log N ^ ((1 : ℝ) / 10)) :=
      Real.exp_le_exp.2 (by nlinarith)
    calc 4 * Real.exp 45 = (4 * Real.exp 55) * Real.exp (-10) := by
          rw [mul_assoc, ← Real.exp_add]; norm_num
      _ ≤ (K + 4 * Real.exp 55) * Real.exp (-(1 / 4 : ℝ) * Real.log N ^ ((1 : ℝ) / 10)) := by
          refine mul_le_mul (by linarith) h1 (Real.exp_pos _).le (by positivity)

end PrimeCarleson.Proof.Fplus31

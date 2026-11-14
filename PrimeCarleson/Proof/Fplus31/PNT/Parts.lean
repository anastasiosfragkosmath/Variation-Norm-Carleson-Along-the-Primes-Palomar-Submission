module

public import PrimeCarleson.Proof.Fplus31.PNT.Budget

/-!
# Three of the four cases of the assembly

Three of the four cases of the assembly of the prime number theorem in progressions
(`PNTSW/Assembly.lean`); the fourth, `r < w` with `gcd(a, r) = 1`, is `pnt_part_sw` of
`PNTSW/Target.lean`. With `L = (log N)^{1/10}` (`log N = L^{10}`) and the target `N exp(-L/3)`
(`c = 1/3`), for a progression `P = apSet r a lo hi ⊆ [1, N]` and a Cramér level
`w ∈ [e^L / 2, e^L + 1]`:

* `trivial_part`: `r ≥ e^{L/2}`: `|∑_P (Λ - Λ_{C,w})| ≤ N e^{-L/3}` from `Λ ≤ log N`,
  `Λ_{C,w} ≤ e⁵ log w`, `|P| ≤ N/r + 1`;
* `noncoprime_part`: `r < w` and `gcd(a, r) > 1`: `Λ_{C,w} = 0` on `P`, `∑_P Λ ≤ log N`;
* `brun_part`: the same for `Λ_{C,w}` from `brun_ap` with `m = ⌊L⁹/4⌋ + 1`, `≤ 2 N e^{-L/3} / 3`.

Each part takes the numerical thresholds `hG1`-`hG4` (polynomial in `L` against `e^{cL}`) as
hypotheses; `PNTSW.Assembly` discharges them for large `L`.
-/

@[expose] public noncomputable section

open ArithmeticFunction

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

theorem log_nat_eq_exp {N : ℕ} {L : ℝ} (hN : Real.log N = L ^ 10) (hN1 : 1 ≤ N) :
    (N : ℝ) = Real.exp (L ^ 10) := by
  rw [← hN, Real.exp_log (by exact_mod_cast hN1)]

/-- `N e^{-L/3} = e^{L^{10} - L/3}`. -/
theorem target_eq {N : ℕ} {L : ℝ} (hN : Real.log N = L ^ 10) (hN1 : 1 ≤ N) :
    (N : ℝ) * Real.exp (-(1 / 3) * L) = Real.exp (L ^ 10 - L / 3) := by
  rw [log_nat_eq_exp hN hN1, ← Real.exp_add]
  ring_nf

theorem one_le_nat_of_log {N : ℕ} {L : ℝ} (hL : 4 ≤ L) (hN : Real.log N = L ^ 10) : 1 ≤ N := by
  by_contra hN1
  have : N = 0 := by omega
  subst this
  simp at hN
  have : (0 : ℝ) < L ^ 10 := by positivity
  linarith

theorem le_pow_ten {L : ℝ} (hL : 4 ≤ L) (c : ℝ) (hc : c ≤ 262144) : c * L ≤ L ^ 10 := by
  have h1 : (4 : ℝ) ^ 9 ≤ L ^ 9 := pow_le_pow_left₀ (by norm_num) hL 9
  have h2 : L ^ 10 = L ^ 9 * L := by ring
  have h0 : (0 : ℝ) ≤ L := by linarith
  linarith only [mul_le_mul_of_nonneg_right h1 h0, mul_le_mul_of_nonneg_right hc h0, h2]

theorem trivial_part {L : ℝ} (hL : 4 ≤ L) {N : ℕ} (hN : Real.log N = L ^ 10) {w : ℕ}
    (hw1 : Real.exp L / 2 ≤ w) (hw2 : (w : ℝ) ≤ Real.exp L + 1)
    (hG1 : 2 * (1 + 2 * Real.exp 5) * L ^ 10 ≤ Real.exp ((1 / 6) * L))
    {r : ℕ} (hr : 1 ≤ r) (hrL : Real.exp (L / 2) ≤ r) (a : ℤ) {lo hi : ℕ} (h : lo ≤ hi)
    (hhi : hi ≤ N) :
    |∑ n ∈ apSet r a lo hi, (Λ n.toNat - cramerModel w n)| ≤
      N * Real.exp (-(1 / 3) * L) := by
  obtain ⟨hw2', hlw0, hlw, _⟩ := level_facts hL hw1 hw2
  have hN1 := one_le_nat_of_log hL hN
  rw [Finset.sum_sub_distrib]
  set A := ∑ n ∈ apSet r a lo hi, Λ n.toNat with hA
  set B := ∑ n ∈ apSet r a lo hi, cramerModel w n with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun n _ => vonMangoldt_nonneg
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun n _ => cramerModel_nonneg w n
  have hAle := vonMangoldt_apSet_le hr a h hhi
  have hBle := cramerModel_apSet_le hr hw2' a h hhi
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  set X : ℝ := N * Real.exp (-(L / 2)) with hX
  have hX1 : 1 ≤ X := by
    rw [hX, log_nat_eq_exp hN hN1, ← Real.exp_add]
    exact Real.one_le_exp (by linarith only [le_pow_ten hL 1 (by norm_num), hL])
  have hNr : (N : ℝ) / r ≤ X := by
    rw [hX, Real.exp_neg, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hNpos.le (Real.exp_pos _) hrL
  have hlogN : Real.log N = L ^ 10 := hN
  have hY : Real.log N + Real.exp 5 * Real.log w ≤ (1 + 2 * Real.exp 5) * L ^ 10 := by
    have h1 : L + 1 ≤ 2 * L ^ 10 := by linarith only [le_pow_ten hL 1 (by norm_num), hL]
    have h5 : 0 < Real.exp 5 := Real.exp_pos 5
    linarith only [hN, mul_le_mul_of_nonneg_left hlw h5.le, mul_nonneg h5.le (sub_nonneg.2 h1)]
  have hlogw : 0 ≤ Real.exp 5 * Real.log w := by positivity
  have hsum : A + B ≤ (X + 1) * ((1 + 2 * Real.exp 5) * L ^ 10) := by
    calc A + B ≤ ((N : ℝ) / r + 1) * Real.log N +
          ((N : ℝ) / r + 1) * (Real.exp 5 * Real.log w) := add_le_add hAle hBle
      _ = ((N : ℝ) / r + 1) * (Real.log N + Real.exp 5 * Real.log w) := by ring
      _ ≤ (X + 1) * ((1 + 2 * Real.exp 5) * L ^ 10) := by
          refine mul_le_mul (by linarith) hY (by positivity) (by linarith)
  have hfin : (X + 1) * ((1 + 2 * Real.exp 5) * L ^ 10) ≤
      N * Real.exp (-(1 / 3) * L) := by
    have e1 : (N : ℝ) * Real.exp (-(1 / 3) * L) = X * Real.exp ((1 / 6) * L) := by
      rw [hX, mul_assoc, ← Real.exp_add]
      ring_nf
    rw [e1]
    have hX0 : 0 ≤ X := by linarith
    calc (X + 1) * ((1 + 2 * Real.exp 5) * L ^ 10) ≤ (2 * X) * ((1 + 2 * Real.exp 5) * L ^ 10) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = X * (2 * (1 + 2 * Real.exp 5) * L ^ 10) := by ring
      _ ≤ X * Real.exp ((1 / 6) * L) := mul_le_mul_of_nonneg_left hG1 hX0
  rw [abs_le]
  constructor <;> linarith only [hsum, hfin, hA0, hB0]

theorem noncoprime_part {L : ℝ} (hL : 4 ≤ L) {N : ℕ} (hN : Real.log N = L ^ 10) {w : ℕ}
    (hG4 : 6 * Real.exp 5 * L ^ 10 ≤ Real.exp (1 * L))
    {r : ℕ} (hr : 1 ≤ r) (hrw : r < w) {a : ℤ} (hna : ¬ IsCoprime a (r : ℤ)) {lo hi : ℕ}
    (hhi : hi ≤ N) :
    |∑ n ∈ apSet r a lo hi, (Λ n.toNat - cramerModel w n)| ≤
      N * Real.exp (-(1 / 3) * L) := by
  have hN1 := one_le_nat_of_log hL hN
  rw [Finset.sum_sub_distrib]
  have hB : ∑ n ∈ apSet r a lo hi, cramerModel w n = 0 :=
    Finset.sum_eq_zero fun n hn => cramerModel_eq_zero_of_not_coprime hr hrw hna hn
  rw [hB, sub_zero]
  have hA0 : 0 ≤ ∑ n ∈ apSet r a lo hi, Λ n.toNat :=
    Finset.sum_nonneg fun n _ => vonMangoldt_nonneg
  have hA := vonMangoldt_apSet_noncoprime_le (lo := lo) hna hhi hN1
  rw [abs_of_nonneg hA0, target_eq hN hN1]
  have h1 : L ^ 10 ≤ Real.exp L := by
    have : (1 : ℝ) ≤ 6 * Real.exp 5 := by
      have := Real.add_one_le_exp (5 : ℝ)
      linarith only [this]
    have hp : 0 ≤ L ^ 10 := by positivity
    have hG := hG4
    rw [one_mul] at hG
    linarith only [mul_le_mul_of_nonneg_right this hp, hG]
  have h2 : L ≤ L ^ 10 - L / 3 := by linarith only [le_pow_ten hL (4 / 3) (by norm_num)]
  calc _ ≤ Real.log N := hA
    _ = L ^ 10 := hN
    _ ≤ Real.exp L := h1
    _ ≤ _ := Real.exp_le_exp.mpr h2

theorem pow_nine_ge {L : ℝ} (hL : 4 ≤ L) (c : ℝ) (hc : c ≤ 65536) : c * L ≤ L ^ 9 := by
  have h1 : (4 : ℝ) ^ 8 ≤ L ^ 8 := pow_le_pow_left₀ (by norm_num) hL 8
  have h2 : L ^ 9 = L ^ 8 * L := by ring
  have h0 : (0 : ℝ) ≤ L := by linarith
  linarith only [mul_le_mul_of_nonneg_right h1 h0, mul_le_mul_of_nonneg_right hc h0, h2]

theorem exp_two_lt_eight : Real.exp 2 < 8 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h0 := Real.exp_pos 1
  rw [e]
  linarith only [mul_self_lt_mul_self h0.le h]

/-- First Brun term: `W · 2 e^S (S^m/m!) (D/r) ≤ T/3` (abstract in the real quantities). -/
theorem brun_term1 {L : ℝ} (hL : 4 ≤ L) {W E F Dr Nn : ℝ}
    (hW : W ≤ Real.exp 5 * (L + 1)) (hE : E ≤ Real.exp 4 * (L + 1)) (hE0 : 0 ≤ E)
    (hF0 : 0 ≤ F) (hF : F ≤ Real.exp (-(L ^ 9 / 4))) (hD0 : 0 ≤ Dr) (hD : Dr ≤ Nn)
    (hN0 : 0 ≤ Nn) (hG3 : 24 * Real.exp 9 * L ^ 2 ≤ Real.exp (1 * L)) :
    W * (2 * E * F * Dr) ≤ (1 / 3) * (Real.exp (-(L / 3)) * Nn) := by
  have hL0 : 0 ≤ L := by linarith
  have hQ0 : 0 ≤ Real.exp (-(L ^ 9 / 4)) := (Real.exp_pos _).le
  have a1 : 2 * E ≤ 2 * (Real.exp 4 * (L + 1)) := by linarith
  have a2 : 2 * E * F ≤ 2 * (Real.exp 4 * (L + 1)) * Real.exp (-(L ^ 9 / 4)) :=
    mul_le_mul a1 hF hF0 (by positivity)
  have a3 : 2 * E * F * Dr ≤ 2 * (Real.exp 4 * (L + 1)) * Real.exp (-(L ^ 9 / 4)) * Nn :=
    mul_le_mul a2 hD hD0 (by positivity)
  have a4 : W * (2 * E * F * Dr) ≤ Real.exp 5 * (L + 1) *
      (2 * (Real.exp 4 * (L + 1)) * Real.exp (-(L ^ 9 / 4)) * Nn) :=
    mul_le_mul hW a3 (by positivity) (by positivity)
  refine a4.trans ?_
  have a6 : Real.exp 5 * (L + 1) *
      (2 * (Real.exp 4 * (L + 1)) * Real.exp (-(L ^ 9 / 4)) * Nn) =
      (2 * Real.exp 9 * (L + 1) ^ 2) * Real.exp (-(L ^ 9 / 4)) * Nn := by
    have : Real.exp 9 = Real.exp 5 * Real.exp 4 := by rw [← Real.exp_add]; norm_num
    rw [this]; ring
  rw [a6]
  have hG := hG3
  rw [one_mul] at hG
  have a5 : 2 * Real.exp 9 * (L + 1) ^ 2 ≤ (1 / 3) * Real.exp L := by
    have h1 : (L + 1) ^ 2 ≤ 4 * L ^ 2 := by
      linarith only [mul_le_mul_of_nonneg_right hL hL0, hL]
    have h2 : 2 * Real.exp 9 * (L + 1) ^ 2 ≤ 2 * Real.exp 9 * (4 * L ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have a7 : Real.exp L * Real.exp (-(L ^ 9 / 4)) ≤ Real.exp (-(L / 3)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    linarith [pow_nine_ge hL (16 / 3) (by norm_num)]
  calc 2 * Real.exp 9 * (L + 1) ^ 2 * Real.exp (-(L ^ 9 / 4)) * Nn
      ≤ (1 / 3) * Real.exp L * Real.exp (-(L ^ 9 / 4)) * Nn :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right a5 hQ0) hN0
    _ = (1 / 3) * (Real.exp L * Real.exp (-(L ^ 9 / 4))) * Nn := by ring
    _ ≤ (1 / 3) * Real.exp (-(L / 3)) * Nn :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left a7 (by norm_num)) hN0
    _ = _ := by ring

/-- Second Brun term: `W · 2 m w^m ≤ T/3` with `T = e^{L^{10} - L/3}`. -/
theorem brun_term2 {L : ℝ} (hL : 4 ≤ L) {W m wp : ℝ}
    (hW : W ≤ Real.exp 5 * (L + 1)) (hm0 : 0 ≤ m) (hm : 2 * m ≤ L ^ 9) (hwp0 : 0 ≤ wp)
    (hwp : wp ≤ Real.exp (L ^ 10 / 2)) (hG4 : 6 * Real.exp 5 * L ^ 10 ≤ Real.exp (1 * L)) :
    W * (2 * m * wp) ≤ (1 / 3) * Real.exp (L ^ 10 - L / 3) := by
  have hL0 : 0 ≤ L := by linarith
  have b2 : 2 * m * wp ≤ L ^ 9 * Real.exp (L ^ 10 / 2) :=
    mul_le_mul hm hwp hwp0 (by positivity)
  have b3 : W * (2 * m * wp) ≤ Real.exp 5 * (L + 1) * (L ^ 9 * Real.exp (L ^ 10 / 2)) :=
    mul_le_mul hW b2 (by positivity) (by positivity)
  refine b3.trans ?_
  have hG := hG4
  rw [one_mul] at hG
  have b4 : Real.exp 5 * (L + 1) * L ^ 9 ≤ (1 / 3) * Real.exp L := by
    have h1 : (L + 1) * L ^ 9 ≤ 2 * L ^ 10 := by
      linarith only [mul_nonneg (pow_nonneg hL0 9) (by linarith only [hL] : 0 ≤ L - 1)]
    have h2 : Real.exp 5 * ((L + 1) * L ^ 9) ≤ Real.exp 5 * (2 * L ^ 10) :=
      mul_le_mul_of_nonneg_left h1 (Real.exp_pos 5).le
    linarith
  have b5 : Real.exp L * Real.exp (L ^ 10 / 2) ≤ Real.exp (L ^ 10 - L / 3) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    linarith [le_pow_ten hL (8 / 3) (by norm_num)]
  calc Real.exp 5 * (L + 1) * (L ^ 9 * Real.exp (L ^ 10 / 2))
      = (Real.exp 5 * (L + 1) * L ^ 9) * Real.exp (L ^ 10 / 2) := by ring
    _ ≤ (1 / 3) * Real.exp L * Real.exp (L ^ 10 / 2) :=
        mul_le_mul_of_nonneg_right b4 (Real.exp_pos _).le
    _ = (1 / 3) * (Real.exp L * Real.exp (L ^ 10 / 2)) := by ring
    _ ≤ (1 / 3) * Real.exp (L ^ 10 - L / 3) := mul_le_mul_of_nonneg_left b5 (by norm_num)

/-- The bounds on `e^S` and `S^m/m!` for `m = ⌊L⁹/4⌋ + 1`, as needed by `brun_ap`. -/
theorem brun_factorial_part {L : ℝ} (hL : 4 ≤ L) {w : ℕ} (hw2' : 2 ≤ w)
    (hlw0 : 0 < Real.log w) (hlw : Real.log w ≤ L + 1) :
    Real.exp (∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p) ≤ Real.exp 4 * (L + 1) ∧
    (∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p) ^ (⌊L ^ 9 / 4⌋₊ + 1) /
        ((⌊L ^ 9 / 4⌋₊ + 1).factorial : ℝ) ≤ Real.exp (-(L ^ 9 / 4)) := by
  have hL0 : 0 ≤ L := by linarith
  set k : ℕ := ⌊L ^ 9 / 4⌋₊ with hk
  have hm1 : L ^ 9 / 4 < ((k : ℝ) + 1) := Nat.lt_floor_add_one _
  have hSm := PrimeCarleson.Proof.Common.sum_primesBelow_inv_le_log_log hw2'
  have hS0 : 0 ≤ ∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p :=
    Finset.sum_nonneg fun p _ => by positivity
  generalize (∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p) = S at hSm hS0 ⊢
  have hloglog : Real.log (Real.log w) ≤ L := by
    calc Real.log (Real.log w) ≤ Real.log (L + 1) := Real.log_le_log hlw0 hlw
      _ ≤ (L + 1) - 1 := Real.log_le_sub_one_of_pos (by linarith)
      _ = L := by ring
  have hSL : S ≤ L + 4 := by linarith
  refine ⟨?_, ?_⟩
  · calc Real.exp S ≤ Real.exp (Real.log (Real.log w) + 4) := Real.exp_le_exp.mpr hSm
      _ = Real.log w * Real.exp 4 := by rw [Real.exp_add, Real.exp_log hlw0]
      _ ≤ (L + 1) * Real.exp 4 := mul_le_mul_of_nonneg_right hlw (Real.exp_pos 4).le
      _ = _ := by ring
  · have hcond : S * Real.exp 2 ≤ ((k + 1 : ℕ) : ℝ) := by
      have h2 := exp_two_lt_eight
      have h3 := pow_nine_ge hL 64 (by norm_num)
      push_cast
      have h4 : S * Real.exp 2 ≤ (L + 4) * 8 :=
        mul_le_mul hSL h2.le (Real.exp_pos 2).le (by linarith)
      linarith
    have hfac := pow_div_factorial_le_exp_neg hS0 (Nat.succ_pos k) hcond
    refine hfac.trans (Real.exp_le_exp.mpr ?_)
    push_cast
    linarith

/-- `w^m ≤ e^{L^{10}/2}` and `2 m ≤ L⁹` for `m = ⌊L⁹/4⌋ + 1` and `w ≤ e^{L+1}`. -/
theorem brun_w_part {L : ℝ} (hL : 4 ≤ L) {w : ℕ} (hwe : (w : ℝ) ≤ Real.exp (L + 1)) :
    (w : ℝ) ^ (⌊L ^ 9 / 4⌋₊ + 1) ≤ Real.exp (L ^ 10 / 2) ∧
      2 * ((⌊L ^ 9 / 4⌋₊ : ℝ) + 1) ≤ L ^ 9 := by
  have hL0 : 0 ≤ L := by linarith
  set k : ℕ := ⌊L ^ 9 / 4⌋₊ with hk
  have hm2 : ((k : ℝ) + 1) ≤ L ^ 9 / 4 + 1 := by
    have := Nat.floor_le (show 0 ≤ L ^ 9 / 4 by positivity)
    linarith
  have h9 : 12 ≤ L ^ 9 := by linarith [pow_nine_ge hL 12 (by norm_num)]
  have hk1 : ((k : ℝ) + 1) ≤ L ^ 9 / 3 := by linarith
  refine ⟨?_, by linarith⟩
  have h10 : 4 * L ^ 9 ≤ L ^ 10 := by
    have : L ^ 10 = L ^ 9 * L := by ring
    rw [this]
    linarith only [mul_le_mul_of_nonneg_left hL (pow_nonneg hL0 9)]
  have hexpo : ((k + 1 : ℕ) : ℝ) * (L + 1) ≤ L ^ 10 / 2 := by
    push_cast
    have h1 : ((k : ℝ) + 1) * (L + 1) ≤ L ^ 9 / 3 * (L + 1) :=
      mul_le_mul_of_nonneg_right hk1 (by linarith)
    have h2 : L ^ 9 / 3 * (L + 1) = L ^ 10 / 3 + L ^ 9 / 3 := by ring
    linarith
  calc (w : ℝ) ^ (k + 1) ≤ Real.exp (L + 1) ^ (k + 1) :=
        pow_le_pow_left₀ (by positivity) hwe (k + 1)
    _ = Real.exp (((k + 1 : ℕ) : ℝ) * (L + 1)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hexpo

theorem brun_part {L : ℝ} (hL : 4 ≤ L) {N : ℕ} (hN : Real.log N = L ^ 10) {w : ℕ}
    (hw1 : Real.exp L / 2 ≤ w) (hw2 : (w : ℝ) ≤ Real.exp L + 1)
    (hG3 : 24 * Real.exp 9 * L ^ 2 ≤ Real.exp (1 * L))
    (hG4 : 6 * Real.exp 5 * L ^ 10 ≤ Real.exp (1 * L))
    {r : ℕ} (hr : 1 ≤ r) (hrw : r < w) {a : ℤ} (ha : IsCoprime a (r : ℤ)) {lo hi : ℕ}
    (h : lo ≤ hi) (hhi : hi ≤ N) :
    |∑ n ∈ apSet r a lo hi, cramerModel w n - ((hi : ℝ) - lo) / (Nat.totient r : ℝ)| ≤
      (2 / 3) * (N * Real.exp (-(1 / 3) * L)) := by
  obtain ⟨hw2', hlw0, hlw, hwe⟩ := level_facts hL hw1 hw2
  have hN1 := one_le_nat_of_log hL hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hT : (N : ℝ) * Real.exp (-(1 / 3) * L) = Real.exp (L ^ 10 - L / 3) := target_eq hN hN1
  have hT' : (N : ℝ) * Real.exp (-(1 / 3) * L) = Real.exp (-(L / 3)) * N := by
    rw [mul_comm]; ring_nf
  have hbrun := brun_ap w (⌊L ^ 9 / 4⌋₊) r hw2' hrw hr ha h
  obtain ⟨hexpS, hfac'⟩ := brun_factorial_part hL hw2' hlw0 hlw
  obtain ⟨hwpow, hm⟩ := brun_w_part hL hwe
  have hS0 : 0 ≤ ∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p :=
    Finset.sum_nonneg fun p _ => by positivity
  have hW := primorialBelow_div_totient_le w hw2'
  generalize (∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p) = S at hbrun hexpS hfac' hS0
  generalize (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) = W at hbrun hW
  generalize ⌊L ^ 9 / 4⌋₊ = k at hbrun hfac' hwpow hm
  have hW' : W ≤ Real.exp 5 * (L + 1) :=
    hW.trans (mul_le_mul_of_nonneg_left hlw (Real.exp_pos 5).le)
  have hD : ((hi : ℝ) - lo) / r ≤ N := by
    have hr0 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have h0 : (0 : ℝ) ≤ (hi : ℝ) - lo := by
      have : (lo : ℝ) ≤ hi := by exact_mod_cast h
      linarith
    have h1 : (hi : ℝ) - lo ≤ N := by
      have : (hi : ℝ) ≤ N := by exact_mod_cast hhi
      have : (0 : ℝ) ≤ lo := by positivity
      linarith
    exact (div_le_self h0 hr0).trans h1
  have hD0 : 0 ≤ ((hi : ℝ) - lo) / r := by
    have : (lo : ℝ) ≤ hi := by exact_mod_cast h
    have : (0 : ℝ) < r := by exact_mod_cast hr
    positivity
  have hfn : 0 ≤ S ^ (k + 1) / ((k + 1).factorial : ℝ) := by positivity
  have bT1 := brun_term1 hL hW' hexpS (Real.exp_pos S).le hfn hfac' hD0 hD hNpos.le hG3
  have bT2 := brun_term2 hL hW' (m := (k : ℝ) + 1) (by positivity) hm
    (wp := (w : ℝ) ^ (k + 1)) (by positivity) hwpow hG4
  rw [hT'] 
  have e1 : 2 * Real.exp S * S ^ (k + 1) / ((k + 1).factorial : ℝ) * (((hi : ℝ) - lo) / r) =
      2 * Real.exp S * (S ^ (k + 1) / ((k + 1).factorial : ℝ)) * (((hi : ℝ) - lo) / r) := by
    ring
  rw [e1] at hbrun
  have bT2' : W * (2 * ((k : ℝ) + 1) * (w : ℝ) ^ (k + 1)) ≤
      (1 / 3) * (Real.exp (-(L / 3)) * N) := by
    rw [← hT', hT]; exact bT2
  calc _ ≤ _ := hbrun
    _ = W * (2 * Real.exp S * (S ^ (k + 1) / ((k + 1).factorial : ℝ)) *
          (((hi : ℝ) - lo) / r)) + W * (2 * ((k : ℝ) + 1) * (w : ℝ) ^ (k + 1)) := by ring
    _ ≤ (1 / 3) * (Real.exp (-(L / 3)) * N) + (1 / 3) * (Real.exp (-(L / 3)) * N) :=
        add_le_add bT1 bT2'
    _ = _ := by ring

end PrimeCarleson.Proof.Fplus31

module

public import PrimeCarleson.Proof.Fplus31.Cramer.Approx
public import PrimeCarleson.Proof.Fplus31.Cramer.Ramanujan
public import PrimeCarleson.Frozen.HeathBrownModel
public import PrimeCarleson.Proof.Paper.P2.NormProperties

/-!
# Cramér–Heath-Brown comparison, step 1: the decomposition of `Λ_{C,w} - Λ_{≤T}` into dyadic blocks

The comparison of the Cramér model with the Heath-Brown model in the proof of [F+] Proposition 3.1:
with `T' = 2^J`, `J = ⌊log₂ T⌋`, and `w = T' + 1`, the Cramér model `Λ_{C,w}` and the
Heath-Brown model `Λ_{≤T}` differ by `D = ∑_{q ∣ P(w), q > T'} μ(q) c_q / φ(q)`.

* `ramWeight n q = μ(q)/φ(q) c_q(n)`, the summand of the `blockWeight`;
  `ramR q n` is the Ramanujan sum as a real number (`ramanujanSum_eq_ofReal`);
* `heathBrownModel_eq_blockWeight_Icc`: `Λ_{≤T} = blockWeight [1, 2^{⌊log₂ T⌋}]`
  (the dyadic blocks `(2^j/2, 2^j]`, `2^j ≤ T`, tile `[1, T']`: `sum_range_two_pow_div`);
* `cramerModel_sub_heathBrown`: `Λ_{C,w} - Λ_{≤T} = blockWeight {q ∣ P(w) : q > 2^J}` (a
  squarefree `q ≤ T' < w` divides `P(w)`, a non squarefree `q` has `μ(q) = 0`);
* `dpart P l u` (the block weight of the divisors of `P` in `(l, u]`), `dpart_two_pow` (dyadic
  tiling), `blockWeight_filter_lt_split` (splitting off the tail above `u`);
* `gowersNormInterval_sum_le`: the `U³[N]` norm is subadditive over finite sums.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open PrimeCarleson

/-- The summand `μ(q)/φ(q) · c_q(n)` of the `blockWeight`. -/
def ramWeight (n : ℤ) (q : ℕ) : ℂ :=
  (((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ) : ℂ) * ramanujanSum q n

/-- The `blockWeight` is the sum of the summands `ramWeight`. -/
theorem blockWeight_eq_sum_ramWeight (B : Finset ℕ) (n : ℤ) :
    blockWeight B n = ∑ q ∈ B, ramWeight n q := rfl

/-- The Ramanujan sum is real: `c_q(n)` as a real number. -/
def ramR (q : ℕ) (n : ℤ) : ℝ :=
  ∑ f ∈ q.divisors with ((f : ℕ) : ℤ) ∣ n,
    (f : ℝ) * ((ArithmeticFunction.moebius (q / f) : ℤ) : ℝ)

/-- `c_q(n)` equals the real number `ramR q n`. -/
theorem ramanujanSum_eq_ofReal (q : ℕ) (n : ℤ) : ramanujanSum q n = (ramR q n : ℂ) := by
  rw [Goal0.ramanujanSum_eq_sum_divisors, ramR]
  push_cast
  rfl


/-- The weight `μ(q)/φ(q)`. -/
def mobTot (q : ℕ) : ℝ := ((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ)

/-- `μ(q)/φ(q) · c_q(n)` is a real number. -/
theorem ramWeight_eq_ofReal (n : ℤ) (q : ℕ) :
    ramWeight n q = ((mobTot q * ramR q n : ℝ) : ℂ) := by
  rw [ramWeight, mobTot, ramanujanSum_eq_ofReal]
  push_cast
  rfl


/-- Dyadic partition: the blocks `(2^j/2, 2^j]`, `j ∈ (a, b]`, tile `(2^a, 2^b]`. -/
theorem sum_Ioc_two_pow_div {M : Type*} [AddCommMonoid M] (f : ℕ → M) {a b : ℕ} (hab : a ≤ b) :
    ∑ j ∈ Ioc a b, ∑ q ∈ Ioc (2 ^ j / 2) (2 ^ j), f q =
      ∑ q ∈ Ioc (2 ^ a) (2 ^ b), f q := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, ih]
    have h2 : 2 ^ (b + 1) / 2 = 2 ^ b := by
      rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    rw [h2]
    exact Finset.sum_Ioc_consecutive f (Nat.pow_le_pow_right (by norm_num) hab)
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ b))

/-- The blocks `(2^j/2, 2^j]`, `j ≤ b`, tile `(0, 2^b]`. -/
theorem sum_range_two_pow_div {M : Type*} [AddCommMonoid M] (f : ℕ → M) (b : ℕ) :
    ∑ j ∈ range (b + 1), ∑ q ∈ Ioc (2 ^ j / 2) (2 ^ j), f q =
      ∑ q ∈ Ioc 0 (2 ^ b), f q := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, ih]
    have h2 : 2 ^ (b + 1) / 2 = 2 ^ b := by
      rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    rw [h2]
    exact Finset.sum_Ioc_consecutive f (Nat.zero_le _)
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ b))

/-- **The Heath-Brown model is the block weight of `[1, T']`**, `T' = 2^{⌊log₂ T⌋}`. -/
theorem heathBrownModel_eq_blockWeight_Icc {T : ℝ} (hT : 1 ≤ T) (n : ℤ) :
    heathBrownModel T n = blockWeight (Icc 1 (2 ^ Nat.log 2 ⌊T⌋₊)) n := by
  have hm : ⌊T⌋₊ ≠ 0 := (Nat.floor_pos.2 hT).ne'
  have hfilter : (range (⌊T⌋₊ + 1)).filter (fun j => (2 : ℝ) ^ j ≤ T) =
      range (Nat.log 2 ⌊T⌋₊ + 1) := by
    ext j
    simp only [mem_filter, mem_range, Nat.lt_succ_iff]
    rw [Nat.le_log_iff_pow_le (by norm_num) hm]
    have h : 2 ^ j ≤ ⌊T⌋₊ ↔ (2 : ℝ) ^ j ≤ T := by
      rw [Nat.le_floor_iff (by linarith)]
      push_cast
      rfl
    rw [← h]
    constructor
    · exact fun hh => hh.2
    · intro hh
      refine ⟨?_, hh⟩
      exact (Nat.lt_two_pow_self.le).trans hh
  unfold heathBrownModel
  rw [hfilter]
  simp only [blockWeight_eq_sum_ramWeight]
  rw [sum_range_two_pow_div (fun q => ramWeight n q)]
  rfl



/-- The block weight of the divisors of `P` lying in `(l, u]`. -/
def dpart (P l u : ℕ) (n : ℤ) : ℂ := blockWeight ((Ioc l u).filter (· ∣ P)) n

/-- `dpart` as a sum over `(l, u]` with a divisibility indicator. -/
theorem dpart_eq_sum (P l u : ℕ) (n : ℤ) :
    dpart P l u n = ∑ q ∈ Ioc l u, if q ∣ P then ramWeight n q else 0 := by
  rw [dpart, blockWeight_eq_sum_ramWeight, Finset.sum_filter]

/-- The dyadic blocks `(2^j/2, 2^j]`, `a < j ≤ b`, tile `(2^a, 2^b]`. -/
theorem dpart_two_pow (P : ℕ) {a b : ℕ} (hab : a ≤ b) (n : ℤ) :
    dpart P (2 ^ a) (2 ^ b) n = ∑ j ∈ Ioc a b, dpart P (2 ^ j / 2) (2 ^ j) n := by
  simp only [dpart_eq_sum]
  exact (sum_Ioc_two_pow_div (fun q => if q ∣ P then ramWeight n q else 0) hab).symm

/-- `μ(q) = 0` for non squarefree `q`, hence the weight vanishes. -/
theorem ramWeight_eq_zero_of_not_squarefree {q : ℕ} (hq : ¬ Squarefree q) (n : ℤ) :
    ramWeight n q = 0 := by
  rw [ramWeight, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]
  simp

/-- **The Cramér model minus the Heath-Brown model** (Ramanujan identity and the divisor
condition): with `w = 2^J + 1`, `Λ_{C,w} - Λ_{≤T} = ∑_{q ∣ P(w), q > 2^J} μ(q) c_q / φ(q)`. -/
theorem cramerModel_sub_heathBrown (w J : ℕ) (hw : w = 2 ^ J + 1) {T : ℝ} (hT : 1 ≤ T)
    (hJ : Nat.log 2 ⌊T⌋₊ = J) (n : ℤ) :
    (cramerModel w n : ℂ) - heathBrownModel T n =
      blockWeight ((primorialBelow w).divisors.filter (fun q => 2 ^ J < q)) n := by
  have hP : primorialBelow w ≠ 0 := (primorialBelow_pos w).ne'
  rw [cramerModel_eq_blockWeight, heathBrownModel_eq_blockWeight_Icc hT, hJ]
  simp only [blockWeight_eq_sum_ramWeight]
  have hsplit := Finset.sum_filter_add_sum_filter_not (primorialBelow w).divisors
    (fun q => q ≤ 2 ^ J) (fun q => ramWeight n q)
  have hlow : ∑ q ∈ Icc 1 (2 ^ J), ramWeight n q =
      ∑ q ∈ (primorialBelow w).divisors.filter (fun q => q ≤ 2 ^ J), ramWeight n q := by
    symm
    refine Finset.sum_subset ?_ ?_
    · intro q hq
      rw [mem_filter, Nat.mem_divisors] at hq
      rw [mem_Icc]
      exact ⟨Nat.pos_of_dvd_of_pos hq.1.1 (primorialBelow_pos w), hq.2⟩
    · intro q hq hq'
      rw [mem_Icc] at hq
      by_cases hsq : Squarefree q
      · exfalso
        apply hq'
        rw [mem_filter, Nat.mem_divisors]
        exact ⟨⟨dvd_primorialBelow_of_squarefree hsq (by omega), hP⟩, hq.2⟩
      · exact ramWeight_eq_zero_of_not_squarefree hsq n
  rw [hlow, ← hsplit]
  simp only [not_le]
  ring


/-- Splitting the divisors of `P` above `l` at `u ≥ l`: the middle block `(l, u]` and the tail. -/
theorem blockWeight_filter_lt_split {P : ℕ} (hP : P ≠ 0) {l u : ℕ} (hlu : l ≤ u) (n : ℤ) :
    blockWeight (P.divisors.filter (fun q => l < q)) n =
      dpart P l u n + blockWeight (P.divisors.filter (fun q => u < q)) n := by
  have hset : P.divisors.filter (fun q => l < q) =
      (Ioc l u).filter (· ∣ P) ∪ P.divisors.filter (fun q => u < q) := by
    ext q
    simp only [mem_filter, mem_union, Nat.mem_divisors, mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases h4 : q ≤ u
      · exact Or.inl ⟨⟨h3, h4⟩, h1⟩
      · exact Or.inr ⟨⟨h1, h2⟩, by omega⟩
    · rintro (⟨⟨h3, h4⟩, h1⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨⟨h1, hP⟩, h3⟩
      · exact ⟨⟨h1, h2⟩, by omega⟩
  have hdisj : Disjoint ((Ioc l u).filter (· ∣ P)) (P.divisors.filter (fun q => u < q)) := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    rw [mem_filter, mem_Ioc] at hq
    rw [mem_filter] at hq'
    omega
  rw [dpart, blockWeight_eq_sum_ramWeight, blockWeight_eq_sum_ramWeight,
    blockWeight_eq_sum_ramWeight, hset, Finset.sum_union hdisj]

/-- The `U³[N]` norm is subadditive over finite sums. -/
theorem gowersNormInterval_sum_le {ι : Type*} (N : ℕ+) (s : Finset ι) (g : ι → ℤ → ℂ) :
    gowersNormInterval 3 N (fun n => ∑ i ∈ s, g i n) ≤
      ∑ i ∈ s, gowersNormInterval 3 N (g i) := by
  obtain ⟨hadd, -, hzero⟩ := Paper.gowersNormInterval_three_norm_properties N
  have h := Finset.le_sum_of_subadditive (fun f : ℤ → ℂ => gowersNormInterval 3 N f)
    (by
      have : gowersNormInterval 3 N (0 : ℤ → ℂ) = 0 :=
        (hzero 0).2 (fun _ _ => rfl)
      exact this.le)
    hadd s g
  have hfun : (fun n => ∑ i ∈ s, g i n) = ∑ i ∈ s, g i := by
    funext n
    simp [Finset.sum_apply]
  rw [hfun]
  exact h

end PrimeCarleson.Proof.Fplus31

module

public import PrimeCarleson.Proof.Fplus31.Cramer.Approx
public import PrimeCarleson.Proof.Fplus31.TypeIII.Vaughan
public import PrimeCarleson.Proof.Fplus31.TypeIII.Reindex

/-!
# The type I / type II decomposition of `Λ - Λ_{C,w}` on `[1, N]`

Part of the Vaughan decomposition in the proof of [F+] Proposition 3.1 (Leng23 Lemma
`l:type1type2decomposition`, `Final_Version.tex` L1186-L1207). Replace `Λ_{C,w}` by its Brun
truncation `brunTrunc w k` (type I of level `w^k`, `cramer_brun_L1_Icc` for the `L¹` error), apply
Vaughan's identity at `U = V = N^{1/3}` (`vaughan_apply`) and exchange the order of summation. For a
function `f` supported on `[1, N]` (in the application `f = 1_P · star (T.eval)`) this gives the
exact identity

`∑_{n ≤ N} (Λ - Λ_{C,w})(n) f(n)
   = smallPart + brunErr + typeIPart + typeIIPart`,

with, for `D = cubeLevel N` (the largest `D ≤ N` with `D³ ≤ N²`),

* `smallPart = ∑_{n ≤ N, n³ ≤ N} Λ(n) f(n)` (negligible: `≤ N^{1/3} log N`);
* `brunErr = ∑_{n ≤ N} (Λ_{C,w}^{(k)} - Λ_{C,w})(n) f(n)` (`L¹`-small);
* `typeIPart = ∑_{d ≤ D} a_d S_d(N) - ∑_{K < N} (log (K+1) - log K) ∑_{d ≤ D} μ_N(d) S_d(K)`
  with `S_d(K) = ∑_{n ≤ K, d ∣ n} f(n)` (`dvdSum`), `μ_N(d) = μ(d) 1_{d³ ≤ N}` and
  `a_d = μ_N(d)(log N - log d) - vaughanA N d - brunCoeff w k d`: a convex-combination type I sum of
  level `D ≤ N^{2/3}` with `|a_d| ≤ (2 + e⁵) log N`;
* `typeIIPart = ∑_{c, w ≤ D} Λ(c) 1_{c³ > N} b_w f(c w)`, `b_w = ∑_{e ∣ w, e³ > N} μ(e)`.

* `cubeLevel` and its properties;
* `typeICoeff`, `moebiusCut`, `typeIICoeffA`, their supports and bounds;
* `brunTrunc_eq_sum_divisors`, `correlation_decomposition`.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- `D = max {d ≤ N : d³ ≤ N²}`: the level `N^{2/3}` of the type I sums. -/
def cubeLevel (N : ℕ) : ℕ := Nat.findGreatest (fun d => d ^ 3 ≤ N ^ 2) N

/-- `cubeLevel N ≥ 1` for `N ≥ 1`. -/
theorem cubeLevel_pos {N : ℕ} (hN : 1 ≤ N) : 1 ≤ cubeLevel N :=
  Nat.le_findGreatest hN (by simpa using Nat.one_le_pow 2 N hN)

/-- `cubeLevel N³ ≤ N²`. -/
theorem cubeLevel_pow_le {N : ℕ} (hN : 1 ≤ N) : cubeLevel N ^ 3 ≤ N ^ 2 :=
  Nat.findGreatest_spec (P := fun d => d ^ 3 ≤ N ^ 2) (m := 1) hN
    (by simpa using Nat.one_le_pow 2 N hN)

/-- `cubeLevel N ≤ N`. -/
theorem cubeLevel_le (N : ℕ) : cubeLevel N ≤ N := Nat.findGreatest_le N

/-- Every `d` with `d³ ≤ N²` is at most `cubeLevel N`. -/
theorem le_cubeLevel {N d : ℕ} (hN : 1 ≤ N) (h : d ^ 3 ≤ N ^ 2) : d ≤ cubeLevel N := by
  have hdN : d ≤ N :=
    (Nat.pow_le_pow_iff_left (by norm_num : 3 ≠ 0)).mp
      (h.trans (Nat.pow_le_pow_right hN (by norm_num)))
  exact Nat.le_findGreatest hdN h

/-- `d > cubeLevel N` implies `d³ > N²`. -/
theorem lt_pow_of_cubeLevel_lt {N d : ℕ} (hN : 1 ≤ N) (h : cubeLevel N < d) : N ^ 2 < d ^ 3 := by
  by_contra hcon
  exact absurd (le_cubeLevel hN (not_lt.mp hcon)) (not_le.mpr h)

/-- The truncated Möbius weight `μ_N(d) = μ(d) 1_{d³ ≤ N}`. -/
def moebiusCut (N d : ℕ) : ℝ :=
  if d ^ 3 ≤ N then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0

/-- The type I coefficients `a_d = μ_N(d)(log N - log d) - a^{Vaughan}_d - brunCoeff`. -/
def typeICoeff (N w k d : ℕ) : ℝ :=
  moebiusCut N d * (Real.log N - Real.log d) - vaughanA N d - brunCoeff w k d

/-- The type II coefficients `Λ(c) 1_{c³ > N}`. -/
def typeIICoeffA (N c : ℕ) : ℝ := if N < c ^ 3 then ArithmeticFunction.vonMangoldt c else 0

/-- `|μ_N(d)| ≤ 1`. -/
theorem abs_moebiusCut_le (N d : ℕ) : |moebiusCut N d| ≤ 1 := by
  unfold moebiusCut
  split_ifs
  · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  · simp

/-- `μ_N(d) = 0` above the level `cubeLevel N`. -/
theorem moebiusCut_eq_zero {N d : ℕ} (hN : 1 ≤ N) (h : cubeLevel N < d) : moebiusCut N d = 0 := by
  unfold moebiusCut
  have h1 := lt_pow_of_cubeLevel_lt hN h
  have h2 : N ≤ N ^ 2 := by nlinarith
  rw [ite_eq_right_iff]
  intro hcon
  omega

/-- The type I coefficients vanish above the level `cubeLevel N`, provided the Brun
level `w^k` is at most `N^{2/3}`. -/
theorem typeICoeff_eq_zero {N w k d : ℕ} (hN : 1 ≤ N) (hw : 1 ≤ w) (hlevel : (w ^ k) ^ 3 ≤ N ^ 2)
    (h : cubeLevel N < d) : typeICoeff N w k d = 0 := by
  unfold typeICoeff
  have h1 := lt_pow_of_cubeLevel_lt hN h
  have hwk : w ^ k ≤ cubeLevel N := le_cubeLevel hN hlevel
  rw [moebiusCut_eq_zero hN h, vaughanA_eq_zero h1, brunCoeff_eq_zero_of_lt hw (by omega)]
  ring

/-- `|a_d| ≤ (2 + e⁵) log N` for the type I coefficients, `1 ≤ d ≤ N`, `2 ≤ w ≤ N`. -/
theorem abs_typeICoeff_le {N w k d : ℕ} (hw : 2 ≤ w) (hwN : w ≤ N) (hdN : d ≤ N) (hd : 1 ≤ d) :
    |typeICoeff N w k d| ≤ (2 + Real.exp 5) * Real.log N := by
  unfold typeICoeff
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hlogd : Real.log d ≤ Real.log N :=
    Real.log_le_log hdpos (by exact_mod_cast hdN)
  have hlogd0 : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
  have hlogw : Real.log w ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < w)) (by exact_mod_cast hwN)
  have h1 : |moebiusCut N d * (Real.log N - Real.log d)| ≤ Real.log N := by
    rw [abs_mul]
    have : |Real.log N - Real.log d| ≤ Real.log N := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    calc |moebiusCut N d| * |Real.log N - Real.log d| ≤ 1 * Real.log N :=
          mul_le_mul (abs_moebiusCut_le N d) this (abs_nonneg _) zero_le_one
      _ = Real.log N := one_mul _
  have h2 : |vaughanA N d| ≤ Real.log N := (abs_vaughanA_le_log N d).trans hlogd
  have h3 : |brunCoeff w k d| ≤ Real.exp 5 * Real.log N :=
    (abs_brunCoeff_le_log hw k d).trans
      (mul_le_mul_of_nonneg_left hlogw (Real.exp_pos 5).le)
  calc |moebiusCut N d * (Real.log N - Real.log d) - vaughanA N d - brunCoeff w k d|
      ≤ |moebiusCut N d * (Real.log N - Real.log d)| + |vaughanA N d| + |brunCoeff w k d| := by
        refine (abs_sub _ _).trans ?_
        have := abs_sub (moebiusCut N d * (Real.log N - Real.log d)) (vaughanA N d)
        linarith
    _ ≤ (2 + Real.exp 5) * Real.log N := by nlinarith

/-- `|Λ(c) 1_{c³ > N}| ≤ log N` for `c ≤ N`. -/
theorem abs_typeIICoeffA_le {N c : ℕ} (hN : 1 ≤ N) (hc : c ≤ N) :
    |typeIICoeffA N c| ≤ Real.log N := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  unfold typeIICoeffA
  split_ifs
  · rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
    rcases Nat.eq_zero_or_pos c with rfl | hc0
    · simpa using hlogN
    · exact Real.log_le_log (by exact_mod_cast hc0) (by exact_mod_cast hc)
  · simpa using hlogN

/-- The Brun truncation at a natural number is the divisor sum of its coefficients. -/
theorem brunTrunc_eq_sum_divisors {w : ℕ} (hw : 1 ≤ w) (k n : ℕ) (hn : 1 ≤ n) :
    brunTrunc w k (n : ℤ) = ∑ d ∈ n.divisors, brunCoeff w k d := by
  rw [brunTrunc_eq_sum_coeff hw k]
  simp_rw [mul_ite, mul_one, mul_zero, Int.natCast_dvd_natCast]
  rw [← Finset.sum_filter]
  refine Finset.sum_subset ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    exact Nat.mem_divisors.mpr ⟨hd.2, by omega⟩
  · intro d hd hnot
    refine brunCoeff_eq_zero_of_lt hw ?_
    by_contra hle
    refine hnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, not_lt.mp hle⟩,
      Nat.dvd_of_mem_divisors hd⟩)
    exact Nat.pos_of_mem_divisors hd

/-- `∑_{n ≤ N, n³ ≤ N} Λ(n) f(n)`: the negligible part. -/
def smallPart (N : ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, (((if n ^ 3 ≤ N then ArithmeticFunction.vonMangoldt n else 0 : ℝ)) : ℂ) * f n

/-- `∑_{n ≤ N} (Λ_{C,w}^{(k)} - Λ_{C,w})(n) f(n)`: the Brun error. -/
def brunErr (N w k : ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, ((brunTrunc w k (n : ℤ) - cramerModel w (n : ℤ) : ℝ) : ℂ) * f n

/-- The type I part: a type I sum of level `cubeLevel N` against the cut-off sums
`S_d(N)`, minus the weighted average over the cut-offs `S_d(K)`, `K < N`. -/
def typeIPart (N w k : ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Icc 1 (cubeLevel N), (typeICoeff N w k d : ℂ) * dvdSum f d N -
    ∑ K ∈ range N, (logStep K : ℂ) *
      ∑ d ∈ Icc 1 (cubeLevel N), (moebiusCut N d : ℂ) * dvdSum f d K

/-- The type II part: the bilinear sum `∑_{c, w ≤ D} Λ(c) 1_{c³ > N} b_w f(c w)`. -/
def typeIIPart (N : ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ c ∈ Icc 1 (cubeLevel N), ∑ w ∈ Icc 1 (cubeLevel N),
    (typeIICoeffA N c : ℂ) * (typeTwoCoeff N w : ℂ) * f (c * w)

/-- Pointwise form of Vaughan's identity for `Λ - Λ_{C,w}` at `n ∈ [1, N]`. -/
theorem pointwise_decomposition {N w k : ℕ} (hw : 1 ≤ w) {n : ℕ} (hn : 1 ≤ n) :
    ArithmeticFunction.vonMangoldt n - cramerModel w (n : ℤ) =
      (if n ^ 3 ≤ N then ArithmeticFunction.vonMangoldt n else 0) +
      (brunTrunc w k (n : ℤ) - cramerModel w (n : ℤ)) +
      ∑ b ∈ n.divisors, moebiusCut N b * (Real.log n - Real.log b) -
      ∑ d ∈ n.divisors, (vaughanA N d + brunCoeff w k d) +
      ∑ c ∈ n.divisors, typeIICoeffA N c * typeTwoCoeff N (n / c) := by
  have h := vaughan_apply N hn
  rw [Finset.sum_add_distrib, ← brunTrunc_eq_sum_divisors hw k n hn]
  have e1 : (∑ b ∈ n.divisors, moebiusCut N b * (Real.log n - Real.log b)) =
      ∑ b ∈ n.divisors, (if b ^ 3 ≤ N then ((ArithmeticFunction.moebius b : ℤ) : ℝ) else 0) *
        (Real.log n - Real.log b) := rfl
  have e2 : (∑ c ∈ n.divisors, typeIICoeffA N c * typeTwoCoeff N (n / c)) =
      ∑ c ∈ n.divisors, (if N < c ^ 3 then ArithmeticFunction.vonMangoldt c else 0) *
        typeTwoCoeff N (n / c) := rfl
  rw [e1, e2]
  linarith

/-- The log-weighted divisor sum, by partial summation. -/
theorem sum_log_term (N : ℕ) (m : ℕ → ℝ) (f : ℕ → ℂ) :
    ∑ n ∈ Icc 1 N, ((∑ b ∈ n.divisors, m b * (Real.log n - Real.log b) : ℝ) : ℂ) * f n =
      ∑ b ∈ Icc 1 N, (m b : ℂ) * ((Real.log N : ℂ) * dvdSum f b N -
          ∑ K ∈ range N, (logStep K : ℂ) * dvdSum f b K) -
        ∑ b ∈ Icc 1 N, ((m b * Real.log b : ℝ) : ℂ) * dvdSum f b N := by
  have h1 : ∀ n ∈ Icc 1 N,
      ((∑ b ∈ n.divisors, m b * (Real.log n - Real.log b) : ℝ) : ℂ) * f n =
      (∑ b ∈ n.divisors, (m b : ℂ)) * ((Real.log n : ℂ) * f n) -
        (∑ b ∈ n.divisors, ((m b * Real.log b : ℝ) : ℂ)) * f n := by
    intro n _
    have : ((∑ b ∈ n.divisors, m b * (Real.log n - Real.log b) : ℝ) : ℂ) =
        (∑ b ∈ n.divisors, (m b : ℂ)) * (Real.log n : ℂ) -
          ∑ b ∈ n.divisors, ((m b * Real.log b : ℝ) : ℂ) := by
      push_cast
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [this]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib,
    sum_Icc_mul_divisors N (fun b => (m b : ℂ)) (fun n => (Real.log n : ℂ) * f n),
    sum_Icc_mul_divisors N (fun b => ((m b * Real.log b : ℝ) : ℂ)) f]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  have key : dvdSum (fun n => (Real.log n : ℂ) * f n) b N =
      ∑ n ∈ (Icc 1 N).filter (b ∣ ·), f n * (Real.log n : ℂ) := by
    unfold dvdSum
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [key]
  exact sum_dvd_mul_log f b N

/-- The type I terms of `Λ - Λ_{C,w}`, summed over `n` and exchanged (over `d ≤ N`). -/
theorem sum_typeI_terms (N : ℕ) (m β : ℕ → ℝ) (f : ℕ → ℂ) :
    ∑ n ∈ Icc 1 N, ((∑ b ∈ n.divisors, m b * (Real.log n - Real.log b) -
        ∑ d ∈ n.divisors, β d : ℝ) : ℂ) * f n =
      ∑ d ∈ Icc 1 N, ((m d * (Real.log N - Real.log d) - β d : ℝ) : ℂ) * dvdSum f d N -
        ∑ K ∈ range N, (logStep K : ℂ) * ∑ d ∈ Icc 1 N, (m d : ℂ) * dvdSum f d K := by
  have h1 : ∀ n ∈ Icc 1 N, ((∑ b ∈ n.divisors, m b * (Real.log n - Real.log b) -
        ∑ d ∈ n.divisors, β d : ℝ) : ℂ) * f n =
      ((∑ b ∈ n.divisors, m b * (Real.log n - Real.log b) : ℝ) : ℂ) * f n -
        (∑ d ∈ n.divisors, (β d : ℂ)) * f n := by
    intro n _
    push_cast
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, sum_log_term,
    sum_Icc_mul_divisors N (fun d => (β d : ℂ)) f]
  have h2 : ∑ b ∈ Icc 1 N, (m b : ℂ) * ((Real.log N : ℂ) * dvdSum f b N -
          ∑ K ∈ range N, (logStep K : ℂ) * dvdSum f b K) =
      ∑ b ∈ Icc 1 N, (m b : ℂ) * (Real.log N : ℂ) * dvdSum f b N -
        ∑ K ∈ range N, (logStep K : ℂ) * ∑ d ∈ Icc 1 N, (m d : ℂ) * dvdSum f d K := by
    have : ∀ b ∈ Icc 1 N, (m b : ℂ) * ((Real.log N : ℂ) * dvdSum f b N -
          ∑ K ∈ range N, (logStep K : ℂ) * dvdSum f b K) =
        (m b : ℂ) * (Real.log N : ℂ) * dvdSum f b N -
          ∑ K ∈ range N, (logStep K : ℂ) * ((m b : ℂ) * dvdSum f b K) := by
      intro b _
      rw [mul_sub, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun K _ => by ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [Finset.mul_sum]
  rw [h2]
  have h3 : ∑ d ∈ Icc 1 N, ((m d * (Real.log N - Real.log d) - β d : ℝ) : ℂ) * dvdSum f d N =
      ∑ b ∈ Icc 1 N, (m b : ℂ) * (Real.log N : ℂ) * dvdSum f b N -
        ∑ b ∈ Icc 1 N, ((m b * Real.log b : ℝ) : ℂ) * dvdSum f b N -
          ∑ d ∈ Icc 1 N, (β d : ℂ) * dvdSum f d N := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    push_cast
    ring
  rw [h3]
  ring

/-- The type II terms summed over `n` and exchanged, restricted to `c, w ≤ cubeLevel N`. -/
theorem sum_typeII_terms {N : ℕ} (hN : 1 ≤ N) (f : ℕ → ℂ) (hf0 : ∀ n, N < n → f n = 0) :
    ∑ n ∈ Icc 1 N, ((∑ c ∈ n.divisors, typeIICoeffA N c * typeTwoCoeff N (n / c) : ℝ) : ℂ) *
        f n = typeIIPart N f := by
  set G : ℕ → ℕ → ℂ := fun c w => (typeIICoeffA N c : ℂ) * (typeTwoCoeff N w : ℂ) * f (c * w)
    with hG
  have h1 : ∀ n ∈ Icc 1 N, ((∑ c ∈ n.divisors, typeIICoeffA N c * typeTwoCoeff N (n / c) : ℝ) : ℂ) *
        f n = ∑ c ∈ n.divisors, G c (n / c) := by
    intro n _
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c hc => ?_
    simp only [hG]
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hc)]
  rw [Finset.sum_congr rfl h1, sum_Icc_divisors N G]
  -- support
  have hsupp : ∀ c w, G c w ≠ 0 → c ≤ cubeLevel N ∧ w ≤ cubeLevel N := by
    intro c w hne
    simp only [hG] at hne
    have hA : typeIICoeffA N c ≠ 0 := by
      intro h0
      exact hne (by rw [h0]; simp)
    have hB : typeTwoCoeff N w ≠ 0 := by
      intro h0
      exact hne (by rw [h0]; simp)
    have hF : f (c * w) ≠ 0 := by
      intro h0
      exact hne (by rw [h0]; simp)
    have hcw : c * w ≤ N := by
      by_contra hlt
      exact hF (hf0 _ (not_le.mp hlt))
    have hc3 : N < c ^ 3 := by
      by_contra hle
      refine hA ?_
      unfold typeIICoeffA
      rw [ite_eq_right_iff]
      intro h
      omega
    have hw3 : N < w ^ 3 := by
      by_contra hle
      exact hB (typeTwoCoeff_eq_zero (not_lt.mp hle))
    have hcw3 : c ^ 3 * w ^ 3 ≤ N ^ 3 := by
      rw [← mul_pow]
      exact Nat.pow_le_pow_left hcw 3
    have hc2 : c ^ 3 ≤ N ^ 2 := by
      by_contra hlt
      have : N ^ 2 < c ^ 3 := not_le.mp hlt
      have h4 : N ^ 2 * N < c ^ 3 * w ^ 3 :=
        Nat.mul_lt_mul_of_lt_of_le this hw3.le (by omega)
      have : N ^ 3 = N ^ 2 * N := by ring
      omega
    have hw2 : w ^ 3 ≤ N ^ 2 := by
      by_contra hlt
      have : N ^ 2 < w ^ 3 := not_le.mp hlt
      have h4 : N * N ^ 2 < c ^ 3 * w ^ 3 :=
        Nat.mul_lt_mul_of_lt_of_le hc3 this.le (by omega)
      have : N ^ 3 = N * N ^ 2 := by ring
      omega
    exact ⟨le_cubeLevel hN hc2, le_cubeLevel hN hw2⟩
  have hDN : cubeLevel N ≤ N := cubeLevel_le N
  -- extend the inner range to `[1, N]`
  have h2 : ∀ c ∈ Icc 1 N, ∑ w ∈ Icc 1 (N / c), G c w = ∑ w ∈ Icc 1 (cubeLevel N), G c w := by
    intro c hc
    have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
    have hsub1 : Icc 1 (N / c) ⊆ Icc 1 N :=
      Finset.Icc_subset_Icc_right (Nat.div_le_self _ _)
    have hsub2 : Icc 1 (cubeLevel N) ⊆ Icc 1 N := Finset.Icc_subset_Icc_right hDN
    have e1 : ∑ w ∈ Icc 1 (N / c), G c w = ∑ w ∈ Icc 1 N, G c w := by
      refine Finset.sum_subset hsub1 fun w hw hw' => ?_
      have hwN : N / c < w := by
        have := Finset.mem_Icc.mp hw
        by_contra hle
        exact hw' (Finset.mem_Icc.mpr ⟨this.1, not_lt.mp hle⟩)
      have : N < c * w := by
        have h5 := Nat.lt_mul_div_succ N (by omega : 0 < c)
        calc N < c * (N / c + 1) := h5
          _ ≤ c * w := Nat.mul_le_mul_left c hwN
      simp only [hG]
      rw [hf0 _ this]
      simp
    have e2 : ∑ w ∈ Icc 1 (cubeLevel N), G c w = ∑ w ∈ Icc 1 N, G c w := by
      refine Finset.sum_subset hsub2 fun w hw hw' => ?_
      by_contra hne
      have := (hsupp c w hne).2
      exact hw' (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hw).1, this⟩)
    rw [e1, e2]
  rw [Finset.sum_congr rfl h2]
  have hsub : Icc 1 (cubeLevel N) ⊆ Icc 1 N := Finset.Icc_subset_Icc_right hDN
  rw [← Finset.sum_subset hsub (f := fun c => ∑ w ∈ Icc 1 (cubeLevel N), G c w)
    (fun c hc hc' => Finset.sum_eq_zero fun w _ => by
      by_contra hne
      exact hc' (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hc).1, (hsupp c w hne).1⟩))]
  rfl

/-- `typeICoeff` in the form `μ_N(d)(log N - log d) - (a^{Vaughan}_d + brunCoeff)`. -/
theorem typeICoeff_eq (N w k d : ℕ) :
    typeICoeff N w k d = moebiusCut N d * (Real.log N - Real.log d) -
      (vaughanA N d + brunCoeff w k d) := by
  unfold typeICoeff
  ring

/-- **The exact decomposition of the correlation of `Λ - Λ_{C,w}` with `f`.**  For `f` supported
on `[1, N]`, `w ≥ 1` and `(w^k)³ ≤ N²` (level of the Brun truncation at most `N^{2/3}`):
`∑_{n ≤ N} (Λ - Λ_{C,w})(n) f(n) = smallPart + brunErr + typeIPart + typeIIPart`. -/
theorem correlation_decomposition {N w k : ℕ} (hN : 1 ≤ N) (hw : 1 ≤ w)
    (hlevel : (w ^ k) ^ 3 ≤ N ^ 2) (f : ℕ → ℂ) (hf0 : ∀ n, N < n → f n = 0) :
    ∑ n ∈ Icc 1 N, ((ArithmeticFunction.vonMangoldt n - cramerModel w (n : ℤ) : ℝ) : ℂ) * f n =
      smallPart N f + brunErr N w k f + typeIPart N w k f + typeIIPart N f := by
  have hpt : ∀ n ∈ Icc 1 N,
      ((ArithmeticFunction.vonMangoldt n - cramerModel w (n : ℤ) : ℝ) : ℂ) * f n =
      (((if n ^ 3 ≤ N then ArithmeticFunction.vonMangoldt n else 0 : ℝ)) : ℂ) * f n +
        ((brunTrunc w k (n : ℤ) - cramerModel w (n : ℤ) : ℝ) : ℂ) * f n +
        ((∑ b ∈ n.divisors, moebiusCut N b * (Real.log n - Real.log b) -
          ∑ d ∈ n.divisors, (vaughanA N d + brunCoeff w k d) : ℝ) : ℂ) * f n +
        ((∑ c ∈ n.divisors, typeIICoeffA N c * typeTwoCoeff N (n / c) : ℝ) : ℂ) * f n := by
    intro n hn
    rw [pointwise_decomposition (N := N) (k := k) hw (Finset.mem_Icc.mp hn).1]
    push_cast
    ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, sum_typeI_terms N (moebiusCut N)
      (fun d => vaughanA N d + brunCoeff w k d) f, sum_typeII_terms hN f hf0]
  have hDN : cubeLevel N ≤ N := cubeLevel_le N
  have hsub : Icc 1 (cubeLevel N) ⊆ Icc 1 N := Finset.Icc_subset_Icc_right hDN
  have hI1 : ∑ d ∈ Icc 1 N, ((moebiusCut N d * (Real.log N - Real.log d) -
        (vaughanA N d + brunCoeff w k d) : ℝ) : ℂ) * dvdSum f d N =
      ∑ d ∈ Icc 1 (cubeLevel N), (typeICoeff N w k d : ℂ) * dvdSum f d N := by
    rw [← Finset.sum_subset hsub (f := fun d => ((moebiusCut N d * (Real.log N - Real.log d) -
        (vaughanA N d + brunCoeff w k d) : ℝ) : ℂ) * dvdSum f d N) (fun d hd hd' => by
      have hlt : cubeLevel N < d := by
        by_contra hle
        exact hd' (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, not_lt.mp hle⟩)
      rw [← typeICoeff_eq, typeICoeff_eq_zero hN hw hlevel hlt]
      simp)]
    exact Finset.sum_congr rfl fun d _ => by rw [typeICoeff_eq]
  have hI2 : ∀ K, ∑ d ∈ Icc 1 N, (moebiusCut N d : ℂ) * dvdSum f d K =
      ∑ d ∈ Icc 1 (cubeLevel N), (moebiusCut N d : ℂ) * dvdSum f d K := by
    intro K
    rw [← Finset.sum_subset hsub (f := fun d => (moebiusCut N d : ℂ) * dvdSum f d K)
      (fun d hd hd' => by
        have hlt : cubeLevel N < d := by
          by_contra hle
          exact hd' (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, not_lt.mp hle⟩)
        rw [moebiusCut_eq_zero hN hlt]
        simp)]
  rw [hI1]
  simp_rw [hI2]
  unfold typeIPart smallPart brunErr
  ring

end PrimeCarleson.Proof.Fplus31

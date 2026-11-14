module

public import PrimeCarleson.Proof.Fplus31.Brun.Main

/-!
# The `L¹` type I approximation of the Cramér model

In the proof of [F+] Proposition 3.1 (the comparison of `Λ` with the Cramér model) we replace
`Λ_{C,w}` by its Brun truncation `Λ_{C,w}^{(k)}(n) = (P/φ(P)) ∑_{d ∣ (n, P(w)), ω(d) ≤ k} μ(d)`, a
type I sum with coefficients `a_d = (P/φ(P)) μ(d)` of size `≤ e⁵ log w`, supported on `d ≤ w^k`,
with an `L¹` error that is `exp(-k log k)`-small once `k ≫ log log w`.

* `brunCoeff w k d`: the coefficients; `abs_brunCoeff_le`, `abs_brunCoeff_le_log`,
  `brunCoeff_eq_zero_of_lt`, `brunTrunc_eq_sum_coeff`
  (`brunTrunc w k n = ∑_{d ≤ w^k} a_d 1_{d ∣ n}`);
* `pow_div_factorial_le`: `S^m / m! ≤ (e S / m)^m`;
* `cramer_brun_L1` (used by the Vaughan decomposition): for `2 ≤ w`, `1 ≤ r`, `gcd(a, r) = 1`,
  `∑_{n ∈ apSet r a lo hi} |Λ_{C,w}(n) - Λ_{C,w}^{(k)}(n)|
    ≤ e⁵ log w · ((hi - lo)/r · (e (log log w + 4)/(k+1))^{k+1} + w^{k+1})`;
* `cramer_brun_L1_Icc`: the case of the interval `[1, N]` (`r = 1`);
* `brun_Icc` (used by the comparison with the Heath-Brown model):
  `|∑_{n=1}^N Λ_{C,w}(n) - N| ≤ (P/φ(P)) (2 e^S S^{k+1}/(k+1)! N
  + 2 (k+1) w^{k+1})`, the density `𝔼_{n ≤ N} Λ_{C,w} = 1 + O(·)`.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- The coefficients `a_d = (P/φ(P)) μ(d) 1_{d ∈ brunSet w k}` of the Brun truncation. -/
def brunCoeff (w k d : ℕ) : ℝ :=
  if d ∈ brunSet w k then
    (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) *
      ((ArithmeticFunction.moebius d : ℤ) : ℝ)
  else 0

/-- `|a_d| ≤ P/φ(P)`. -/
theorem abs_brunCoeff_le (w k d : ℕ) :
    |brunCoeff w k d| ≤ (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) := by
  have hW : 0 ≤ (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) := by positivity
  unfold brunCoeff
  split_ifs
  · rw [abs_mul, abs_of_nonneg hW]
    have : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    nlinarith [abs_nonneg ((ArithmeticFunction.moebius d : ℤ) : ℝ)]
  · simpa using hW

/-- `|a_d| ≤ e⁵ log w` for `w ≥ 2`. -/
theorem abs_brunCoeff_le_log {w : ℕ} (hw : 2 ≤ w) (k d : ℕ) :
    |brunCoeff w k d| ≤ Real.exp 5 * Real.log w :=
  (abs_brunCoeff_le w k d).trans (primorialBelow_div_totient_le w hw)

/-- The coefficients vanish above the level `w^k` (`w ≥ 1`). -/
theorem brunCoeff_eq_zero_of_lt {w k d : ℕ} (hw : 1 ≤ w) (h : w ^ k < d) :
    brunCoeff w k d = 0 := by
  unfold brunCoeff
  rw [ite_eq_right_iff]
  intro hd
  exact absurd (le_pow_of_mem_brunSet hw hd) (not_le.mpr h)

/-- The Brun truncation is a type I sum of level `w^k`:
`Λ_{C,w}^{(k)}(n) = ∑_{1 ≤ d ≤ w^k} a_d 1_{d ∣ n}`. -/
theorem brunTrunc_eq_sum_coeff {w : ℕ} (hw : 1 ≤ w) (k : ℕ) (n : ℤ) :
    brunTrunc w k n =
      ∑ d ∈ Finset.Icc 1 (w ^ k), brunCoeff w k d * (if (d : ℤ) ∣ n then 1 else 0) := by
  rw [brunTrunc, truncMoebius, Finset.mul_sum]
  have hsub : brunSet w k ⊆ Finset.Icc 1 (w ^ k) := by
    intro d hd
    rw [Finset.mem_Icc]
    obtain ⟨hdP, _⟩ := mem_brunSet.mp hd
    exact ⟨Nat.pos_of_dvd_of_pos hdP (primorialBelow_pos w), le_pow_of_mem_brunSet hw hd⟩
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun d hd => ?_
    rw [brunCoeff, ite_eq_left hd]
    ring
  · intro d _ hd
    rw [brunCoeff, ite_eq_right hd]
    simp

/-- `S^m / m! ≤ (e S / m)^m` for `S ≥ 0` and `m ≥ 1`. -/
theorem pow_div_factorial_le {S : ℝ} (hS : 0 ≤ S) {m : ℕ} (hm : 1 ≤ m) :
    S ^ m / (m.factorial : ℝ) ≤ (Real.exp 1 * S / m) ^ m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h := Real.pow_div_factorial_le_exp (x := (m : ℝ)) hm'.le m
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hexp : Real.exp (m : ℝ) = Real.exp 1 ^ m := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [hexp, div_le_iff₀ hfac] at h
  calc S ^ m / (m.factorial : ℝ) = (S / m) ^ m * ((m : ℝ) ^ m / (m.factorial : ℝ)) := by
        rw [div_pow]; field_simp
    _ ≤ (S / m) ^ m * Real.exp 1 ^ m := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rwa [div_le_iff₀ hfac]
    _ = (Real.exp 1 * S / m) ^ m := by rw [← mul_pow]; congr 1; ring

/-- **The `L¹` type I approximation of the Cramér model.** For `2 ≤ w`, `1 ≤ r` and
`gcd(a, r) = 1`:
`∑_{n ∈ apSet r a lo hi} |Λ_{C,w}(n) - Λ_{C,w}^{(k)}(n)|
  ≤ e⁵ log w · ((hi - lo)/r · (e (log log w + 4)/(k+1))^{k+1} + w^{k+1})`. -/
theorem cramer_brun_L1 (w k : ℕ) (hw : 2 ≤ w) {r : ℕ} (hr : 1 ≤ r) {a : ℤ}
    (ha : IsCoprime a (r : ℤ)) {lo hi : ℕ} (h : lo ≤ hi) :
    ∑ n ∈ apSet r a lo hi, |cramerModel w n - brunTrunc w k n| ≤
      Real.exp 5 * Real.log w *
        (((hi : ℝ) - lo) / r * (Real.exp 1 * (Real.log (Real.log w) + 4) / ((k + 1 : ℕ) : ℝ)) ^
            (k + 1) + (w : ℝ) ^ (k + 1)) := by
  refine (brun_err1 w k hr ha h).trans ?_
  have hL : 0 ≤ ((hi : ℝ) - lo) / r := by
    have : (lo : ℝ) ≤ hi := by exact_mod_cast h
    positivity
  have hS0 : 0 ≤ ∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p := Finset.sum_nonneg fun p _ => by positivity
  have hS := PrimeCarleson.Proof.Common.sum_primesBelow_inv_le_log_log hw
  have hfac : (1 : ℝ) ≤ ((k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hwk : (0 : ℝ) ≤ (w : ℝ) ^ (k + 1) := by positivity
  have hmain : (∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p) ^ (k + 1) / ((k + 1).factorial : ℝ) ≤
      (Real.exp 1 * (Real.log (Real.log w) + 4) / ((k + 1 : ℕ) : ℝ)) ^ (k + 1) := by
    refine (pow_div_factorial_le hS0 (Nat.succ_pos k)).trans ?_
    refine pow_le_pow_left₀ (by positivity) ?_ _
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_left hS (Real.exp_pos 1).le
  refine mul_le_mul (primorialBelow_div_totient_le w hw) ?_ ?_ ?_
  · refine add_le_add (mul_le_mul_of_nonneg_left hmain hL) ?_
    exact div_le_self hwk hfac
  · refine add_nonneg (mul_nonneg hL (by positivity)) (by positivity)
  · exact mul_nonneg (Real.exp_pos 5).le
      (Real.log_nonneg (by exact_mod_cast hw.trans' (by norm_num)))

/-- `apSet 1 a lo hi` is the whole interval `(lo, hi]`. -/
theorem apSet_one (a : ℤ) (lo hi : ℕ) : apSet 1 a lo hi = Finset.Ioc (lo : ℤ) hi := by
  simp [apSet, Int.modEq_one]

/-- `(0, N] = [1, N]` in `ℤ`. -/
theorem apSet_one_zero (a : ℤ) (N : ℕ) : apSet 1 a 0 N = Finset.Icc (1 : ℤ) N := by
  rw [apSet_one]
  ext n
  simp only [Finset.mem_Ioc, Finset.mem_Icc, Nat.cast_zero]
  omega

/-- `cramer_brun_L1` on the interval `[1, N]`: the `L¹[N]` error of the Brun truncation. -/
theorem cramer_brun_L1_Icc (w k N : ℕ) (hw : 2 ≤ w) :
    ∑ n ∈ Finset.Icc (1 : ℤ) N, |cramerModel w n - brunTrunc w k n| ≤
      Real.exp 5 * Real.log w *
        ((N : ℝ) * (Real.exp 1 * (Real.log (Real.log w) + 4) / ((k + 1 : ℕ) : ℝ)) ^ (k + 1) +
          (w : ℝ) ^ (k + 1)) := by
  have := cramer_brun_L1 w k hw (r := 1) le_rfl (a := 0) isCoprime_one_right (lo := 0) (hi := N)
    (Nat.zero_le N)
  rw [apSet_one_zero] at this
  simpa using this

/-- **Brun's pure sieve on `[1, N]`** (`r = 1`): `|∑_{n=1}^N Λ_{C,w}(n) - N|
  ≤ (P/φ(P)) (2 e^S S^{k+1}/(k+1)! · N + 2 (k+1) w^{k+1})`, `S = ∑_{p < w} 1/p`; i.e.
  `𝔼_{n ≤ N} Λ_{C,w}(n) = 1 + O(·)`. -/
theorem brun_Icc (w k N : ℕ) (hw : 2 ≤ w) :
    |∑ n ∈ Finset.Icc (1 : ℤ) N, cramerModel w n - (N : ℝ)| ≤
      ((primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ)) *
        (2 * Real.exp (∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p) *
            (∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) *
            (N : ℝ) + 2 * (k + 1) * (w : ℝ) ^ (k + 1)) := by
  have := brun_ap w k 1 hw (by omega) le_rfl (a := 0) isCoprime_one_right (lo := 0) (hi := N)
    (Nat.zero_le N)
  rw [apSet_one_zero] at this
  simpa using this

end PrimeCarleson.Proof.Fplus31

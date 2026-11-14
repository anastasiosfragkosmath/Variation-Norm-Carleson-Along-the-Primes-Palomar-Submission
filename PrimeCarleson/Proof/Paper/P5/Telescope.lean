module

public import PrimeCarleson.Proof.Paper.Defs.Psi
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The partition of unity behind `ψ` and its telescoping identity

Source: main paper `s:Prelim`, L609–L612, used for the uniform bounded variation of the multiplier
`∑_{k ≥ k₀} ψ̂(2^k β)` of `K_Q` (main paper `s:red`, L1694–L1695, and `p:global-shell-var`,
L2028–L2029).

For `ψ : PsiData` let `H(t) = ∑_{k ≥ 0} ψ_k(t)` (a locally finite sum: `ψ_k` lives on
`2^{k-2} < |t| < 2^k`) and `λ(t) = 1 - t H(t)`. Then

* `H` and `λ` are smooth (`contDiff_Hfun`, `contDiff_lamFun`);
* `λ(t) = 0` for `|t| ≥ 1` (`lamFun_eq_zero`: `∑_{k ≥ 0} ψ_k(t) = 1/t` for `|t| ≥ 1`), so `λ` is a
  compactly supported smooth function (`hasCompactSupport_lamFun`);
* the telescoping identity `t ψ_k(t) = λ(t / 2^{k+1}) - λ(t / 2^k)` (`mul_psiK_eq_sub_lamFun`),
  hence `t ∑_{k < n} ψ_k(t) = λ(t / 2^n) - λ(t)`.

The point: the derivative of `β ↦ ψ̂(2^k β)` is, up to `-2πi`, the Fourier transform of
`λ(·/2^{k+1}) - λ(·/2^k)`, so the derivatives of the partial sums `∑_{k<n} ψ̂(2^k β)` telescope
into `2^n λ̂(2^n β) - λ̂(β)` and have `L¹` norm at most `2‖λ̂‖_{L¹}` uniformly in `n`.
-/

@[expose] public noncomputable section

open scoped ContDiff

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper.P5

open PrimeCarleson.Proof.Paper

variable (ψ : PsiData)

/-- `H(t) = ∑_{k ≥ 0} ψ_k(t)`, a locally finite sum. -/
def Hfun (t : ℝ) : ℝ := ∑' k : ℕ, psiK ψ.toFun k t

/-- `λ(t) = 1 - t H(t)`. -/
def lamFun (t : ℝ) : ℝ := 1 - t * Hfun ψ t

/-- For `|t| ≤ 2^m / 4` only the terms `k < m` of `H(t)` can be nonzero. -/
theorem psiK_eq_zero_of_le_pow {m k : ℕ} {t : ℝ} (hk : m ≤ k) (ht : |t| ≤ (2 : ℝ) ^ m / 4) :
    psiK ψ.toFun k t = 0 :=
  ψ.psiK_eq_zero_of_le (ht.trans (by gcongr; norm_num))

/-- The series `H(t)` is summable (it is a finite sum). -/
theorem summable_psiK (t : ℝ) : Summable fun k : ℕ => psiK ψ.toFun k t := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (4 * |t|) (by norm_num : (1 : ℝ) < 2)
  refine summable_of_ne_finset_zero (s := Finset.range m) fun k hk => ?_
  refine psiK_eq_zero_of_le_pow ψ (m := m) (by simpa using hk) ?_
  rw [le_div_iff₀ (by norm_num)]
  linarith

/-- `H = ∑_{k < m} ψ_k` on `|t| ≤ 2^m / 4`. -/
theorem Hfun_eq_sum {m : ℕ} {t : ℝ} (ht : |t| ≤ (2 : ℝ) ^ m / 4) :
    Hfun ψ t = ∑ k ∈ Finset.range m, psiK ψ.toFun k t :=
  tsum_eq_sum fun k hk => psiK_eq_zero_of_le_pow ψ (by simpa using hk) ht

/-- `H` is smooth. -/
theorem contDiff_Hfun : ContDiff ℝ ∞ (Hfun ψ) := by
  rw [contDiff_iff_contDiffAt]
  intro t₀
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (4 * (|t₀| + 1)) (by norm_num : (1 : ℝ) < 2)
  have hnhd : {t : ℝ | |t| < (2 : ℝ) ^ m / 4} ∈ nhds t₀ := by
    refine (isOpen_lt continuous_abs continuous_const).mem_nhds ?_
    simp only [Set.mem_ofPred_eq]
    rw [lt_div_iff₀ (by norm_num)]
    linarith [abs_nonneg t₀]
  have hev : Hfun ψ =ᶠ[nhds t₀] fun t => ∑ k ∈ Finset.range m, psiK ψ.toFun k t := by
    filter_upwards [hnhd] with t ht using Hfun_eq_sum ψ (le_of_lt ht)
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact (ContDiff.sum fun k _ => ψ.contDiff_psiK k).contDiffAt

/-- `H(t) = 1/t` for `|t| ≥ 1`. -/
theorem Hfun_eq_inv {t : ℝ} (ht : 1 ≤ |t|) : Hfun ψ t = 1 / t := by
  have h0 : psiK ψ.toFun 0 t = 0 := ψ.psiK_eq_zero_of_ge (by simpa using ht)
  rw [Hfun, (summable_psiK ψ t).tsum_eq_zero_add, h0, zero_add]
  exact ψ.tsum_psiK ht

/-- `λ(t) = 0` for `|t| ≥ 1`. -/
theorem lamFun_eq_zero {t : ℝ} (ht : 1 ≤ |t|) : lamFun ψ t = 0 := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
    linarith
  rw [lamFun, Hfun_eq_inv ψ ht]
  field_simp
  ring

/-- `λ` is smooth. -/
theorem contDiff_lamFun : ContDiff ℝ ∞ (lamFun ψ) :=
  contDiff_const.sub (contDiff_id.mul (contDiff_Hfun ψ))

/-- `λ` has compact support in `[-1, 1]`. -/
theorem hasCompactSupport_lamFun : HasCompactSupport (lamFun ψ) := by
  refine HasCompactSupport.intro (K := Set.Icc (-1) 1) isCompact_Icc fun t ht => ?_
  refine lamFun_eq_zero ψ ?_
  by_contra h
  exact ht (Set.mem_Icc.2 (abs_le.1 (not_le.1 h).le))

/-- The splitting `H(t) = ∑_{k<n} ψ_k(t) + 2^{-n} H(t / 2^n)`. -/
theorem Hfun_split (n : ℕ) (t : ℝ) :
    Hfun ψ t = ∑ k ∈ Finset.range n, psiK ψ.toFun k t + ((2 : ℝ) ^ n)⁻¹ * Hfun ψ (t / 2 ^ n) := by
  have h := (summable_psiK ψ t).sum_add_tsum_nat_add n
  rw [Hfun, ← h]
  congr 1
  rw [Hfun, ← tsum_mul_left]
  refine tsum_congr fun i => ?_
  simp only [psiK]
  rw [show t / 2 ^ n * ((2 : ℝ) ^ i)⁻¹ = t * ((2 : ℝ) ^ (i + n))⁻¹ by
    rw [pow_add]; field_simp]
  rw [pow_add]
  field_simp

/-- `t ∑_{k<n} ψ_k(t) = λ(t / 2^n) - λ(t)`. -/
theorem mul_sum_psiK_eq (n : ℕ) (t : ℝ) :
    t * ∑ k ∈ Finset.range n, psiK ψ.toFun k t = lamFun ψ (t / 2 ^ n) - lamFun ψ t := by
  have h := Hfun_split ψ n t
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  unfold lamFun
  have : t * Hfun ψ t = t * ∑ k ∈ Finset.range n, psiK ψ.toFun k t +
      t / 2 ^ n * Hfun ψ (t / 2 ^ n) := by
    rw [h]
    field_simp
  linarith

/-- The telescoping identity `t ψ_k(t) = λ(t / 2^{k+1}) - λ(t / 2^k)`. -/
theorem mul_psiK_eq_sub_lamFun (k : ℕ) (t : ℝ) :
    t * psiK ψ.toFun k t = lamFun ψ (t / 2 ^ (k + 1)) - lamFun ψ (t / 2 ^ k) := by
  have h1 := mul_sum_psiK_eq ψ (k + 1) t
  have h0 := mul_sum_psiK_eq ψ k t
  rw [Finset.sum_range_succ, mul_add] at h1
  linarith

end PrimeCarleson.Proof.Paper.P5

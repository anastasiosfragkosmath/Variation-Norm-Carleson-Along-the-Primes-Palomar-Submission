module

public import PrimeCarleson.Proof.Paper.P5.Kernel
public import PrimeCarleson.Proof.Paper.P4a.VarScale
public import PrimeCarleson.Proof.Common.Interpolation
public import PrimeCarleson.Proof.Common.Variation
public import PrimeCarleson.Frozen.PrimeVariation
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Definitions and basic API for the variational reduction `p:red-var`

Source: main paper `p:red-var`, L1227–L1519 (Proposition `p:red-var` and its proof). The files of
`P6a/` prove the steps of the proof: the triangle-inequality split (L1245–L1273), the main-term
split (L1390–L1411), the reindexing of the low-denominator term (L1460–L1474), the auxiliary
exponent (L1324), the moments of the residual (L1305–L1310, L1338–L1359), the residual sum
(L1374–L1387), the crude and summed high-denominator bounds (L1434–L1458; the summed bound is
`highQ_sum_param` of `Main/Interp.lean`), the replacement of `∑ ψ_k` by `K_Q` and its error
(L1476–L1507) and the sum over dyadic `Q` (L1517–L1518), together with `e:var-covering-loss`,
`e:highQ-var-L2-red`, `e:minor-U3-var-red` and its cutoff bridge. The combination of the pieces
(L1508–L1516) is in `Main/RedVar.lean`.

This file fixes the notation:

* `wFun n = w(n) = Λ(|n|)` (`e:wweight`);
* `varOp r u f x = V^r(∑_n f(x - n) u(n) e(λ n) : λ ∈ 𝕋)` (the pointwise variation of the
  modulated sum with the weight `u`; `weightedModSum`, `pointwiseVariation`), the common shape of
  every operator in the proof of `p:red-var`;
* `psiKz ψ k n = ψ_k(n)`, `psiTailZ ψ k₀ n = ∑_{k ≥ k₀} ψ_k(n)` (L609–L612);
* `resWeight k = w - w_{≤ M(k)}` (the residual `u_k` of L1277–L1281, `wLeM`, `cutoffM`);
* the index sets of the main-term split: `jSet k` (the dyadic `Q = 2^j ≤ M(k)`), `lowJ D₀ k`
  (`Q ≤ k^{D₀}`), `highJ D₀ k` (`Q > k^{D₀}`) and the finitely many leftover pairs
  `leftoverSet D₀ = {(k, j) : M(k) < 2^j ≤ k^{D₀}}`.

The basic API: `varOp` is subadditive in the weight and in `f`, invariant under the sign of the
weight, and the sums over `n` are finite sums for finitely supported `f`
(`weightedModSum_eq_sum_of_finsupp`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-! ### Definitions -/

/-- The weight `w(n) = Λ(|n|)` of `e:wweight` (L283-L288), as a complex-valued function on `ℤ`. -/
def wFun (n : ℤ) : ℂ := ((ArithmeticFunction.vonMangoldt n.natAbs : ℝ) : ℂ)

/-- The pointwise variation `V^r(∑_n f(x - n) u(n) e(λ n) : λ ∈ 𝕋)(x)` of the modulated sum with
weight `u` (`𝕋 = [0, 1)`); the shape of every variational operator in the proof of `p:red-var`. -/
def varOp (r : ℝ) (u : ℤ → ℂ) (f : ℤ → ℂ) (x : ℤ) : ℝ≥0∞ :=
  pointwiseVariation r (fun lam y => weightedModSum u f lam y) x

/-- `varOp` unfolded: the `r`-variation over `[0, 1)` of `λ ↦ T^u_λ f(x)`. -/
theorem varOp_eq (r : ℝ) (u f : ℤ → ℂ) (x : ℤ) :
    varOp r u f x = rVariationOn r (Set.Ico 0 1) (fun lam => weightedModSum u f lam x) := rfl

/-- `ψ_k(n)` as a complex number, `n ∈ ℤ`. -/
def psiKz (ψ : PsiData) (k : ℕ) (n : ℤ) : ℂ := ((psiK ψ.toFun k (n : ℝ) : ℝ) : ℂ)

/-- The tail `∑_{k ≥ k₀} ψ_k(n)`. -/
def psiTailZ (ψ : PsiData) (k₀ : ℕ) (n : ℤ) : ℂ := ∑' i : ℕ, psiKz ψ (k₀ + i) n

/-- The residual weight `u_k = w - w_{≤ M(k)}` (L1277–L1281). -/
def resWeight (k : ℕ) (n : ℤ) : ℂ := wFun n - wLeM k n

/-- The weight `w_Q ψ_k` of a pair `(k, j)`, `Q = 2^j`. -/
def pairW (ψ : PsiData) (k j : ℕ) (n : ℤ) : ℂ := wQ (2 ^ j) n * psiKz ψ k n

/-- The least `k` with `Q^{1/D₀} ≤ k` (the range of `e:KQ`); `S.P.kmin = kminD S.P.D₀`. -/
def kminD (D₀ : ℝ) (Q : ℕ) : ℕ := ⌈(Q : ℝ) ^ (1 / D₀)⌉₊

/-- The dyadic exponents `j` with `2^j ≤ M(k)`: the blocks of `w_{≤ M(k)}` (`wLeM_eq_sum`). -/
def jSet (k : ℕ) : Finset ℕ :=
  (Finset.range (⌊cutoffM k⌋₊ + 1)).filter fun j => (2 : ℝ) ^ j ≤ cutoffM k

/-- The low-denominator blocks `Q = 2^j ≤ min(k^{D₀}, M(k))` of the split. -/
def lowJ (D₀ : ℝ) (k : ℕ) : Finset ℕ := (jSet k).filter fun j => (2 : ℝ) ^ j ≤ (k : ℝ) ^ D₀

/-- The high-denominator blocks `k^{D₀} < Q = 2^j ≤ M(k)` of the split. -/
def highJ (D₀ : ℝ) (k : ℕ) : Finset ℕ := (jSet k).filter fun j => ¬ (2 : ℝ) ^ j ≤ (k : ℝ) ^ D₀

/-- The leftover pairs `M(k) < Q = 2^j ≤ k^{D₀}`, `k ≥ 1`; finite (`leftoverSet_finite` in
`P6a/Finite.lean`). -/
def leftoverSet (D₀ : ℝ) : Set (ℕ × ℕ) :=
  {p | 1 ≤ p.1 ∧ cutoffM p.1 < (2 : ℝ) ^ p.2 ∧ (2 : ℝ) ^ p.2 ≤ (p.1 : ℝ) ^ D₀}

/-! ### Basic facts on the weights -/

/-- `w` is even. -/
theorem wFun_neg (n : ℤ) : wFun (-n) = wFun n := by simp [wFun]

/-- `|w(n)| ≤ log |n|`. -/
theorem norm_wFun_le_log (n : ℤ) : ‖wFun n‖ ≤ Real.log (n.natAbs : ℝ) := by
  unfold wFun
  rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact ArithmeticFunction.vonMangoldt_le_log

/-- `w_{≤ M(k)}` is even. -/
theorem wLeM_neg (k : ℕ) (n : ℤ) : wLeM k (-n) = wLeM k n := heathBrownModel_neg _ n

/-- The residual `u_k = w - w_{≤ M(k)}` is even. -/
theorem resWeight_neg (k : ℕ) (n : ℤ) : resWeight k (-n) = resWeight k n := by
  simp [resWeight, wFun_neg, wLeM_neg]

/-- `ψ_k` vanishes on integers `n` with `|n| ≤ 2^k / 4`. -/
theorem psiKz_eq_zero_of_le (ψ : PsiData) {k : ℕ} {n : ℤ} (h : (n.natAbs : ℝ) ≤ (2 : ℝ) ^ k / 4) :
    psiKz ψ k n = 0 := by
  unfold psiKz
  rw [ψ.psiK_eq_zero_of_le (by simpa [Nat.cast_natAbs, Int.cast_abs] using h)]
  simp

/-- `ψ_k` vanishes on integers `n` with `|n| ≥ 2^k`. -/
theorem psiKz_eq_zero_of_ge (ψ : PsiData) {k : ℕ} {n : ℤ} (h : (2 : ℝ) ^ k ≤ (n.natAbs : ℝ)) :
    psiKz ψ k n = 0 := by
  unfold psiKz
  rw [ψ.psiK_eq_zero_of_ge (by simpa [Nat.cast_natAbs, Int.cast_abs] using h)]
  simp

/-- `ψ_k(n) ≠ 0` forces `2^k / 4 < |n| < 2^k`. -/
theorem psiKz_ne_zero (ψ : PsiData) {k : ℕ} {n : ℤ} (h : psiKz ψ k n ≠ 0) :
    (2 : ℝ) ^ k / 4 < (n.natAbs : ℝ) ∧ (n.natAbs : ℝ) < (2 : ℝ) ^ k := by
  by_contra hc
  rw [not_and_or, not_lt, not_lt] at hc
  rcases hc with hc | hc
  · exact h (psiKz_eq_zero_of_le ψ hc)
  · exact h (psiKz_eq_zero_of_ge ψ hc)

/-- `ψ_k` is odd on `ℤ`. -/
theorem psiKz_neg (ψ : PsiData) (k : ℕ) (n : ℤ) : psiKz ψ k (-n) = -psiKz ψ k n := by
  unfold psiKz
  push_cast
  rw [ψ.psiK_odd]
  simp

/-- `ψ_k(0) = 0`. -/
theorem psiKz_zero (ψ : PsiData) (k : ℕ) : psiKz ψ k 0 = 0 := by
  have h := ψ.psiK_odd k 0
  simp only [neg_zero] at h
  unfold psiKz
  have : psiK ψ.toFun k 0 = 0 := by linarith
  simp [this]

/-- `M(k)` is nondecreasing in `k`. -/
theorem cutoffM_mono {k k' : ℕ} (h : k ≤ k') : cutoffM k ≤ cutoffM k' := by
  unfold cutoffM
  exact Real.exp_le_exp.2 (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h)
    (by norm_num))

/-- `j ∈ jSet k` iff `2^j ≤ M(k)`. -/
theorem mem_jSet_iff {k j : ℕ} : j ∈ jSet k ↔ (2 : ℝ) ^ j ≤ cutoffM k := by
  unfold jSet
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have hj : (j : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast (Nat.lt_two_pow_self (n := j)).le
  exact Nat.lt_succ_of_le (Nat.le_floor (hj.trans h))

/-- `j ∈ lowJ D₀ k` iff `2^j ≤ M(k)` and `2^j ≤ k^{D₀}`. -/
theorem mem_lowJ_iff {D₀ : ℝ} {k j : ℕ} :
    j ∈ lowJ D₀ k ↔ (2 : ℝ) ^ j ≤ cutoffM k ∧ (2 : ℝ) ^ j ≤ (k : ℝ) ^ D₀ := by
  unfold lowJ
  rw [Finset.mem_filter, mem_jSet_iff]

/-! ### Finite sums for finitely supported `f` -/

/-- The finite set of `n` with `f(x - n) ≠ 0`. -/
def suppAt (f : ℤ →₀ ℂ) (x : ℤ) : Finset ℤ := f.support.image fun m => x - m

/-- `f(x - n) = 0` off `suppAt f x`. -/
theorem apply_sub_eq_zero_of_not_mem_suppAt {f : ℤ →₀ ℂ} {x n : ℤ} (hn : n ∉ suppAt f x) :
    f (x - n) = 0 := by
  by_contra h
  apply hn
  unfold suppAt
  rw [Finset.mem_image]
  exact ⟨x - n, Finsupp.mem_support_iff.2 h, by ring⟩

/-- For finitely supported `f`, the modulated sum is the finite sum over `suppAt f x`. -/
theorem weightedModSum_eq_sum_of_finsupp (u : ℤ → ℂ) (f : ℤ →₀ ℂ) (lam : ℝ) (x : ℤ) :
    weightedModSum u (⇑f) lam x = ∑ n ∈ suppAt f x, f (x - n) * u n * e (lam * n) := by
  unfold weightedModSum
  exact tsum_eq_sum fun n hn => by simp [apply_sub_eq_zero_of_not_mem_suppAt hn]

/-- Any finite set `S ⊇ suppAt f x` computes the modulated sum. -/
theorem weightedModSum_eq_sum_of_superset (u : ℤ → ℂ) (f : ℤ →₀ ℂ) (lam : ℝ) (x : ℤ)
    {S : Finset ℤ} (hS : suppAt f x ⊆ S) :
    weightedModSum u (⇑f) lam x = ∑ n ∈ S, f (x - n) * u n * e (lam * n) := by
  unfold weightedModSum
  exact tsum_eq_sum fun n hn => by
    simp [apply_sub_eq_zero_of_not_mem_suppAt fun h => hn (hS h)]

/-- The modulated sum is additive in the weight (for finitely supported `f`). -/
theorem weightedModSum_add_weight (u v : ℤ → ℂ) (f : ℤ →₀ ℂ) (lam : ℝ) (x : ℤ) :
    weightedModSum (u + v) (⇑f) lam x =
      weightedModSum u (⇑f) lam x + weightedModSum v (⇑f) lam x := by
  simp only [weightedModSum_eq_sum_of_finsupp, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => by ring

/-- The modulated sum is a finite sum in the weight (for finitely supported `f`). -/
theorem weightedModSum_sum_weight {ι : Type*} (s : Finset ι) (u : ι → ℤ → ℂ) (f : ℤ →₀ ℂ)
    (lam : ℝ) (x : ℤ) :
    weightedModSum (fun n => ∑ i ∈ s, u i n) (⇑f) lam x =
      ∑ i ∈ s, weightedModSum (u i) (⇑f) lam x := by
  simp only [weightedModSum_eq_sum_of_finsupp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]

/-- The modulated sum with the negative weight. -/
theorem weightedModSum_neg_weight (u : ℤ → ℂ) (f : ℤ →₀ ℂ) (lam : ℝ) (x : ℤ) :
    weightedModSum (fun n => -u n) (⇑f) lam x = -weightedModSum u (⇑f) lam x := by
  simp only [weightedModSum_eq_sum_of_finsupp, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- The modulated sum is additive in `f` (finitely supported). -/
theorem weightedModSum_add_left (u : ℤ → ℂ) (f g : ℤ →₀ ℂ) (lam : ℝ) (x : ℤ) :
    weightedModSum u (⇑(f + g)) lam x =
      weightedModSum u (⇑f) lam x + weightedModSum u (⇑g) lam x := by
  classical
  have hS : suppAt (f + g) x ⊆ suppAt f x ∪ suppAt g x := by
    intro n hn
    by_contra h
    rw [Finset.mem_union, not_or] at h
    have h1 := apply_sub_eq_zero_of_not_mem_suppAt h.1
    have h2 := apply_sub_eq_zero_of_not_mem_suppAt h.2
    have h3 : (f + g) (x - n) = 0 := by simp [h1, h2]
    unfold suppAt at hn
    rw [Finset.mem_image] at hn
    obtain ⟨m, hm, hmn⟩ := hn
    rw [Finsupp.mem_support_iff] at hm
    have : m = x - n := by omega
    rw [this] at hm
    exact hm h3
  rw [weightedModSum_eq_sum_of_superset u (f + g) lam x hS,
    weightedModSum_eq_sum_of_superset u f lam x Finset.subset_union_left,
    weightedModSum_eq_sum_of_superset u g lam x Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [Finsupp.add_apply]
  ring

/-! ### Properties of `varOp` -/

/-- `varOp` of the zero weight vanishes. -/
theorem varOp_zero_weight {r : ℝ} (hr : 0 < r) (f : ℤ → ℂ) (x : ℤ) :
    varOp r 0 f x = 0 := by
  rw [varOp_eq]
  have : (fun lam => weightedModSum (0 : ℤ → ℂ) f lam x) = 0 := by
    funext lam
    simp [weightedModSum]
  rw [this]
  exact rVariationOn_zero hr _

/-- `varOp` is subadditive in the weight (finitely supported `f`, `r ≥ 1`). -/
theorem varOp_add_weight_le {r : ℝ} (hr : 1 ≤ r) (u v : ℤ → ℂ) (f : ℤ →₀ ℂ) (x : ℤ) :
    varOp r (u + v) (⇑f) x ≤ varOp r u (⇑f) x + varOp r v (⇑f) x := by
  rw [varOp_eq, varOp_eq, varOp_eq]
  have : (fun lam => weightedModSum (u + v) (⇑f) lam x) =
      (fun lam => weightedModSum u (⇑f) lam x) + (fun lam => weightedModSum v (⇑f) lam x) := by
    funext lam
    exact weightedModSum_add_weight u v f lam x
  rw [this]
  exact rVariationOn_add_le hr _ _ _

/-- `varOp` of a finite sum of weights is at most the sum of the `varOp`'s. -/
theorem varOp_sum_weight_le {ι : Type*} {r : ℝ} (hr : 1 ≤ r) (s : Finset ι) (u : ι → ℤ → ℂ)
    (f : ℤ →₀ ℂ) (x : ℤ) :
    varOp r (fun n => ∑ i ∈ s, u i n) (⇑f) x ≤ ∑ i ∈ s, varOp r (u i) (⇑f) x := by
  rw [varOp_eq]
  simp only [varOp_eq]
  have : (fun lam => weightedModSum (fun n => ∑ i ∈ s, u i n) (⇑f) lam x) =
      ∑ i ∈ s, fun lam => weightedModSum (u i) (⇑f) lam x := by
    funext lam
    rw [weightedModSum_sum_weight]
    simp
  rw [this]
  exact rVariationOn_sum_le s hr _ _

/-- `varOp` does not see the sign of the weight. -/
theorem varOp_neg_weight {r : ℝ} (hr : 0 < r) (u : ℤ → ℂ) (f : ℤ →₀ ℂ) (x : ℤ) :
    varOp r (fun n => -u n) (⇑f) x = varOp r u (⇑f) x := by
  rw [varOp_eq, varOp_eq]
  have : (fun lam => weightedModSum (fun n => -u n) (⇑f) lam x) =
      (-1 : ℂ) • (fun lam => weightedModSum u (⇑f) lam x) := by
    funext lam
    simp [weightedModSum_neg_weight]
  rw [this, rVariationOn_const_smul hr]
  simp

/-- `varOp` is subadditive in `f` (finitely supported, `r ≥ 1`). -/
theorem varOp_add_left_le {r : ℝ} (hr : 1 ≤ r) (u : ℤ → ℂ) (f g : ℤ →₀ ℂ) (x : ℤ) :
    varOp r u (⇑(f + g)) x ≤ varOp r u (⇑f) x + varOp r u (⇑g) x := by
  rw [varOp_eq, varOp_eq, varOp_eq]
  have : (fun lam => weightedModSum u (⇑(f + g)) lam x) =
      (fun lam => weightedModSum u (⇑f) lam x) + (fun lam => weightedModSum u (⇑g) lam x) := by
    funext lam
    exact weightedModSum_add_left u f g lam x
  rw [this]
  exact rVariationOn_add_le hr _ _ _

/-- `varOp` only depends on the weight at the points of `suppAt f x`. -/
theorem varOp_congr_of_finsupp {r : ℝ} {u v : ℤ → ℂ} (f : ℤ →₀ ℂ) (x : ℤ)
    (h : ∀ n ∈ suppAt f x, u n = v n) : varOp r u (⇑f) x = varOp r v (⇑f) x := by
  rw [varOp_eq, varOp_eq]
  congr 1
  funext lam
  rw [weightedModSum_eq_sum_of_finsupp, weightedModSum_eq_sum_of_finsupp]
  exact Finset.sum_congr rfl fun n hn => by rw [h n hn]

/-! ### The operator and the operators `V^{Q,r}` as `varOp` -/

/-- The weight `n ↦ w(|n|)/n` (`n ≠ 0`, `0` at `n = 0`) of the `modulatedSum` for the
von Mangoldt weight (`e:Carweight`). -/
def hilbW (n : ℤ) : ℂ := if n = 0 then 0 else wFun n / (n : ℂ)

/-- The modulated sum for the von Mangoldt weight is `weightedModSum` for `hilbW`. -/
theorem modulatedSum_vonMangoldt_eq_hilbW (f : ℤ →₀ ℂ) (lam : ℝ) (x : ℤ) :
    modulatedSum (ArithmeticFunction.vonMangoldt : ℕ → ℝ) f lam x =
      weightedModSum hilbW (⇑f) lam x := by
  rw [modulatedSum_eq_weightedModSum]
  unfold weightedModSum
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · simp [hilbW, hn]
  · simp [hilbW, wFun, hn]

/-- The `primeVariation` is `varOp` for the weight `w(|n|)/n`. -/
theorem primeVariation_eq_varOp (r : ℝ) (f : ℤ →₀ ℂ) (x : ℤ) :
    primeVariation r f x = varOp r hilbW (⇑f) x := by
  unfold primeVariation varOp pointwiseVariation
  simp only [rVariation_eq_rVariationOn, modulatedSum_vonMangoldt_eq_hilbW]

/-- `V^{Q,r} f = varOp r (w_Q K_Q) f` (`e:CQvar`). -/
theorem VQr_eq_varOp (S : KQSetup) (r : ℝ) (Q : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    S.VQr r Q f x = varOp r (fun n => wQ Q n * S.KQz Q n) f x := rfl

end PrimeCarleson.Proof.Paper

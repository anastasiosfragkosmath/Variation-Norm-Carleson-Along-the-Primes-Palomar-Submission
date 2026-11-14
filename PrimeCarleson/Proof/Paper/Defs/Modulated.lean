module

public import PrimeCarleson.Proof.Paper.Defs.Norms
public import PrimeCarleson.Proof.Paper.Defs.Basic
public import PrimeCarleson.Frozen.ModulatedSum

/-!
# Modulated sums and averages

The families of operators indexed by the frequency `λ` (`sources/Variational_Carleson.tex`
L930, L1072, L1943): for functions `w, f : ℤ → ℂ`

* `weightedModSum w f lam x = T^w_λ f(x) := ∑_n f(x - n) w(n) e(λ n)` (L1072); with
  `w = w_Q K_Q` this is `T^Q_λ f(x) = ∑_n f(x - n) w_Q(n) K_Q(n) e(λ n)` (L1943), and
  `modulatedSum_eq_weightedModSum` identifies the `PrimeCarleson.modulatedSum`
  (with `w : ℕ → ℝ`, `1/n` built in) as `T^{w'}_λ` for the odd-extended weight
  `w'(n) = w(|n|)/n`, `w'(0) = 0`;
* `modAverage N w f lam x = A_λ f(x) := E_{n ∈ [N]} f(x - n) w(n) e(λ n)` (L930), with
  `modAverage_eq_weightedModSum`: `A_λ f = N⁻¹ T^{w 1_{[N]}}_λ f`.

Basic API: the sum is finite when `w` has finite support (`weightedModSum_eq_sum`) and
`1`-periodicity in `λ` (`weightedModSum_add_intCast`, so `λ ∈ 𝕋 = [0, 1)` is no loss).
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-- The modulated sum `T^w_λ f(x) := ∑_n f(x - n) w(n) e(λ n)` (L1072; `T^Q_λ` of L1943 is the
case `w = w_Q K_Q`), a sum over `ℤ` (finitely many nonzero terms when `f` or `w` has finite
support). -/
def weightedModSum (w f : ℤ → ℂ) (lam : ℝ) (x : ℤ) : ℂ :=
  ∑' n : ℤ, f (x - n) * w n * e (lam * n)

/-- The modulated average `A_λ f(x) := E_{n ∈ [N]} f(x - n) w(n) e(λ n)` (L930), for
`N : ℕ+` and `w : [N] → ℂ` (extended arbitrarily; only the values on `[N]` enter). -/
def modAverage (N : ℕ+) (w f : ℤ → ℂ) (lam : ℝ) (x : ℤ) : ℂ :=
  expect (bracket N) fun n => f (x - n) * w n * e (lam * n)

/-- `A_λ f(x) = N⁻¹ ∑_{n ∈ [N]} f(x - n) w(n) e(λ n)`. -/
theorem modAverage_eq (N : ℕ+) (w f : ℤ → ℂ) (lam : ℝ) (x : ℤ) :
    modAverage N w f lam x =
      (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc (1 : ℤ) N, f (x - n) * w n * e (lam * n) :=
  expect_bracket N _

/-- The sum defining `T^w_λ f(x)` is the finite sum over any finite set carrying the support
of `w`. -/
theorem weightedModSum_eq_sum (w f : ℤ → ℂ) (lam : ℝ) (x : ℤ) (S : Finset ℤ)
    (hS : ∀ n, n ∉ S → w n = 0) :
    weightedModSum w f lam x = ∑ n ∈ S, f (x - n) * w n * e (lam * n) :=
  tsum_eq_sum fun n hn => by simp [hS n hn]

/-- `A_λ f = N⁻¹ T^{w 1_{[N]}}_λ f`. -/
theorem modAverage_eq_weightedModSum (N : ℕ+) (w f : ℤ → ℂ) (lam : ℝ) (x : ℤ) :
    modAverage N w f lam x =
      (N : ℂ)⁻¹ * weightedModSum (fun n => if n ∈ bracket N then w n else 0) f lam x := by
  classical
  rw [modAverage_eq, weightedModSum_eq_sum _ f lam x (bracket N) (fun n hn => by simp [hn])]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have : n ∈ bracket N := hn
  simp [this]

/-- The `modulatedSum` is `T^{w'}_λ` for the odd-extended weight `w'(n) = w(|n|)/n`,
`w'(0) = 0` (the `1/n` of `e:Carweight`, `e:CP` built into the weight). -/
theorem modulatedSum_eq_weightedModSum (w : ℕ → ℝ) (f : ℤ →₀ ℂ) (lam : ℝ) (x : ℤ) :
    modulatedSum w f lam x =
      weightedModSum (fun n => if n = 0 then 0 else (w n.natAbs : ℂ) / (n : ℂ)) (⇑f) lam x := by
  unfold modulatedSum weightedModSum
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ite_false]
    ring

/-- The modulated sum is `1`-periodic in `λ`: `T^w_{λ + k} = T^w_λ` for `k ∈ ℤ`. -/
theorem weightedModSum_add_intCast (w f : ℤ → ℂ) (lam : ℝ) (k : ℤ) (x : ℤ) :
    weightedModSum w f (lam + k) x = weightedModSum w f lam x := by
  unfold weightedModSum
  refine tsum_congr fun n => ?_
  have : (lam + k) * (n : ℝ) = lam * n + ((k * n : ℤ) : ℝ) := by push_cast; ring
  rw [this, e_add_intCast]

/-- The zero weight gives the zero sum. -/
theorem weightedModSum_zero_weight (f : ℤ → ℂ) (lam : ℝ) (x : ℤ) :
    weightedModSum 0 f lam x = 0 := by
  simp [weightedModSum]

end PrimeCarleson.Proof.Paper

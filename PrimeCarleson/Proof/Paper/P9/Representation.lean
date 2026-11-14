module

public import PrimeCarleson.Proof.Paper.P9.VariableMain
public import PrimeCarleson.Proof.Paper.P5.Support
public import PrimeCarleson.Proof.Paper.P5.KQProps
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Fourier representation of `T^Q_λ f` and the smooth Fourier restriction

Source: main paper `p:global-shell-var`, L1971–L1983 and L2002–L2019.

* `invFZ_KQmult`: for the multiplier `m_λ(β) = K̂_Q(β - λ)` supported in the chart,
  `invFZ θ m_λ (z) = e(λ z) K_Q(z)` (the kernel of `K_λ`);
* `exists_theta`: the smooth cutoff `ϑ` (`= 1` on `J + [-ℓ/4, ℓ/4]`, `= 0` off `3J`,
  `J = [u, u + ℓ]`), the smooth Fourier restriction of `f` to `a/q + 3J` is
  `f̂_{a/q}(β) = ϑ(β) f̂(β + a/q)` (`densR`, with the weight `μ(q)/φ(q)`, i.e. `F_{a/q}`);
  its density is supported in `3J`, as for the sharp cutoff `1_{1.1J}` of the paper (L1977–L1982);
* `TQ_eq_aSum` (the Fourier representation, L2002–L2019): for `λ` such that `ϑ = 1` on
  `λ + supp K̂_Q`, `T^Q_λ f(x) = ∑_{a/q ∈ Γ_Q} e(a x/q) (K_λ * F_{a/q})(x)`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap ContDiff

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

namespace KQSetup

variable (S : KQSetup)

/-- The multiplier `m_λ(β) = K̂_Q(β - λ)` of `K_λ` (`K_λ(n) = K_Q(n) e(λ n)`). -/
def KQmult (Q : ℕ) (lam β : ℝ) : ℂ := S.KQhat Q (β - lam)

theorem measurable_KQmult (Q : ℕ) (lam : ℝ) : Measurable (S.KQmult Q lam) :=
  (S.measurable_KQhat Q).comp (measurable_id.sub_const lam)

/-- **The kernel of `K_λ`**: if `supp m_λ` lies in the chart `(θ, θ + 1)` then
`invFZ θ m_λ (z) = e(λ z) K_Q(z)`. -/
theorem invFZ_KQmult (Q : ℕ) {θ lam : ℝ} (hlo : θ < lam - S.δ / S.P.NQ Q)
    (hhi : lam + S.δ / S.P.NQ Q < θ + 1) (z : ℤ) :
    invFZ θ (S.KQmult Q lam) z = e (lam * z) * S.KQz Q z := by
  unfold invFZ KQmult KQz KQ
  rw [intervalIntegral.integral_of_le (by linarith)]
  have h1 : ∫ β in Set.Ioc θ (θ + 1), S.KQhat Q (β - lam) * e ((z : ℝ) * β) =
      ∫ β, S.KQhat Q (β - lam) * e ((z : ℝ) * β) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun β hβ => ?_
    rw [S.KQhat_eq_zero Q ?_, zero_mul]
    by_contra hle
    push Not at hle
    apply hβ
    rw [abs_le] at hle
    constructor <;> linarith [hle.1, hle.2]
  rw [h1]
  have h2 : ∀ β : ℝ, S.KQhat Q (β - lam) * e ((z : ℝ) * β) =
      e (lam * z) * (S.KQhat Q (β - lam) * e ((z : ℝ) * (β - lam))) := by
    intro β
    have : e ((z : ℝ) * β) = e (lam * z) * e ((z : ℝ) * (β - lam)) := by
      rw [← e_add]; congr 1; ring
    rw [this]; ring
  simp_rw [h2]
  rw [integral_const_mul]
  congr 1
  exact integral_sub_right_eq_self (fun ξ => S.KQhat Q ξ * e ((z : ℝ) * ξ)) lam

/-- The multiplier `m_λ` is square integrable on every chart (it is bounded). -/
theorem chartL2_KQmult (Q : ℕ) (lam θ : ℝ) : ChartL2 θ (S.KQmult Q lam) := by
  obtain ⟨C, _, hC⟩ := S.KQhat_bv
  exact ChartL2.of_bound (S.measurable_KQmult Q lam).aestronglyMeasurable (M := C)
    fun β _ => (hC S.P Q).1 _ |> fun h => by simpa [KQmult] using h

end KQSetup

/-- A smooth cutoff `ϑ` for `J = [u, u + ℓ]`: `0 ≤ ϑ ≤ 1`, `ϑ = 1` on `J + [-ℓ/4, ℓ/4]`, `ϑ = 0`
off `3J = [u - ℓ, u + 2ℓ]`. -/
theorem exists_theta (u ℓ : ℝ) (hℓ : 0 < ℓ) :
    ∃ ϑ : ℝ → ℝ, ContDiff ℝ ∞ ϑ ∧ (∀ x, 0 ≤ ϑ x ∧ ϑ x ≤ 1) ∧
      (∀ x ∈ Set.Icc (u - ℓ / 4) (u + ℓ + ℓ / 4), ϑ x = 1) ∧
      (∀ x, x ∉ Set.Icc (u - ℓ) (u + 2 * ℓ) → ϑ x = 0) := by
  let bump : ContDiffBump (u + ℓ / 2) := ⟨3 * ℓ / 4, 3 * ℓ / 2, by linarith, by linarith⟩
  refine ⟨fun x => bump x, bump.contDiff, fun x => ⟨bump.nonneg, bump.le_one⟩, fun x hx => ?_,
    fun x hx => ?_⟩
  · apply bump.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> simp only [bump] <;> linarith [hx.1, hx.2]
  · apply bump.zero_of_le_dist
    rw [Real.dist_eq]
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    change 3 * ℓ / 2 ≤ |x - (u + ℓ / 2)|
    rcases hx with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith

/-- The weight `μ(q)/φ(q)` of the reduced fraction `a/q = r` (the coefficient of `e(n a/q)` in
`w_Q(n)`, `e:WQ`). -/
def gcoef (r : ℚ) : ℂ :=
  (((ArithmeticFunction.moebius r.den : ℤ) : ℝ) / (Nat.totient r.den : ℝ) : ℂ)

/-- Modulation of a finitely supported sequence: `f(k) e(-γ k)`; its Fourier series is
`β ↦ f̂(β + γ)`. -/
def modF (f : ℤ →₀ ℂ) (γ : ℝ) : ℤ →₀ ℂ :=
  Finsupp.onFinset f.support (fun k => f k * e (-(γ * (k : ℝ)))) (fun k hk => by
    by_contra h
    exact hk (by simp [Finsupp.notMem_support_iff.1 h]))

theorem fourierZ_modF (f : ℤ →₀ ℂ) (γ β : ℝ) : fourierZ (modF f γ) β = fourierZ f (β + γ) := by
  rw [fourierZ_eq_sum_of_support_subset (modF f γ) (S := f.support) (fun k hk => by
    simp only [Finsupp.mem_support_iff, modF, Finsupp.onFinset_apply] at hk ⊢
    intro h; exact hk (by simp [h])), fourierZ_eq_sum_of_support_subset f (subset_refl _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [modF, Finsupp.onFinset_apply]
  rw [mul_assoc, ← e_add]
  congr 2
  ring

/-- The densities `F_{a/q}`: `f̂_{a/q}(β) = ϑ(β) f̂(β + a/q)`, times the weight `μ(q)/φ(q)`. -/
def densR (ϑ : ℝ → ℝ) (f : ℤ →₀ ℂ) (r : ℚ) (β : ℝ) : ℂ :=
  gcoef r * (ϑ β : ℂ) * fourierZ f (β + (r : ℝ))

/-- For finitely supported `f`, `T^Q_λ f(x)` is a finite sum over `supp f`:
`∑_{k ∈ supp f} f(k) w_Q(x - k) K_Q(x - k) e(λ (x - k))` (so `λ ↦ T^Q_λ f(x)` is continuous). -/
theorem KQSetup.TQ_eq_sum (S : KQSetup) (Q : ℕ) (lam : ℝ) (f : ℤ →₀ ℂ) (x : ℤ) :
    S.TQ Q lam f x = ∑ k ∈ f.support,
      f k * (wQ Q (x - k) * S.KQz Q (x - k)) * e (lam * ((x - k : ℤ) : ℝ)) := by
  unfold KQSetup.TQ weightedModSum
  rw [← (Equiv.subLeft x).tsum_eq]
  rw [tsum_eq_sum (s := f.support)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [Equiv.subLeft_apply]
  · intro k hk
    simp [Finsupp.notMem_support_iff.1 hk]

theorem KQSetup.continuous_TQ (S : KQSetup) (Q : ℕ) (f : ℤ →₀ ℂ) (x : ℤ) :
    Continuous fun lam : ℝ => S.TQ Q lam f x := by
  simp_rw [S.TQ_eq_sum Q _ f x]
  exact continuous_finsetSum _ fun k _ =>
    continuous_const.mul (continuous_e.comp (continuous_id.mul continuous_const))

/-- **The Fourier representation** (Source: main paper `p:global-shell-var`, L2002–L2019): for `λ`
in the interval `J` (so that `ϑ = 1` on `λ + supp K̂_Q` and the chart contains `λ + supp K̂_Q`),
`T^Q_λ f(x) = ∑_{a/q ∈ Γ_Q} e(a x/q) (K_λ * F_{a/q})(x)`, `F_{a/q}` with density `densR`. -/
theorem KQSetup.TQ_eq_aSum (S : KQSetup) (Q : ℕ) {θ lam : ℝ} {ϑ : ℝ → ℝ}
    (hlo : θ < lam - S.δ / S.P.NQ Q) (hhi : lam + S.δ / S.P.NQ Q < θ + 1)
    (hϑ : ∀ β : ℝ, S.KQhat Q (β - lam) ≠ 0 → ϑ β = 1) (f : ℤ →₀ ℂ) (x : ℤ) :
    S.TQ Q lam f x = aSum θ (fun (r : ↥(gammaQ Q)) (z : ℤ) => e ((r : ℚ) * (z : ℝ)))
      (fun t β => S.KQmult Q t β) (fun (r : ↥(gammaQ Q)) β => densR ϑ f r β) lam x := by
  classical
  -- the left side as a finite sum over the support of `f`
  have hL := S.TQ_eq_sum Q lam f x
  -- the right side
  have hR : ∀ r : ↥(gammaQ Q), (e ((r : ℚ) * (x : ℝ))) * KSeq θ (fun t β => S.KQmult Q t β)
      (fun (r : ↥(gammaQ Q)) β => densR ϑ f r β) lam r x =
      ∑ k ∈ f.support, gcoef r * (f k * e (((r : ℚ) : ℝ) * ((x - k : ℤ) : ℝ))) *
        (S.KQz Q (x - k) * e (lam * ((x - k : ℤ) : ℝ))) := by
    intro r
    have h1 : (fun β => S.KQmult Q lam β * densR ϑ f r β) =
        fun β => gcoef r * (S.KQmult Q lam β * fourierZ (modF f (r : ℝ)) β) := by
      funext β
      rw [fourierZ_modF]
      unfold densR
      by_cases h0 : S.KQhat Q (β - lam) = 0
      · simp [KQSetup.KQmult, h0]
      · rw [hϑ β h0]; simp only [KQSetup.KQmult]; push_cast; ring
    unfold KSeq
    rw [h1, invFZ_const_mul,
      ← invFZ_conv_fourierZ (S.chartL2_KQmult Q lam θ) (modF f (r : ℝ)) x]
    rw [Finset.sum_subset (s₁ := (modF f (r : ℝ)).support) (s₂ := f.support) (fun k hk => by
        simp only [Finsupp.mem_support_iff, modF, Finsupp.onFinset_apply] at hk ⊢
        intro h; exact hk (by simp [h])) (fun k _ hk => by
        simp [Finsupp.notMem_support_iff.1 hk])]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [S.invFZ_KQmult Q hlo hhi]
    simp only [modF, Finsupp.onFinset_apply]
    have : e (((r : ℚ) : ℝ) * (x : ℝ)) * e (-(((r : ℚ) : ℝ) * (k : ℝ))) =
        e (((r : ℚ) : ℝ) * ((x - k : ℤ) : ℝ)) := by
      rw [← e_add]; congr 1; push_cast; ring
    rw [← this]
    push_cast
    ring
  unfold aSum
  rw [hL, Finset.sum_congr rfl fun r _ => hR r, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [wQ_eq_sum_gammaQ, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_coe_sort (gammaQ Q)]
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold gcoef
  rw [mul_comm ((x - k : ℤ) : ℝ) ((r : ℚ) : ℝ)]
  ring

end PrimeCarleson.Proof.Paper

module

public import PrimeCarleson.Proof.Paper.P6a.Basic
public import PrimeCarleson.Proof.Paper.P7.Sums

/-!
# The Möbius expansion of `V^{Q,r}` and `C^Q`

Source: main paper `l:red-var-l2`, L1599–L1620. With
`w_Q(n) = ∑_{Q/2 < q ≤ Q} μ(q)/φ(q) c_q(n)` and `c_q(n) = ∑_{d ∣ q} d μ(q/d) 1_{d ∣ n}`,

`T^Q_λ f(x) = ∑_{Q/2 < q ≤ Q} ∑_{d ∣ q} (μ(q) μ(q/d)/φ(q)) ∑_m f(x - dm) K_{Q,d}(m) e(λ d m)`,

and the inner sum is `dilSum K̂_{Q,d} d f x (d λ)` (`dilSum k̂ d f x λ = ∑_m f(x - dm) e(λ m) k(m)`
with `k = K_{Q,d}`, `K_{Q,d}(m) = d K_Q(dm)`). Hence the triangle inequality for `V^r` and for the
supremum give the pointwise bounds `VQr_le_mobius` and `CQ_le_mobius`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

/-- The coefficient `μ(q) μ(q/d) / φ(q)` of the Möbius expansion of `w_Q`. -/
def mobCoef (q d : ℕ) : ℂ :=
  (((ArithmeticFunction.moebius q : ℤ) : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)) /
    (Nat.totient q : ℂ)

/-- `|μ(q) μ(q/d) / φ(q)| ≤ 1/φ(q)`. -/
theorem enorm_mobCoef_le (q d : ℕ) :
    ‖mobCoef q d‖ₑ ≤ ENNReal.ofReal (1 / (Nat.totient q : ℝ)) := by
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  unfold mobCoef
  rw [norm_div, norm_mul, one_div]
  have h1 : ‖((ArithmeticFunction.moebius q : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have h2 : ‖((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have h3 : ‖(Nat.totient q : ℂ)‖ = (Nat.totient q : ℝ) := by
    rw [Complex.norm_natCast]
  rw [h3, div_eq_mul_inv]
  refine mul_le_of_le_one_left (inv_nonneg.2 (Nat.cast_nonneg _)) ?_
  calc ‖((ArithmeticFunction.moebius q : ℤ) : ℂ)‖ * ‖((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)‖
      ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The kernel `1_{d ∣ n} d K(n)` (the weight `d K_Q(dm)` at `n = d m`). -/
def dvdKernel (K : ℤ → ℂ) (d : ℕ) (n : ℤ) : ℂ := if (d : ℤ) ∣ n then (d : ℂ) * K n else 0

/-- **The Möbius expansion of the weight** (L1599-L1608):
`w_Q(n) K(n) = ∑_{Q/2 < q ≤ Q} ∑_{d ∣ q} (μ(q) μ(q/d)/φ(q)) 1_{d ∣ n} d K(n)`. -/
theorem wQ_mul_eq_sum (Q : ℕ) (K : ℤ → ℂ) (n : ℤ) :
    wQ Q n * K n = ∑ q ∈ Finset.Ioc (Q / 2) Q, ∑ d ∈ q.divisors, mobCoef q d * dvdKernel K d n := by
  unfold wQ blockWeight
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [ramanujanSum_eq_intCast, Finset.sum_filter]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases h : (d : ℤ) ∣ n
  · simp only [h, ite_true, mobCoef, dvdKernel]
    ring
  · simp [h, dvdKernel]

/-- Scalars factor out of the modulated sum. -/
theorem weightedModSum_const_mul_weight (c : ℂ) (u : ℤ → ℂ) (f : ℤ → ℂ) (lam : ℝ) (x : ℤ) :
    weightedModSum (fun n => c * u n) f lam x = c * weightedModSum u f lam x := by
  unfold weightedModSum
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

/-- `T^Q_λ f(x) = ∑_q ∑_{d ∣ q} (μ(q) μ(q/d)/φ(q)) T^{1_{d ∣ ·} d K_Q}_λ f(x)`. -/
theorem TQ_eq_mobius (S : KQSetup) (Q : ℕ) (f : ℤ →₀ ℂ) (lam : ℝ) (x : ℤ) :
    S.TQ Q lam (⇑f) x = ∑ q ∈ Finset.Ioc (Q / 2) Q, ∑ d ∈ q.divisors,
      mobCoef q d * weightedModSum (dvdKernel (S.KQz Q) d) (⇑f) lam x := by
  unfold KQSetup.TQ
  have h1 : (fun n => wQ Q n * S.KQz Q n) = fun n => ∑ q ∈ Finset.Ioc (Q / 2) Q,
      ∑ d ∈ q.divisors, mobCoef q d * dvdKernel (S.KQz Q) d n := funext fun n =>
    wQ_mul_eq_sum Q _ n
  rw [h1, weightedModSum_sum_weight]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [weightedModSum_sum_weight]
  exact Finset.sum_congr rfl fun d _ => weightedModSum_const_mul_weight _ _ _ _ _

/-- **The dilation identity**: for `d ≥ 1`,
`∑_n f(x - n) 1_{d ∣ n} d K_Q(n) e(λ n) = ∑_m f(x - dm) K_{Q,d}(m) e(dλ m)`, which is
`dilSum K̂_{Q,d} d f x (d λ)`. -/
theorem weightedModSum_dvdKernel (S : KQSetup) {d : ℕ} (hd : 1 ≤ d) (Q : ℕ) (f : ℤ →₀ ℂ)
    (lam : ℝ) (x : ℤ) :
    weightedModSum (dvdKernel (S.KQz Q) d) (⇑f) lam x =
      dilSum (S.KQdhat Q d) (d : ℤ) f x ((d : ℝ) * lam) := by
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hinj : Function.Injective (fun m : ℤ => (d : ℤ) * m) := fun a b h =>
    mul_left_cancel₀ hd0 h
  unfold weightedModSum dilSum
  rw [← hinj.tsum_eq]
  · refine tsum_congr fun m => ?_
    have h1 : dvdKernel (S.KQz Q) d ((d : ℤ) * m) = (d : ℂ) * S.KQz Q ((d : ℤ) * m) := by
      simp [dvdKernel]
    have h2 : (∫ ξ : ℝ, S.KQdhat Q d ξ * e ((m : ℝ) * ξ)) = (d : ℂ) * S.KQz Q ((d : ℤ) * m) :=
      (S.KQd_eq_integral hd Q m).symm
    have h3 : e (lam * (((d : ℤ) * m : ℤ) : ℝ)) = e (((d : ℝ) * lam) * (m : ℝ)) := by
      congr 1; push_cast; ring
    simp only [h1, h2, h3]
    ring
  · intro n hn
    rw [Function.mem_support] at hn
    have : dvdKernel (S.KQz Q) d n ≠ 0 := fun h => hn (by simp [h])
    unfold dvdKernel at this
    by_cases h : (d : ℤ) ∣ n
    · obtain ⟨m, rfl⟩ := h
      exact ⟨m, rfl⟩
    · exact absurd (by simp [h]) this

/-- The dilated modulated sum is `1`-periodic in `λ`. -/
theorem dilSum_periodic (khat : ℝ → ℂ) (Q : ℤ) (f : ℤ →₀ ℂ) (x : ℤ) :
    Function.Periodic (fun lam => dilSum khat Q f x lam) 1 := by
  intro lam
  unfold dilSum
  refine tsum_congr fun n => ?_
  have : (lam + 1) * (n : ℝ) = lam * n + ((n : ℤ) : ℝ) := by ring
  simp only [this, e_add_intCast]

/-- `T^Q_λ f(x) = ∑_{(q, d)} c_{q,d} a_d(dλ)`, `a_d` the dilated sum `dilSum K̂_{Q,d} d f x`. -/
theorem TQ_eq_dilSum (S : KQSetup) (Q : ℕ) (f : ℤ →₀ ℂ) (lam : ℝ) (x : ℤ) :
    S.TQ Q lam (⇑f) x = ∑ q ∈ Finset.Ioc (Q / 2) Q, ∑ d ∈ q.divisors,
      mobCoef q d * dilSum (S.KQdhat Q d) (d : ℤ) f x ((d : ℝ) * lam) := by
  rw [TQ_eq_mobius]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun d hd => ?_
  rw [weightedModSum_dvdKernel S (Nat.pos_of_mem_divisors hd) Q f lam x]

/-- **The Möbius expansion** (Source: main paper `l:red-var-l2`, L1610–L1620), variational form: for
`r ≥ 1`,
`V^{Q,r} f(x) ≤ ∑_{Q/2 < q ≤ Q} φ(q)⁻¹ ∑_{d ∣ q} V^r(∑_m f(x - dm) K_{Q,d}(m) e(λ d m) : λ)` with
`λ ∈ [0, 1)`. -/
theorem VQr_le_mobius (S : KQSetup) {r : ℝ} (hr : 1 ≤ r) (Q : ℕ) (f : ℤ →₀ ℂ) (x : ℤ) :
    S.VQr r Q (⇑f) x ≤ ∑ q ∈ Finset.Ioc (Q / 2) Q, ENNReal.ofReal (1 / (Nat.totient q : ℝ)) *
      ∑ d ∈ q.divisors, rVariationOn r (Set.Ico 0 1)
        (fun lam => dilSum (S.KQdhat Q d) (d : ℤ) f x ((d : ℝ) * lam)) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hVQ : S.VQr r Q (⇑f) x = rVariationOn r (Set.Ico 0 1) (fun lam => S.TQ Q lam (⇑f) x) :=
    rfl
  have hfun : (fun lam => S.TQ Q lam (⇑f) x) = ∑ q ∈ Finset.Ioc (Q / 2) Q,
      ∑ d ∈ q.divisors, mobCoef q d • (fun lam : ℝ =>
        dilSum (S.KQdhat Q d) (d : ℤ) f x ((d : ℝ) * lam)) := by
    funext lam
    rw [TQ_eq_dilSum]
    simp [Finset.sum_apply]
  rw [hVQ, hfun]
  refine (rVariationOn_sum_le _ hr _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  refine (rVariationOn_sum_le _ hr _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [rVariationOn_const_smul hr0]
  exact mul_le_mul_left (enorm_mobCoef_le q d) _

/-- **The Möbius expansion**, maximal form: for every `f` and `x`,
`C^Q f(x) ≤ ∑_{Q/2 < q ≤ Q} φ(q)⁻¹ ∑_{d ∣ q} sup_{λ ∈ [0, 1)} |∑_m f(x - dm) K_{Q,d}(m) e(λ m)|`
(the change of variables `λ ↦ dλ` costs nothing, by periodicity). -/
theorem CQ_le_mobius (S : KQSetup) (Q : ℕ) (f : ℤ →₀ ℂ) (x : ℤ) :
    S.CQ Q (⇑f) x ≤ ∑ q ∈ Finset.Ioc (Q / 2) Q, ENNReal.ofReal (1 / (Nat.totient q : ℝ)) *
      ∑ d ∈ q.divisors, ⨆ lam ∈ Set.Ico (0 : ℝ) 1,
        ‖dilSum (S.KQdhat Q d) (d : ℤ) f x lam‖ₑ := by
  unfold KQSetup.CQ
  refine iSup₂_le fun lam _ => ?_
  rw [TQ_eq_dilSum]
  refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  refine (enorm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [enorm_mul]
  refine mul_le_mul (enorm_mobCoef_le q d) ?_ zero_le zero_le
  have hper := (dilSum_periodic (S.KQdhat Q d) (d : ℤ) f x).sub_int_mul_eq
    (⌊(d : ℝ) * lam⌋) (x := (d : ℝ) * lam)
  rw [mul_one] at hper
  rw [← hper]
  exact le_iSup₂_of_le (Int.fract ((d : ℝ) * lam)) ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩ le_rfl

end PrimeCarleson.Proof.Paper

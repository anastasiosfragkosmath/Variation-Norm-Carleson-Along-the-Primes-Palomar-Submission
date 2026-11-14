module

public import PrimeCarleson.Proof.Oplus.SquareFunction.Coarse
public import PrimeCarleson.Proof.Oplus.SquareFunction.Fine
public import PrimeCarleson.Proof.Oplus.SquareFunction.Orthogonality

/-!
# Per-scale bounds for `A_k D_j f - E_k D_j f`

The operator `T_k g = A_k g - E_k g` of the square-function estimate of
Jones–Kaufman–Rosenblatt–Wierdl (proved here). For the martingale difference
`D_j f = E_{j-1} f - E_j f` of an `L²` function `f`:

* for `j ≤ k`, `E_k D_j f = 0`, so `T_k D_j f = A_k D_j f` and the coarse bound gives
  `‖T_k D_j f‖₂ ≤ Kθ 2^{-(k-j)} ‖D_j f‖₂`;
* for `k < j`, `E_k D_j f = D_j f` (since `D_j f` is constant on the intervals of length
  `2^{j-1} ≥ 2^k`), so `T_k D_j f = A_k D_j f - D_j f` and the fine bound gives
  `‖T_k D_j f‖₂ ≤ B (√2)^{k-j} ‖D_j f‖₂`.

Both bounds are of the form `‖T_k D_j f‖₂ ≤ ρ(k - j) ‖D_j f‖₂` with the summable
`ρ = ofReal ∘ sqRate A B`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal SchwartzMap

open PrimeCarleson.Proof.Lepingle

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- `T_k g = A_k g - E_k g`. -/
def schwartzSqOp (ψ : ℝ → ℂ) (k : ℤ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => schwartzAvg ψ k g x - dyadicAvg g k x

/-! ### The rate function -/

/-- The decay profile `ρ(m) = A 2^{-m}` for `m ≥ 0` and `ρ(m) = B (√2)^m` for `m < 0`. -/
def sqRate (A B : ℝ) (m : ℤ) : ℝ :=
  if 0 ≤ m then A * (2 : ℝ) ^ (-m) else B * (Real.sqrt 2) ^ m

/-- `((√2)^m)² = 2^m` for `m ∈ ℤ`. -/
theorem sqrt_two_zpow_sq (m : ℤ) : ((Real.sqrt 2) ^ m) ^ 2 = (2 : ℝ) ^ m := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, Real.sq_sqrt (by norm_num)]

/-- The rate function is summable (in `ℝ≥0∞`). -/
theorem tsum_ofReal_sqRate_lt_top {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∑' m : ℤ, ENNReal.ofReal (sqRate A B m) < ∞ := by
  set q : ℝ := (Real.sqrt 2)⁻¹ with hq
  have hs1 : 1 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hq0 : 0 < q := inv_pos.2 (by linarith)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ hs1
  have hhalf : (1 : ℝ) / 2 ≤ q := by
    rw [hq, one_div]
    refine inv_anti₀ (by linarith) ?_
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith
  set r : ℝ≥0∞ := ENNReal.ofReal q with hr
  have hr1 : r < 1 := by
    rw [hr]
    exact (ENNReal.ofReal_lt_one).2 hq1
  have hgeom : ∑' n : ℕ, r ^ n < ∞ := by
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_lt_top.2 (tsub_pos_of_lt hr1)
  rw [tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · calc ∑' n : ℕ, ENNReal.ofReal (sqRate A B (n : ℤ))
        ≤ ∑' n : ℕ, ENNReal.ofReal A * r ^ n := by
          refine ENNReal.tsum_le_tsum fun n => ?_
          simp only [sqRate, Int.natCast_nonneg, ite_true]
          rw [ENNReal.ofReal_mul hA, hr, ← ENNReal.ofReal_pow hq0.le]
          refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
          rw [zpow_neg, zpow_natCast, ← inv_pow, ← one_div]
          exact pow_le_pow_left₀ (by norm_num) hhalf n
      _ = ENNReal.ofReal A * ∑' n : ℕ, r ^ n := ENNReal.tsum_mul_left
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgeom
  · calc ∑' n : ℕ, ENNReal.ofReal (sqRate A B (-((n : ℤ) + 1)))
        ≤ ∑' n : ℕ, ENNReal.ofReal B * r ^ (n + 1) := by
          refine ENNReal.tsum_le_tsum fun n => ?_
          have hneg : ¬ (0 ≤ -((n : ℤ) + 1)) := by omega
          simp only [sqRate, hneg, ite_false]
          rw [ENNReal.ofReal_mul hB, hr, ← ENNReal.ofReal_pow hq0.le]
          refine le_of_eq ?_
          congr 2
          rw [zpow_neg, ← Nat.cast_one, ← Nat.cast_add, zpow_natCast, hq, inv_pow]
      _ = ENNReal.ofReal B * ∑' n : ℕ, r ^ (n + 1) := ENNReal.tsum_mul_left
      _ < ∞ := by
          refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
          simp_rw [pow_succ]
          rw [ENNReal.tsum_mul_right]
          exact ENNReal.mul_lt_top hgeom (hr1.trans ENNReal.one_lt_top)

/-! ### From squared norms to norms -/

theorem eLpNorm_le_of_sqn_le {X Y : ℝ → ℂ} (hX : AEStronglyMeasurable X volume)
    (hY : AEStronglyMeasurable Y volume) {c : ℝ≥0∞}
    (h : ∫⁻ x, ‖X x‖ₑ ^ 2 ≤ c ^ 2 * ∫⁻ x, ‖Y x‖ₑ ^ 2) :
    eLpNorm X 2 volume ≤ c * eLpNorm Y 2 volume := by
  rw [lintegral_sq_eq_eLpNorm_sq hX, lintegral_sq_eq_eLpNorm_sq hY, ← mul_pow] at h
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h

/-- `E_k f ∈ L²` for `f ∈ L²`. -/
theorem memLp_dyadicAvg {f : ℝ → ℂ} (hf : MemLp f 2 volume) (k : ℤ) :
    MemLp (dyadicAvg f k) 2 volume :=
  memLp_two_of_lintegral_sq_lt_top (measurable_dyadicAvg f k).aestronglyMeasurable
    (lt_of_le_of_lt (sqn_dyadicAvg_le hf k) (lintegral_sq_lt_top_of_memLp hf))

/-- `D_j f` is measurable. -/
theorem measurable_dyadicDiff (f : ℝ → ℂ) (j : ℤ) : Measurable (dyadicDiff f j) :=
  (measurable_dyadicAvg f _).sub (measurable_dyadicAvg f _)

/-- `D_j f ∈ L²` for `f ∈ L²`. -/
theorem memLp_dyadicDiff {f : ℝ → ℂ} (hf : MemLp f 2 volume) (j : ℤ) :
    MemLp (dyadicDiff f j) 2 volume :=
  (memLp_dyadicAvg hf _).sub (memLp_dyadicAvg hf _)

/-! ### The constants -/

/-- `‖ψ‖₁`. -/
def kappaPsi (ψ : 𝓢(ℝ, ℂ)) : ℝ := (∫⁻ t, ‖ψ t‖ₑ).toReal

/-- `∫ |ψ(s)| |s| ds`. -/
def muPsi (ψ : 𝓢(ℝ, ℂ)) : ℝ := (∫⁻ s, ‖ψ s‖ₑ * ENNReal.ofReal |s|).toReal

/-- `‖Θ‖₁` for the majorant `Θ(τ) = 4 C (1 + |τ|)^{-2}`. -/
def thetaPsi (C : ℝ) : ℝ := (∫⁻ τ, decayKernel C τ).toReal

/-- `∫ |ψ(s)| |s| ds < ∞` for a Schwartz function. -/
theorem lintegral_enorm_mul_abs_lt_top (ψ : 𝓢(ℝ, ℂ)) :
    ∫⁻ s, ‖ψ s‖ₑ * ENNReal.ofReal |s| < ∞ := by
  have h := (ψ.integrable_pow_mul volume 1).hasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq ?_) h
  refine lintegral_congr fun s => ?_
  rw [← ofReal_norm, ← ofReal_norm, norm_mul, norm_pow, norm_norm, pow_one, Real.norm_eq_abs,
    ← ENNReal.ofReal_mul (norm_nonneg _), mul_comm]
  simp

/-- `ofReal ‖ψ‖₁ = ∫⁻ |ψ|`. -/
theorem ofReal_kappaPsi (ψ : 𝓢(ℝ, ℂ)) :
    ENNReal.ofReal (kappaPsi ψ) = ∫⁻ t, ‖ψ t‖ₑ :=
  ENNReal.ofReal_toReal (lintegral_enorm_schwartz_lt_top ψ).ne

/-- `ofReal μ_ψ = ∫⁻ |ψ(s)| |s| ds`. -/
theorem ofReal_muPsi (ψ : 𝓢(ℝ, ℂ)) :
    ENNReal.ofReal (muPsi ψ) = ∫⁻ s, ‖ψ s‖ₑ * ENNReal.ofReal |s| :=
  ENNReal.ofReal_toReal (lintegral_enorm_mul_abs_lt_top ψ).ne

/-- `ofReal ‖Θ‖₁ = ∫⁻ Θ`. -/
theorem ofReal_thetaPsi (C : ℝ) : ENNReal.ofReal (thetaPsi C) = ∫⁻ τ, decayKernel C τ :=
  ENNReal.ofReal_toReal (lintegral_decayKernel_lt_top C).ne

/-- `‖ψ‖₁ ≥ 0`. -/
theorem kappaPsi_nonneg (ψ : 𝓢(ℝ, ℂ)) : 0 ≤ kappaPsi ψ := ENNReal.toReal_nonneg

/-- `∫ |ψ||s| ≥ 0`. -/
theorem muPsi_nonneg (ψ : 𝓢(ℝ, ℂ)) : 0 ≤ muPsi ψ := ENNReal.toReal_nonneg

/-- `‖Θ‖₁ ≥ 0`. -/
theorem thetaPsi_nonneg (C : ℝ) : 0 ≤ thetaPsi C := ENNReal.toReal_nonneg

/-! ### The per-scale bound -/

theorem dyadicAvg_dyadicDiff_of_le {f : ℝ → ℂ} (hf : MemLp f 2 volume) {j k : ℤ} (hjk : j ≤ k)
    (x : ℝ) : dyadicAvg (dyadicDiff f j) k x = 0 := by
  have h1 : dyadicDiff f j = dyadicAvg f (j - 1) - dyadicAvg f j := rfl
  rw [h1, dyadicAvg_sub (memLp_dyadicAvg hf _) (memLp_dyadicAvg hf _),
    dyadicAvg_dyadicAvg_of_ge (k := j - 1) (k' := k) (by omega) hf,
    dyadicAvg_dyadicAvg_of_ge (k := j) (k' := k) hjk hf, sub_self]

/-- **The per-scale bound**: `‖T_k D_j f‖₂ ≤ ρ(k - j) ‖D_j f‖₂` with
`ρ = sqRate (‖Θ‖₁) (√(8 ‖ψ‖₁ ∫|ψ||s|))`. -/
theorem eLpNorm_schwartzSqOp_dyadicDiff_le (ψ : 𝓢(ℝ, ℂ)) (hψ : ∫ t, ψ t = 1) {C : ℝ}
    (hC : ∀ u : ℝ, (1 + |u|) ^ 2 * ‖deriv ψ u‖ ≤ C) {f : ℝ → ℂ} (hf : MemLp f 2 volume) (j k : ℤ) :
    eLpNorm (schwartzSqOp ψ k (dyadicDiff f j)) 2 volume ≤
      ENNReal.ofReal (sqRate (thetaPsi C) (Real.sqrt (8 * kappaPsi ψ * muPsi ψ)) (k - j)) *
        eLpNorm (dyadicDiff f j) 2 volume := by
  have hDm := measurable_dyadicDiff f j
  have hDL := memLp_dyadicDiff hf j
  have hTm : Measurable (schwartzSqOp ψ k (dyadicDiff f j)) :=
    (measurable_schwartzAvg ψ k hDm).sub (measurable_dyadicAvg _ k)
  refine eLpNorm_le_of_sqn_le hTm.aestronglyMeasurable hDm.aestronglyMeasurable ?_
  rcases le_or_gt j k with hjk | hkj
  · have hop : ∀ x, schwartzSqOp ψ k (dyadicDiff f j) x = schwartzAvg ψ k (dyadicDiff f j) x :=
      fun x => by simp only [schwartzSqOp, dyadicAvg_dyadicDiff_of_le hf hjk, sub_zero]
    simp_rw [hop]
    refine (sqn_schwartzAvg_le_coarse ψ hC hjk hDm hDL
      (setIntegral_dyadicIco_dyadicDiff hf j)).trans (le_of_eq ?_)
    congr 2
    have hm : 0 ≤ k - j := by omega
    simp only [sqRate, hm, ite_true]
    rw [← ofReal_thetaPsi, ← ENNReal.ofReal_mul (by positivity), neg_sub, mul_comm]
  · have hop : ∀ x, schwartzSqOp ψ k (dyadicDiff f j) x =
        schwartzAvg ψ k (dyadicDiff f j) x - dyadicDiff f j x :=
      fun x => by simp only [schwartzSqOp, dyadicAvg_dyadicDiff_of_lt hkj]
    simp_rw [hop]
    refine (sqn_schwartzAvg_sub_le_fine ψ hψ hDm hDL (constOnDyadic_dyadicDiff f j)).trans
      (le_of_eq ?_)
    congr 1
    have hm : ¬ 0 ≤ k - j := by omega
    simp only [sqRate, hm, ite_false]
    set m := k - j with hmdef
    have hB : (Real.sqrt (8 * kappaPsi ψ * muPsi ψ)) ^ 2 = 8 * kappaPsi ψ * muPsi ψ :=
      Real.sq_sqrt (by have := kappaPsi_nonneg ψ; have := muPsi_nonneg ψ; positivity)
    have hκ := kappaPsi_nonneg ψ
    have hμ := muPsi_nonneg ψ
    rw [← ofReal_kappaPsi, ← ofReal_muPsi, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 8 * (2 : ℝ) ^ m by positivity),
      ← ENNReal.ofReal_mul hκ]
    congr 1
    rw [mul_pow, hB, sqrt_two_zpow_sq]
    ring

end PrimeCarleson.Proof.Oplus

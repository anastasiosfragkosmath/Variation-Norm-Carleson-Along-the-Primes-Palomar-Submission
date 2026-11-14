module

public import PrimeCarleson.Proof.Paper.P5.ErrorMult
public import PrimeCarleson.Proof.Paper.P5.KQProps

/-!
# The `K_Q`-replacement error multiplier

Source: main paper `p:red-var`, L1476–L1483:
"the difference has Fourier multiplier of total variation `O_A(Q^{-A})` for every `A < ∞`, by the
definition of `N(Q) = exp(Q^{1/D₀ - ε/10})` and the rapid decay of the Fourier transforms of the
kernels `ψ_k` at frequencies larger than `N(Q)^{-1}`".

* `KQSetup.KQerr Q = ∑_{k ≥ k₀} ψ̂(2^k ·) - K̂_Q`, the multiplier of `∑_{k ≥ k₀} ψ_k - K_Q`,
  equal to `(1 - φ̂(N(Q) ·)) ∑_{k ≥ k₀} ψ̂(2^k ·)` (`KQerr_eq`);
* `eVariationOn_error_le`: total variation `≤ K (2^{k₀} δ/(2N))^{-m}` for every `m ≥ 1`;
* `exists_error_decay`: `(2^{k₀} δ/(2N(Q)))^{-m} ≤ C Q^{-A}` for `m` large, because
  `2^{k₀} ≥ 2^{Q^{1/D₀}}` while `N(Q) = exp(Q^{1/D₀ - ε/10})`;
* `KQerr_eVariation_le`: **for every `A` there is `C_A` (depending on `A`, `ψ`, `φ`, `δ`, `D₀`,
  `ε`, not on `Q`) with `V(KQerr_Q) ≤ C_A Q^{-A}` for all `Q ≥ 1`**.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform SchwartzMap ContDiff Real

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper.P5

open PrimeCarleson PrimeCarleson.Proof.Paper PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

variable (ψ : PsiData)

/-- **Total variation of the error multiplier** `(1 - φ̂(N ·)) ∑_{k ≥ k₀} ψ̂(2^k ·)`. -/
theorem eVariationOn_error_le (F : 𝓢(ℝ, ℂ)) {δ : ℝ} (hδ : 0 < δ)
    (hF : ∀ ξ : ℝ, |ξ| ≤ δ / 2 → F ξ = 1) {m : ℕ} (hm : 1 ≤ m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℝ), 0 < N → ∀ k₀ : ℕ,
      eVariationOn (fun β => (1 - F (N * β)) * psiTail ψ k₀ β) Set.univ ≤
        ENNReal.ofReal (K * (((2 : ℝ) ^ k₀ * (δ / (2 * N)))⁻¹) ^ m) := by
  obtain ⟨A, hA0, hA⟩ := exists_norm_le_schwartz F
  obtain ⟨Cm, hCm0, hCm⟩ := exists_Spart_decay ψ hm
  have hT1 : (0 : ℝ) ≤ ∫ x, ‖deriv (F : ℝ → ℂ) x‖ := integral_nonneg fun _ => norm_nonneg _
  refine ⟨Cm * (∫ x, ‖deriv (F : ℝ → ℂ) x‖) + 2 * π * (1 + A) * 2 * Mom ψ m,
    by have := Mom_nonneg ψ m; positivity, fun N hN k₀ => ?_⟩
  refine eVariationOn_le_of_forall (F := fun n β => (1 - F (N * β)) * Spart ψ k₀ (k₀ + n) β)
    (fun β => (tendsto_Spart_psiTail ψ k₀ β).const_mul _) fun n => ?_
  exact eVariationOn_error_partial_le ψ F hδ hF hm hA hCm hN k₀ n

/-- `y^θ ≤ c y + c₁` for `y ≥ 1`, `0 ≤ θ < 1`, `c > 0`. -/
theorem exists_rpow_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) {c : ℝ} (hc : 0 < c) :
    ∃ c₁ : ℝ, 0 ≤ c₁ ∧ ∀ y : ℝ, 1 ≤ y → y ^ θ ≤ c * y + c₁ := by
  have hev := (tendsto_rpow_neg_atTop (show 0 < 1 - θ by linarith)).eventually
    (gt_mem_nhds hc)
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.1 (hev.and (eventually_ge_atTop (1 : ℝ)))
  set Y : ℝ := max Y₁ 1 with hY
  have hY1 : 1 ≤ Y := le_max_right _ _
  refine ⟨Y ^ θ, Real.rpow_nonneg (by linarith) _, fun y hy => ?_⟩
  by_cases hyY : Y ≤ y
  · have hy1 := hY₁ y ((le_max_left _ _).trans hyY)
    have hy0 : 0 < y := by linarith
    have h2 : y ^ (-(1 - θ)) = y ^ θ / y := by
      rw [← Real.rpow_sub_one hy0.ne']
      congr 1
      ring
    have h3 : y ^ θ = y ^ (-(1 - θ)) * y := by
      rw [h2]
      field_simp
    have h4 : 0 ≤ Y ^ θ := Real.rpow_nonneg (by linarith) _
    nlinarith [hy1.1]
  · push Not at hyY
    have h5 : y ^ θ ≤ Y ^ θ := Real.rpow_le_rpow (by linarith) hyY.le h0
    nlinarith

/-- `exp(-t y) ≤ y^{-t}` for `t ≥ 0`, `y ≥ 1`. -/
theorem exp_neg_mul_le_rpow_neg {t y : ℝ} (ht : 0 ≤ t) (hy : 1 ≤ y) :
    Real.exp (-(t * y)) ≤ y ^ (-t) := by
  have hy0 : 0 < y := by linarith
  rw [Real.rpow_def_of_pos hy0, Real.exp_le_exp]
  have : Real.log y ≤ y := (Real.log_le_sub_one_of_pos hy0).trans (by linarith)
  nlinarith

/-- The arithmetic of `N(Q) = exp(Q^{1/D₀ - ε/10})` against `2^{⌈Q^{1/D₀}⌉}`: for every `A` there
are `m ≥ 1` and `C` with `(2^{k₀} δ/(2N(Q)))^{-m} ≤ C Q^{-A}` for every `Q ≥ 1`. -/
theorem exists_error_decay (P : KQParams) {δ : ℝ} (hδ : 0 < δ) (A : ℝ) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℕ, 1 ≤ Q →
      (((2 : ℝ) ^ (P.kmin Q) * (δ / (2 * P.NQ Q)))⁻¹) ^ m ≤ C * (Q : ℝ) ^ (-A) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hD := P.D₀_pos
  set θ : ℝ := P.gamma * P.D₀ with hθ
  have hθ1 : θ < 1 := by
    have : P.gamma < 1 / P.D₀ := P.gamma_lt_inv
    rw [hθ]
    calc P.gamma * P.D₀ < 1 / P.D₀ * P.D₀ := mul_lt_mul_of_pos_right this hD
      _ = 1 := by field_simp
  have hθ0 : 0 ≤ θ := (mul_pos P.gamma_pos hD).le
  obtain ⟨c₁, hc₁, hcc⟩ := exists_rpow_le hθ0 hθ1 (show 0 < Real.log 2 / 2 by positivity)
  set Ap : ℝ := max A 0 with hAp
  set m : ℕ := max 1 ⌈2 * Ap * P.D₀ / Real.log 2⌉₊ with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hmreal : Ap * P.D₀ ≤ m * (Real.log 2 / 2) := by
    have h1 : 2 * Ap * P.D₀ / Real.log 2 ≤ (m : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
    rw [div_le_iff₀ hl2] at h1
    nlinarith
  refine ⟨m, hm1, ((2 / δ) * Real.exp c₁) ^ m, by positivity, fun Q hQ => ?_⟩
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  set y : ℝ := (Q : ℝ) ^ (1 / P.D₀) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hQ1 (by positivity)
  have hqγ : (Q : ℝ) ^ P.gamma = y ^ θ := by
    rw [hy, ← Real.rpow_mul hQ0.le]
    congr 1
    rw [hθ]
    field_simp
  have hN : P.NQ Q = Real.exp (y ^ θ) := by
    unfold KQParams.NQ
    rw [hqγ]
  have h2k : Real.exp (y * Real.log 2) ≤ (2 : ℝ) ^ (P.kmin Q) := by
    have : (2 : ℝ) ^ y ≤ (2 : ℝ) ^ ((P.kmin Q : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le one_le_two (P.rpow_le_kmin Q)
    rw [Real.rpow_natCast, Real.rpow_def_of_pos two_pos, mul_comm] at this
    exact this
  have hN0 := P.NQ_pos Q
  have hRinv : ((2 : ℝ) ^ (P.kmin Q) * (δ / (2 * P.NQ Q)))⁻¹ ≤
      (2 / δ) * Real.exp c₁ * Real.exp (-(Real.log 2 / 2 * y)) := by
    have hp0 : (0 : ℝ) < (2 : ℝ) ^ (P.kmin Q) := by positivity
    have e1 : ((2 : ℝ) ^ (P.kmin Q) * (δ / (2 * P.NQ Q)))⁻¹ =
        (2 / δ) * (P.NQ Q / (2 : ℝ) ^ (P.kmin Q)) := by
      field_simp
    rw [e1, hN]
    have e2 : Real.exp (y ^ θ) / (2 : ℝ) ^ (P.kmin Q) ≤
        Real.exp (y ^ θ) / Real.exp (y * Real.log 2) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) h2k
    have e3 : Real.exp (y ^ θ) / Real.exp (y * Real.log 2) ≤
        Real.exp c₁ * Real.exp (-(Real.log 2 / 2 * y)) := by
      rw [← Real.exp_sub, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have := hcc y hy1
      nlinarith
    calc 2 / δ * (Real.exp (y ^ θ) / (2 : ℝ) ^ (P.kmin Q))
        ≤ 2 / δ * (Real.exp c₁ * Real.exp (-(Real.log 2 / 2 * y))) :=
          mul_le_mul_of_nonneg_left (e2.trans e3) (by positivity)
      _ = _ := by ring
  have hpow := pow_le_pow_left₀ (by positivity) hRinv m
  refine hpow.trans ?_
  rw [mul_pow, ← Real.exp_nat_mul]
  have h5 : Real.exp (m * (-(Real.log 2 / 2 * y))) ≤ (Q : ℝ) ^ (-A) := by
    have h6 : Real.exp (m * (-(Real.log 2 / 2 * y))) ≤ Real.exp (-(Ap * P.D₀ * y)) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith [hmreal, hy1]
    refine h6.trans ((exp_neg_mul_le_rpow_neg (by positivity) hy1).trans ?_)
    rw [hy, ← Real.rpow_mul hQ0.le]
    refine Real.rpow_le_rpow_of_exponent_le hQ1 ?_
    have : 1 / P.D₀ * -(Ap * P.D₀) = -Ap := by field_simp
    rw [this]
    have : A ≤ Ap := le_max_left _ _
    linarith
  calc ((2 / δ * Real.exp c₁) ^ m) * Real.exp (m * (-(Real.log 2 / 2 * y)))
      ≤ ((2 / δ * Real.exp c₁) ^ m) * (Q : ℝ) ^ (-A) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = _ := rfl

end PrimeCarleson.Proof.Paper.P5

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Paper.P5

namespace KQSetup

variable (S : KQSetup)

/-- The Fourier multiplier `∑_{k ≥ k₀} ψ̂(2^k ·) - K̂_Q` of `∑_{k ≥ k₀} ψ_k - K_Q` (Source: main
paper `p:red-var`, L1476–L1483). -/
def KQerr (Q : ℕ) (β : ℝ) : ℂ := psiTail S.ψ (S.P.kmin Q) β - S.KQhat Q β

/-- `KQerr = (1 - φ̂(N(Q) ·)) ∑_{k ≥ k₀} ψ̂(2^k ·)`. -/
theorem KQerr_eq (Q : ℕ) (β : ℝ) :
    S.KQerr Q β = (1 - S.φ.hat (S.P.NQ Q * β)) * psiTail S.ψ (S.P.kmin Q) β := by
  unfold KQerr KQhat
  ring

/-- **The error multiplier of the `K_Q`-replacement** (Source: main paper `p:red-var`, L1476–L1483):
for every `A < ∞` there is `C_A` such that for every `Q ≥ 1` (in particular every dyadic `Q`) the
Fourier multiplier of `∑_{Q^{1/D₀} ≤ k} ψ_k - K_Q` has total variation `≤ C_A Q^{-A}`. The constant
depends on `A` and the fixed data (`ψ`, `φ`, `δ`, `D₀`, `ε`), not on `Q`. -/
theorem KQerr_eVariation_le (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℕ, 1 ≤ Q →
      eVariationOn (S.KQerr Q) Set.univ ≤ ENNReal.ofReal (C * (Q : ℝ) ^ (-A)) := by
  obtain ⟨m, hm1, C₁, hC₁0, hC₁⟩ := exists_error_decay S.P S.δ_pos A
  obtain ⟨K, hK0, hK⟩ := eVariationOn_error_le S.ψ (𝓕 S.φ.toSchwartz) S.δ_pos
    (fun ξ hξ => S.φ.fourier_eq_one ξ hξ) hm1
  refine ⟨K * C₁, by positivity, fun Q hQ => ?_⟩
  have hfun : S.KQerr Q = fun β => (1 - (𝓕 S.φ.toSchwartz) (S.P.NQ Q * β)) *
      psiTail S.ψ (S.P.kmin Q) β := by
    funext β
    exact S.KQerr_eq Q β
  rw [hfun]
  refine (hK (S.P.NQ Q) (S.P.NQ_pos Q) (S.P.kmin Q)).trans (ENNReal.ofReal_le_ofReal ?_)
  calc K * (((2 : ℝ) ^ (S.P.kmin Q) * (S.δ / (2 * S.P.NQ Q)))⁻¹) ^ m
      ≤ K * (C₁ * (Q : ℝ) ^ (-A)) := mul_le_mul_of_nonneg_left (hC₁ Q hQ) hK0
    _ = K * C₁ * (Q : ℝ) ^ (-A) := by ring

end KQSetup

end PrimeCarleson.Proof.Paper

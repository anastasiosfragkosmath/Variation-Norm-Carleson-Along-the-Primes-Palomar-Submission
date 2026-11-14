module

public import PrimeCarleson.Proof.Paper.P6a.KQL2
public import PrimeCarleson.Proof.Paper.P6a.KQCrude
public import PrimeCarleson.Proof.Paper.P6a.Interp
public import PrimeCarleson.Proof.Paper.P6a.Series

/-!
# The replacement of `∑_{k ≥ Q^{1/D₀}} ψ_k` by `K_Q`

Source: main paper `p:red-var`, L1504–L1507: `‖V^r(∑_n f(x-n) w_Q(n) ∑_{k ≥ Q^{1/D₀}} ψ_k(n) e(λ n)
: λ)‖_{ℓ^p} ≤ ‖V^{Q,r} f‖_{ℓ^p} + O_{p,r}(Q^{-100} ‖f‖_{ℓ^p})`, by the triangle inequality for `V^r`
and the Marcinkiewicz interpolation of the `ℓ²` bound for the error (L1483–L1502, `A = A(p, r)`
large) and its crude `ℓ^s` bound (L1504), with the auxiliary exponent `s` of L1324.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- The pointwise triangle inequality of the replacement:
`V^r(w_Q ∑_{k ≥ k₀} ψ_k) ≤ V^{Q,r} f + V^r(w_Q E_Q)`. -/
theorem varOp_psiTail_le (S : KQSetup) {r : ℝ} (hr : 1 ≤ r) (Q : ℕ) (f : ℤ →₀ ℂ) (x : ℤ) :
    varOp r (fun n => wQ Q n * psiTailZ S.ψ (S.P.kmin Q) n) (⇑f) x ≤
      S.VQr r Q (⇑f) x + varOp r (fun n => wQ Q n * errW S Q n) (⇑f) x := by
  rw [VQr_eq_varOp]
  have : (fun n => wQ Q n * psiTailZ S.ψ (S.P.kmin Q) n) =
      (fun n => wQ Q n * S.KQz Q n) + (fun n => wQ Q n * errW S Q n) := by
    funext n
    simp only [Pi.add_apply, errW]
    ring
  rw [this]
  exact varOp_add_weight_le hr _ _ f x

/-- **The `K_Q`-replacement** (Source: main paper `p:red-var`, L1504–L1507): for `r > 2`, `p > r'`
there is `C` such that for every `Q ≥ 1` and finitely supported `f`, `‖V^r(∑_n f(x-n) w_Q(n) ∑_{k ≥
Q^{1/D₀}} ψ_k(n) e(λ n) : λ)‖_{ℓ^p} ≤ ‖V^{Q,r} f‖_{ℓ^p} + C Q^{-100} ‖f‖_{ℓ^p}`. -/
theorem KQ_replacement (S : KQSetup) {r p : ℝ} (hr : 2 < r) (hp : r / (r - 1) < p)
    (hV : VarCarZ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ f : ℤ →₀ ℂ,
      eLpNorm (varOp r (fun n => wQ Q n * psiTailZ S.ψ (S.P.kmin Q) n) (⇑f))
          (ENNReal.ofReal p) Measure.count ≤
        eLpNorm (S.VQr r Q (⇑f)) (ENNReal.ofReal p) Measure.count +
          ENNReal.ofReal (C * (Q : ℝ) ^ (-(100 : ℝ))) *
            eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨s, ϑ, Cint, hs, hϑ0, hϑ1, hCint0, hint⟩ := varOp_interp hr hp
  have hp1 : 1 ≤ p := by
    have : 1 ≤ r / (r - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
    linarith
  set A : ℝ := 101 / ϑ with hA
  obtain ⟨C₀, hC₀, h₀⟩ := KQ_error_l2 S hr hV A
  obtain ⟨C₁, hC₁, h₁⟩ := KQ_error_crude S hr hs
  set C₀' : ℝ := max C₀ 1 with hC₀'
  set C₁' : ℝ := max C₁ 1 with hC₁'
  have hC₀'0 : 0 < C₀' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hC₁'0 : 0 < C₁' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set K : ℝ := Cint * C₀' ^ ϑ * C₁' ^ (1 - ϑ) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K, hK0, fun Q hQ f => ?_⟩
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  -- the interpolated bound for the error
  have herr : eLpNorm (varOp r (fun n => wQ Q n * errW S Q n) (⇑f)) (ENNReal.ofReal p)
      Measure.count ≤ ENNReal.ofReal (K * (Q : ℝ) ^ (-(100 : ℝ))) *
        eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
    have hX₀ : 0 < C₀' * (Q : ℝ) ^ (-A) := by positivity
    have hX₁ : 0 < C₁' * (Q : ℝ) := by positivity
    have h := hint (fun n => wQ Q n * errW S Q n) _ _ hX₀ hX₁
      (fun g => (h₀ Q hQ g).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) le_rfl))
      (fun g => (h₁ Q hQ g).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) le_rfl)) f
    refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    rw [Real.mul_rpow hC₀'0.le (by positivity), Real.mul_rpow hC₁'0.le hQ0.le,
      ← Real.rpow_mul hQ0.le]
    have e1 : (Q : ℝ) ^ (-A * ϑ) * (Q : ℝ) ^ (1 - ϑ) = (Q : ℝ) ^ (-101 - ϑ + 1) := by
      rw [← Real.rpow_add hQ0]; congr 1
      rw [hA]; field_simp; ring
    have hle : (Q : ℝ) ^ (-101 - ϑ + 1) ≤ (Q : ℝ) ^ (-(100 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
    calc Cint * (C₀' ^ ϑ * (Q : ℝ) ^ (-A * ϑ)) * (C₁' ^ (1 - ϑ) * (Q : ℝ) ^ (1 - ϑ))
        = K * ((Q : ℝ) ^ (-A * ϑ) * (Q : ℝ) ^ (1 - ϑ)) := by rw [hK]; ring
      _ = K * (Q : ℝ) ^ (-101 - ϑ + 1) := by rw [e1]
      _ ≤ K * (Q : ℝ) ^ (-(100 : ℝ)) := mul_le_mul_of_nonneg_left hle hK0
  have hmono : eLpNorm (varOp r (fun n => wQ Q n * psiTailZ S.ψ (S.P.kmin Q) n) (⇑f))
      (ENNReal.ofReal p) Measure.count ≤
      eLpNorm (fun x => S.VQr r Q (⇑f) x + varOp r (fun n => wQ Q n * errW S Q n) (⇑f) x)
        (ENNReal.ofReal p) Measure.count :=
    eLpNorm_count_mono_enn (fun x => varOp_psiTail_le S (by linarith) Q f x) _
  exact hmono.trans ((eLpNorm_count_add_le _ _ hp1).trans (add_le_add le_rfl herr))

end PrimeCarleson.Proof.Paper

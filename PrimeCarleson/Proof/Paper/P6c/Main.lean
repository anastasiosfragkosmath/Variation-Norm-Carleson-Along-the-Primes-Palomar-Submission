module

public import PrimeCarleson.Proof.Paper.P6c.Split
public import PrimeCarleson.Proof.Paper.P6c.Residual
public import PrimeCarleson.Proof.Paper.P6c.HighQ
public import PrimeCarleson.Proof.Paper.P6c.KQ
public import PrimeCarleson.Proof.Paper.P6a.Hyps

/-!
# The maximal endpoint of `p:red-var`: `‖C_P f‖_{ℓ^p} ≲ ‖f‖_{ℓ^p} + ∑_Q ‖C^Q f‖_{ℓ^p}`

Source: main paper `s:red`, L1521–L1528: the maximal counterpart of `combine_pieces_param`,
`dyadic_Q_sum` and `red_var_param` of `Main/RedVar.lean` and `P6a/Main.lean`.

* `maximal_dyadic_Q_sum`: for `1 < p < ∞` there is `D₁ = D₁(p)` such that for every setup `S`
  with `D₀ ≥ D₁`, `‖C_P f‖_{ℓ^p} ≤ C ‖f‖_{ℓ^p} + ∑_{Q = 2^j} ‖C^Q f‖_{ℓ^p}`, from
  `triangle_split_sup`, `main_term_split_sup`, `low_Q_reindex_sup` (`Split.lean`),
  `residual_sum_sup`, `highQ_sum_sup`, `leftover_pairs_sup` and `KQ_replacement_sup`;
* `maximal_endpoint_reduction`: if `‖C^Q f‖_{ℓ^p} ≲ Q^{-c} ‖f‖_{ℓ^p}` for all dyadic `Q`
  (`c > 0`), then `‖C_P f‖_{ℓ^p} ≲_p ‖f‖_{ℓ^p}` (the conclusion is the statement of `t:carmax`
  at this `p`).

The inputs proved elsewhere enter through `hO : OplusVariationBound` and
`hF : FplusProp31` only (`LocalU3VarRed` and `VarCarZ` are not needed: the maximal `U³`-estimate
and the maximal Euclidean estimate are used directly).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- **The maximal sum over dyadic `Q`**: for `1 < p < ∞` there is `D₁ = D₁(p)` such that for every
setup `S` of `K_Q` with `D₀ ≥ D₁` there is `C` with
`‖C_P f‖_{ℓ^p} ≤ C ‖f‖_{ℓ^p} + ∑_{Q = 2^j} ‖C^Q f‖_{ℓ^p}` for every finitely supported `f`. -/
theorem maximal_dyadic_Q_sum (hO : OplusVariationBound) (hF : FplusProp31) {p : ℝ}
    (hp : 1 < p) :
    ∃ D₁ : ℝ, ∀ S : KQSetup, D₁ ≤ S.P.D₀ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℤ →₀ ℂ,
        eLpNorm (carlesonMax (ArithmeticFunction.vonMangoldt : ℕ → ℝ) f) (ENNReal.ofReal p)
            Measure.count ≤
          ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count +
            ∑' j : ℕ, eLpNorm (S.CQ (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count := by
  have hp1 : 1 ≤ p := hp.le
  obtain ⟨D₁, hD₁⟩ := highQ_sum_sup hp
  refine ⟨D₁, fun S hD => ?_⟩
  have hD0 : 0 < S.P.D₀ := S.P.D₀_pos
  obtain ⟨C_res, hCres0, hres⟩ := residual_sum_sup S.ψ hp hF
  obtain ⟨C_high, hChigh0, hhigh⟩ := hD₁ S.ψ S.P.D₀ hD
  obtain ⟨C_left, hCleft0, hleft⟩ := leftover_pairs_sup S.ψ hp1 S.P.D₀
  obtain ⟨C_kq, hCkq0, hkq⟩ := KQ_replacement_sup hO S hp
  set γ : ℝ := C_kq * (1 - (2 : ℝ) ^ (-(100 : ℝ)))⁻¹ with hγ
  have hq1 : (2 : ℝ) ^ (-(100 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hγ0 : 0 ≤ γ := mul_nonneg hCkq0 (inv_nonneg.2 (by linarith))
  refine ⟨C_res + C_high + C_left + γ, by positivity, fun f => ?_⟩
  set ψ := S.ψ with hψ
  set D₀ := S.P.D₀ with hD₀
  -- the pointwise chain
  have hpt : ∀ x : ℤ, carlesonMax (ArithmeticFunction.vonMangoldt : ℕ → ℝ) f x ≤
      ((∑' j : ℕ, supOp (fun n => wQ (2 ^ j) n * psiTailZ ψ (kminD D₀ (2 ^ j)) n) (⇑f) x +
        ∑ q ∈ (leftoverSet_finite D₀).toFinset, supOp (pairW ψ q.1 q.2) (⇑f) x) +
        ∑' k : ℕ, ∑ j ∈ highJ D₀ (k + 1), supOp (pairW ψ (k + 1) j) (⇑f) x) +
        ∑' k : ℕ, supOp (fun n => resWeight (k + 1) n * psiKz ψ (k + 1) n) (⇑f) x := by
    intro x
    rw [carlesonMax_vonMangoldt_eq_supOp]
    exact maximal_pointwise_chain ψ hD0 f x
  have hnorm : eLpNorm (carlesonMax (ArithmeticFunction.vonMangoldt : ℕ → ℝ) f)
      (ENNReal.ofReal p) Measure.count ≤
      eLpNorm (fun x => ((∑' j : ℕ, supOp (fun n => wQ (2 ^ j) n *
          psiTailZ ψ (kminD D₀ (2 ^ j)) n) (⇑f) x +
        ∑ q ∈ (leftoverSet_finite D₀).toFinset, supOp (pairW ψ q.1 q.2) (⇑f) x) +
        ∑' k : ℕ, ∑ j ∈ highJ D₀ (k + 1), supOp (pairW ψ (k + 1) j) (⇑f) x) +
        ∑' k : ℕ, supOp (fun n => resWeight (k + 1) n * psiKz ψ (k + 1) n) (⇑f) x)
        (ENNReal.ofReal p) Measure.count := eLpNorm_count_mono_enn hpt _
  refine hnorm.trans ?_
  refine (eLpNorm_count_add_le _ _ hp1).trans ?_
  refine (add_le_add (eLpNorm_count_add_le _ _ hp1) le_rfl).trans ?_
  refine (add_le_add (add_le_add (eLpNorm_count_add_le _ _ hp1) le_rfl) le_rfl).trans ?_
  -- the four pieces
  have hL₁ : eLpNorm (fun x => ∑' j : ℕ, supOp (fun n => wQ (2 ^ j) n *
        psiTailZ ψ (kminD D₀ (2 ^ j)) n) (⇑f) x) (ENNReal.ofReal p) Measure.count ≤
      ∑' j : ℕ, eLpNorm (S.CQ (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count +
        ENNReal.ofReal γ * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
    refine (eLpNorm_count_tsum_le _ hp1).trans ?_
    have h1 : ∀ j : ℕ, eLpNorm (supOp (fun n => wQ (2 ^ j) n *
          psiTailZ ψ (kminD D₀ (2 ^ j)) n) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
        eLpNorm (S.CQ (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count +
          ENNReal.ofReal (C_kq * ((2 : ℝ) ^ j) ^ (-(100 : ℝ))) *
            eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
      intro j
      have := hkq (2 ^ j) Nat.one_le_two_pow f
      rw [show ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j by push_cast; rfl] at this
      exact this
    refine (ENNReal.tsum_le_tsum h1).trans ?_
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    refine add_le_add le_rfl (mul_le_mul' ?_ le_rfl)
    exact tsum_ofReal_dyadic_le C_kq 100 hCkq0 (by norm_num)
  have hL₂ : eLpNorm (fun x => ∑ q ∈ (leftoverSet_finite D₀).toFinset,
        supOp (pairW ψ q.1 q.2) (⇑f) x) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal C_left * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count :=
    (eLpNorm_count_finset_sum_le _ _ hp1).trans (hleft f)
  have hH : eLpNorm (fun x => ∑' k : ℕ, ∑ j ∈ highJ D₀ (k + 1),
        supOp (pairW ψ (k + 1) j) (⇑f) x) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal C_high * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
    refine (eLpNorm_count_tsum_le _ hp1).trans ?_
    refine le_trans (ENNReal.tsum_le_tsum fun k => ?_) (hhigh f)
    exact (eLpNorm_count_finset_sum_le _ _ hp1)
  have hR : eLpNorm (fun x => ∑' k : ℕ, supOp (fun n => resWeight (k + 1) n *
        psiKz ψ (k + 1) n) (⇑f) x) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal C_res * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count :=
    (eLpNorm_count_tsum_le _ hp1).trans (hres f)
  -- assemble
  set X := eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count with hX
  set T := ∑' j : ℕ, eLpNorm (S.CQ (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count with hT
  calc _ ≤ ((T + ENNReal.ofReal γ * X) + ENNReal.ofReal C_left * X) +
          ENNReal.ofReal C_high * X + ENNReal.ofReal C_res * X := by
        gcongr
    _ = ENNReal.ofReal (C_res + C_high + C_left + γ) * X + T := by
        rw [ENNReal.ofReal_add (by positivity) hγ0, ENNReal.ofReal_add (by positivity)
          hCleft0, ENNReal.ofReal_add hCres0 hChigh0]
        ring

/-- **The maximal endpoint reduction** (Source: main paper `s:red`, L1521–L1528): for `1 < p < ∞`
there is `D₁ = D₁(p)` such that for every setup `S` of `K_Q` with `D₀ ≥ D₁`, if
`‖C^Q f‖_{ℓ^p} ≲ Q^{-c} ‖f‖_{ℓ^p}` for all dyadic `Q = 2^j` with one exponent `c > 0` and one
constant (in this order of quantifiers), then `‖C_P f‖_{ℓ^p} ≲_p ‖f‖_{ℓ^p}` for all finitely
supported `f`. -/
theorem maximal_endpoint_reduction (hO : OplusVariationBound) (hF : FplusProp31) {p : ℝ}
    (hp : 1 < p) :
    ∃ D₁ : ℝ, ∀ S : KQSetup, D₁ ≤ S.P.D₀ →
      (∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ (j : ℕ) (f : ℤ →₀ ℂ),
        eLpNorm (S.CQ (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
          ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-c)) *
            eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count) →
      ∃ K : ℝ, 0 < K ∧ ∀ f : ℤ →₀ ℂ,
        eLpNorm (carlesonMax (ArithmeticFunction.vonMangoldt : ℕ → ℝ) f) (ENNReal.ofReal p)
            Measure.count ≤
          ENNReal.ofReal K * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨D₁, hD₁⟩ := maximal_dyadic_Q_sum hO hF hp
  refine ⟨D₁, fun S hD ⟨c, hc, C, hC⟩ => ?_⟩
  obtain ⟨C₁, hC₁0, hC₁⟩ := hD₁ S hD
  set G : ℝ := max C 0 * (1 - (2 : ℝ) ^ (-c))⁻¹ with hG
  have hq1 : (2 : ℝ) ^ (-c) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hG0 : 0 ≤ G := mul_nonneg (le_max_right _ _) (inv_nonneg.2 (by linarith))
  refine ⟨C₁ + G + 1, by positivity, fun f => ?_⟩
  refine (hC₁ f).trans ?_
  have h1 : ∀ j : ℕ, eLpNorm (S.CQ (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal (max C 0 * ((2 : ℝ) ^ j) ^ (-c)) *
        eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := fun j =>
    (hC j f).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) le_rfl)
  have h2 : ∑' j : ℕ, eLpNorm (S.CQ (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal G * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
    refine (ENNReal.tsum_le_tsum h1).trans ?_
    rw [ENNReal.tsum_mul_right]
    exact mul_le_mul' (tsum_ofReal_dyadic_le _ _ (le_max_right _ _) hc) le_rfl
  calc ENNReal.ofReal C₁ * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count +
        ∑' j : ℕ, eLpNorm (S.CQ (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count
      ≤ ENNReal.ofReal C₁ * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count +
        ENNReal.ofReal G * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := add_le_add le_rfl h2
    _ = ENNReal.ofReal (C₁ + G) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
        rw [ENNReal.ofReal_add hC₁0 hG0, add_mul]
    _ ≤ ENNReal.ofReal (C₁ + G + 1) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl

end PrimeCarleson.Proof.Paper

module

public import PrimeCarleson.Proof.Paper.Main.Interp
public import PrimeCarleson.Proof.Paper.P6a.Main

/-!
# `p:red-var` with the high-denominator threshold as a parameter

Source: main paper `p:red-var`, L1227–L1242 (statement) and L1508–L1516 (conclusion of the proof),
as input of the bound for a fixed pair `(r, p)` and of the
choice of the range of `p` in `t:main` (`Main/Setup.lean`, `Main/Interp.lean`).

The constant `D₁ = D₁(p, r)` of the high-denominator sum has to be controlled in `p` and `r`, so
this file states both the combination of the pieces and the proposition with the bound of the
high-denominator sum as a hypothesis `HighQSum r p D₁`; `highQSum_of_param` gives
`HighQSum r p (32 / (ϑ (1 - 2/r)))` from the interpolation data of `Main/Interp.lean`.

* `HighQSum r p D₁`: the bound of the high-denominator sum of `p:red-var` for every `D₀ ≥ D₁`;
* `combine_pieces_param`: the combination of the pieces of `p:red-var` for every setup with
  `D₀ ≥ D₁`;
* `red_var_param`: Proposition `p:red-var` for every setup with `D₀ ≥ D₁`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- **The high-denominator sum of `p:red-var`** (Source: main paper `p:red-var`, L1456–L1458) for
every `D₀ ≥ D₁`: for every even-weight setup the
sum over `k ≥ 1` and the dyadic `Q = 2^j` with `k^{D₀} < Q ≤ M(k)` of
`‖V^r(∑_n f(x-n) w_Q(n) ψ_k(n) e(λ n) : λ)‖_{ℓ^p}` is `≲ ‖f‖_{ℓ^p}`. -/
def HighQSum (r p D₁ : ℝ) : Prop :=
  ∀ ψ : PsiData, LocalU3VarRed ψ r → ∀ D₀ : ℝ, D₁ ≤ D₀ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ f : ℤ →₀ ℂ,
      ∑' k : ℕ, ∑ j ∈ highJ D₀ (k + 1),
          eLpNorm (varOp r (pairW ψ (k + 1) j) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count

/-- `highQ_sum_param` in the form `HighQSum`. -/
theorem highQSum_of_param {r p s ϑ : ℝ} (hr : 2 < r) (hs : r / (r - 1) ≤ s) (hϑ0 : 0 < ϑ)
    (hϑ1 : ϑ ≤ 1) (hint : VarOpInterp r p s ϑ) : HighQSum r p (32 / (ϑ * (1 - 2 / r))) :=
  fun ψ hLoc D₀ hD₀ => highQ_sum_param hr hs hϑ0 hϑ1 hint ψ hLoc D₀ hD₀

/-- **Combination of the pieces of `p:red-var`** (L1508–L1516): for `r > 2`, `p > r'` and
`HighQSum r p D₁`, every setup `S` with `D₀ ≥ D₁` (and `e:local-U3-var-red` for its `ψ`) has `C`
with `‖V^r_P f‖_{ℓ^p} ≤ C ‖f‖_{ℓ^p} + ∑_{Q = 2^j} ‖V^{Q,r} f‖_{ℓ^p}`. -/
theorem combine_pieces_param {r p D₁ : ℝ} (hr : 2 < r) (hp : r / (r - 1) < p) (hF : FplusProp31)
    (hV : VarCarZ r) (hH : HighQSum r p D₁) :
    ∀ S : KQSetup, LocalU3VarRed S.ψ r → D₁ ≤ S.P.D₀ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℤ →₀ ℂ,
        eLpNorm (primeVariation r f) (ENNReal.ofReal p) Measure.count ≤
          ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count +
            ∑' j : ℕ, eLpNorm (S.VQr r (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count := by
  have hr1 : 0 < r - 1 := by linarith
  have hr'1 : 1 ≤ r / (r - 1) := by rw [le_div_iff₀ hr1]; linarith
  have hp1 : 1 ≤ p := hr'1.trans hp.le
  intro S hLoc hD
  have hD0 : 0 < S.P.D₀ := S.P.D₀_pos
  obtain ⟨C_res, hCres0, hres⟩ := residual_sum S.ψ hr hp hLoc hF
  obtain ⟨C_high, hChigh0, hhigh⟩ := hH S.ψ hLoc S.P.D₀ hD
  obtain ⟨-, C_left, hCleft0, hleft⟩ := leftover_pairs S.ψ hr hp.le S.P.D₀
  obtain ⟨C_kq, hCkq0, hkq⟩ := KQ_replacement S hr hp hV
  set γ : ℝ := C_kq * (1 - (2 : ℝ) ^ (-(100 : ℝ)))⁻¹ with hγ
  have hq1 : (2 : ℝ) ^ (-(100 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hγ0 : 0 ≤ γ := mul_nonneg hCkq0 (inv_nonneg.2 (by linarith))
  refine ⟨C_res + C_high + C_left + γ, by positivity, fun f => ?_⟩
  set ψ := S.ψ with hψ
  set D₀ := S.P.D₀ with hD₀
  -- the pointwise chain
  have hpt : ∀ x : ℤ, primeVariation r f x ≤
      ((∑' j : ℕ, varOp r (fun n => wQ (2 ^ j) n * psiTailZ ψ (kminD D₀ (2 ^ j)) n) (⇑f) x +
        ∑ q ∈ (leftoverSet_finite D₀).toFinset, varOp r (pairW ψ q.1 q.2) (⇑f) x) +
        ∑' k : ℕ, ∑ j ∈ highJ D₀ (k + 1), varOp r (pairW ψ (k + 1) j) (⇑f) x) +
        ∑' k : ℕ, varOp r (fun n => resWeight (k + 1) n * psiKz ψ (k + 1) n) (⇑f) x := by
    intro x
    refine (triangle_split ψ (by linarith) f x).trans (add_le_add ?_ le_rfl)
    refine (main_term_split ψ (by linarith) D₀ f x).trans (add_le_add ?_ le_rfl)
    exact low_Q_reindex ψ (by linarith) hD0 f x
  have hnorm : eLpNorm (primeVariation r f) (ENNReal.ofReal p) Measure.count ≤
      eLpNorm (fun x => ((∑' j : ℕ, varOp r (fun n => wQ (2 ^ j) n *
          psiTailZ ψ (kminD D₀ (2 ^ j)) n) (⇑f) x +
        ∑ q ∈ (leftoverSet_finite D₀).toFinset, varOp r (pairW ψ q.1 q.2) (⇑f) x) +
        ∑' k : ℕ, ∑ j ∈ highJ D₀ (k + 1), varOp r (pairW ψ (k + 1) j) (⇑f) x) +
        ∑' k : ℕ, varOp r (fun n => resWeight (k + 1) n * psiKz ψ (k + 1) n) (⇑f) x)
        (ENNReal.ofReal p) Measure.count := eLpNorm_count_mono_enn hpt _
  refine hnorm.trans ?_
  refine (eLpNorm_count_add_le _ _ hp1).trans ?_
  refine (add_le_add (eLpNorm_count_add_le _ _ hp1) le_rfl).trans ?_
  refine (add_le_add (add_le_add (eLpNorm_count_add_le _ _ hp1) le_rfl) le_rfl).trans ?_
  -- the four pieces
  have hL₁ : eLpNorm (fun x => ∑' j : ℕ, varOp r (fun n => wQ (2 ^ j) n *
        psiTailZ ψ (kminD D₀ (2 ^ j)) n) (⇑f) x) (ENNReal.ofReal p) Measure.count ≤
      ∑' j : ℕ, eLpNorm (S.VQr r (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count +
        ENNReal.ofReal γ * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
    refine (eLpNorm_count_tsum_le _ hp1).trans ?_
    have h1 : ∀ j : ℕ, eLpNorm (varOp r (fun n => wQ (2 ^ j) n *
          psiTailZ ψ (kminD D₀ (2 ^ j)) n) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
        eLpNorm (S.VQr r (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count +
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
        varOp r (pairW ψ q.1 q.2) (⇑f) x) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal C_left * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count :=
    (eLpNorm_count_finset_sum_le _ _ hp1).trans (hleft f)
  have hH : eLpNorm (fun x => ∑' k : ℕ, ∑ j ∈ highJ D₀ (k + 1),
        varOp r (pairW ψ (k + 1) j) (⇑f) x) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal C_high * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
    refine (eLpNorm_count_tsum_le _ hp1).trans ?_
    refine le_trans (ENNReal.tsum_le_tsum fun k => ?_) (hhigh f)
    exact (eLpNorm_count_finset_sum_le _ _ hp1)
  have hR : eLpNorm (fun x => ∑' k : ℕ, varOp r (fun n => resWeight (k + 1) n *
        psiKz ψ (k + 1) n) (⇑f) x) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal C_res * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count :=
    (eLpNorm_count_tsum_le _ hp1).trans (hres f)
  -- assemble
  set X := eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count with hX
  set T := ∑' j : ℕ, eLpNorm (S.VQr r (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count with hT
  calc _ ≤ ((T + ENNReal.ofReal γ * X) + ENNReal.ofReal C_left * X) +
          ENNReal.ofReal C_high * X + ENNReal.ofReal C_res * X := by
        gcongr
    _ = ENNReal.ofReal (C_res + C_high + C_left + γ) * X + T := by
        rw [ENNReal.ofReal_add (by positivity) hγ0, ENNReal.ofReal_add (by positivity)
          hCleft0, ENNReal.ofReal_add hCres0 hChigh0]
        ring

/-- **Proposition `p:red-var`** (L1227–L1242): for `r > 2`, `p > r'` and
`HighQSum r p D₁`, every setup `S` with `D₀ ≥ D₁` for which `e:red-var` holds (with one exponent
`c > 0` and one constant for all dyadic `Q`) has `‖V^r_P f‖_{ℓ^p} ≤ K ‖f‖_{ℓ^p}` for every finitely
supported `f`. -/
theorem red_var_param {r p D₁ : ℝ} (hr : 2 < r) (hp : r / (r - 1) < p) (hF : FplusProp31)
    (hV : VarCarZ r) (hH : HighQSum r p D₁) :
    ∀ S : KQSetup, LocalU3VarRed S.ψ r → D₁ ≤ S.P.D₀ →
      (∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ (j : ℕ) (f : ℤ →₀ ℂ),
        eLpNorm (S.VQr r (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
          ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-c)) *
            eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count) →
      ∃ K : ℝ, 0 < K ∧ ∀ f : ℤ →₀ ℂ,
        eLpNorm (primeVariation r f) (ENNReal.ofReal p) Measure.count ≤
          ENNReal.ofReal K * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  intro S hLoc hD ⟨c, hc, C, hC⟩
  obtain ⟨C₁, hC₁0, hC₁⟩ := combine_pieces_param hr hp hF hV hH S hLoc hD
  set G : ℝ := max C 0 * (1 - (2 : ℝ) ^ (-c))⁻¹ with hG
  have hq1 : (2 : ℝ) ^ (-c) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hG0 : 0 ≤ G := mul_nonneg (le_max_right _ _) (inv_nonneg.2 (by linarith))
  refine ⟨C₁ + G + 1, by positivity, fun f => ?_⟩
  refine (hC₁ f).trans ?_
  have h2 := dyadic_Q_sum S hc hC f
  calc ENNReal.ofReal C₁ * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count +
        ∑' j : ℕ, eLpNorm (S.VQr r (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count
      ≤ ENNReal.ofReal C₁ * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count +
        ENNReal.ofReal G * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := add_le_add le_rfl h2
    _ = ENNReal.ofReal (C₁ + G) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
        rw [ENNReal.ofReal_add hC₁0 hG0, add_mul]
    _ ≤ ENNReal.ofReal (C₁ + G + 1) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl

end PrimeCarleson.Proof.Paper

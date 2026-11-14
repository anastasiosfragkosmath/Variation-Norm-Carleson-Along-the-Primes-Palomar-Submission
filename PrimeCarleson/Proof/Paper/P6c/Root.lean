module

public import PrimeCarleson.Proof.Paper.P6c.Main
public import PrimeCarleson.Proof.Paper.P6b.Interp
public import PrimeCarleson.Proof.Paper.P10.BlockSum

/-!
# The conditional provider for `t:carmax`

Source: main paper `t:carmax`, L329–L334; main paper `l:red-var-l2`, L1565–L1573; main paper
`s:red`, L1521–L1528 and
L1729–L1746.

* `CQ_lp_saving` (the `ℓ^p` saving for `C^Q`, L1565–L1573): for every `1 < p < ∞`,
  `‖C^Q f‖_{ℓ^p} ≲_p Q^{-c_p} ‖f‖_{ℓ^p}` for all dyadic `Q`, for the setups `S` with `D₀` large
  (`exists_D₀_cqL2Saving`, the `ℓ²` saving of `P10/BlockSum.lean` (Source: main paper `s:number`,
  L1742–L1745), and `maximal_part` of `P6b/Interp.lean`);
* `exists_KQSetup`: setups with `D₀` as large as desired and the support condition (C1);
* `prime_carleson_maximal_of_inputs`: the statement of the theorem
  `PrimeCarleson.prime_carleson_maximal` (`t:carmax`), conditional on `hO : OplusVariationBound`
  (the `[O+]` statement) and `hF : FplusProp31` (the `[F+, Proposition 3.1]`
  statement). Both are proved in this repository, and the theorem's proof applies this
  theorem to them (`PrimeCarleson/Proof/PrimeCarlesonMaximal.lean`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- **The `ℓ^p` saving for `C^Q`** (Source: main paper `l:red-var-l2`, L1565–L1573; main paper
L1735–L1746; conditional on `hO`): there is `D₁` such that for every setup `S` with `D₀ ≥ D₁` and
the support condition `SupportBlock` (so `ε = ε(D₀)` and `κ` is small) and every `1 < p < ∞` there
are `c_p > 0` and `C` with `‖C^Q f‖_{ℓ^p} ≤ C Q^{-c_p} ‖f‖_{ℓ^p}` for every dyadic `Q = 2^j` and
finitely supported `f` (the `ℓ²` saving `Q^{-ε/2}` of `P10/BlockSum.lean` interpolated by
`maximal_part`). -/
theorem CQ_lp_saving (hO : OplusVariationBound) :
    ∃ D₁ : ℝ, ∀ S : KQSetup, D₁ ≤ S.P.D₀ → S.P.SupportBlock S.δ → ∀ p : ℝ, 1 < p →
      ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (f : ℤ →₀ ℂ),
        eLpNorm (S.CQ (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
          ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-c)) *
            eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨D₁, hD₁⟩ := exists_D₀_cqL2Saving hO
  refine ⟨D₁, fun S hD hS p hp => ?_⟩
  obtain ⟨C, -, hC⟩ := hD₁ S hD hS
  have hε : 0 < S.P.ε / 2 := by have := S.P.ε_pos; positivity
  exact maximal_part hO S hS hε hC hp

/-- **Setups of `K_Q` with `D₀` large and the support condition**: for every `D₁` there is a setup
`S` (the fixed cutoffs `ψ`, `φ` and the parameters `D₀ ≥ D₁`, `ε = 1/(101 D₀)`) satisfying (C1)
`SupportBlock S.δ`. -/
theorem exists_KQSetup (D₁ : ℝ) : ∃ S : KQSetup, D₁ ≤ S.P.D₀ ∧ S.P.SupportBlock S.δ := by
  obtain ⟨P, hP, -⟩ := KQParams.exists_ge D₁
  obtain ⟨δ, hδ, hδS⟩ := P.exists_delta0 (c := 1) one_pos
  obtain ⟨φ⟩ := PhiData.nonempty hδ
  obtain ⟨ψ⟩ := PsiData.nonempty
  exact ⟨⟨ψ, δ, hδ, φ, P⟩, hP, (hδS δ hδ le_rfl).1⟩

/-- **`t:carmax`, conditional on the `[O+]` and `[F+]` statements** (Theorem
`t:carmax`, L329-L334; proof L1521-L1528, L1735-L1746). Its conclusion is exactly the statement of
the theorem `PrimeCarleson.prime_carleson_maximal`: for every `1 < p < ∞` there is
`0 < K < ∞` with `‖𝒞_ℙ f‖_{ℓ^p} ≤ K ‖f‖_{ℓ^p}` for every finitely supported `f`. The only
hypotheses are `hO : OplusVariationBound` (`[O+]`, the
`variation_norm_carleson_real`) and `hF : FplusProp31` (`[F+, Proposition 3.1]`, the
`vonMangoldt_sub_heathBrown_U3`). -/
theorem prime_carleson_maximal_of_inputs (hO : OplusVariationBound) (hF : FplusProp31) :
    ∀ p : ℝ, 1 < p → ∃ K : ℝ, 0 < K ∧ ∀ f : ℤ →₀ ℂ,
      eLpNorm (carlesonMax (ArithmeticFunction.vonMangoldt : ℕ → ℝ) f) (ENNReal.ofReal p)
          Measure.count ≤
        ENNReal.ofReal K * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  intro p hp
  obtain ⟨D₁, hD₁⟩ := maximal_endpoint_reduction hO hF hp
  obtain ⟨D₂, hD₂⟩ := CQ_lp_saving hO
  obtain ⟨S, hS1, hS2⟩ := exists_KQSetup (max D₁ D₂)
  obtain ⟨c, hc, C, -, hC⟩ := hD₂ S (le_trans (le_max_right _ _) hS1) hS2 p hp
  exact hD₁ S (le_trans (le_max_left _ _) hS1) ⟨c, hc, C, hC⟩

end PrimeCarleson.Proof.Paper

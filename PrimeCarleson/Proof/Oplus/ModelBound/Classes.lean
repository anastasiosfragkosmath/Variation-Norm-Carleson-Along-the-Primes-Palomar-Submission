module

public import PrimeCarleson.Proof.Oplus.ModelBound.Interpolation
public import PrimeCarleson.Proof.Oplus.Decomposition.Sorting

/-!
# The model bound in the form consumed by `linearizedtheorem` ([O+] L1059-L1067)

The statements of `ModelBound/Interpolation.lean` (`model_strong_type`) for the standard constants
`C₁, C₂, C₃ = 12, 2, 11/10`, restated for the ten classes `ρ ∈ R` as they arise from a finite family
of tiles `𝔓` (`Multitile.ofTiles`, `RIdx.choice`, Decomposition/Sorting.lean), and the sum of the
ten classes:

* `classOp_strong_type`: `‖𝒮^ρ_𝔓[f]‖_{L^p} ≤ C ‖f‖_{L^p}` for every `ρ ∈ R` (as `RIdx`);
* `waveOp_strong_type`: `‖𝒮''_𝔓[f]‖_{L^p} ≤ 10 C ‖f‖_{L^p}` (`𝒮'' = ∑_{ρ ∈ R} 𝒮^ρ`,
  `waveOp_eq_sum_modelOp`; the ten strong bounds are added by Minkowski in `L^p`, in place of the
  quasi-triangle inequality of weak `L^p` of the printed route).

Both hold for every `r > 2`, `r' < p < 2r/(r-2)`, every finite family `𝔓` of tiles, every
linearizing data with `Ξ` free of dyadic end points, with `C = C(p, r)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- `model_strong_type` for the ten classes `ρ ∈ R` of a finite family of tiles. -/
theorem classOp_strong_type {r p : ℝ} (hr : 2 < r) (hp1 : Real.conjExponent r < p)
    (hp2 : p < 2 * r / (r - 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : RIdx) (L : Linearization r), AvoidsDyadicEndpoints (L.Ξ : Set ℝ) →
      ∀ (𝔓 : Finset Tile) {f : ℝ → ℂ}, MemLp f (ENNReal.ofReal p) volume →
      eLpNorm (modelOp ρ.choice L (Multitile.ofTiles ρ.toIdx 𝔓) f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC0, h⟩ := model_strong_type hr hp1 hp2 admissibleConstants_std rfl
  exact ⟨C, hC0, fun ρ L hΞ 𝔓 f hf =>
    h ρ.toIdx_isStd ρ.choice L hΞ (Multitile.ofTiles ρ.toIdx 𝔓) hf⟩

/-- **The strong `L^p` bound for `𝒮''_𝔓`** (the model bound for [O+] `linearizedtheorem`):
`‖𝒮''_𝔓[f]‖_{L^p} ≤ 10 C ‖f‖_{L^p}` for every finite family `𝔓` of tiles, `f ∈ L^p` (in particular
every Schwartz function) and linearizing data with `Ξ` free of dyadic end points. -/
theorem waveOp_strong_type {r p : ℝ} (hr : 2 < r) (hp1 : Real.conjExponent r < p)
    (hp2 : p < 2 * r / (r - 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Linearization r), AvoidsDyadicEndpoints (L.Ξ : Set ℝ) →
      ∀ (𝔓 : Finset Tile) {f : ℝ → ℂ}, MemLp f (ENNReal.ofReal p) volume →
      eLpNorm (waveOp L 𝔓 f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  have hr1 : 1 < r := by linarith
  have hp0 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 (by
    linarith [one_lt_conjExponent hr1])
  obtain ⟨C, hC0, h⟩ := classOp_strong_type hr hp1 hp2
  refine ⟨10 * C, by positivity, fun L hΞ 𝔓 f hf => ?_⟩
  have hfun : waveOp L 𝔓 f = ∑ ρ : RIdx, modelOp ρ.choice L (Multitile.ofTiles ρ.toIdx 𝔓) f :=
    funext fun x => by rw [Finset.sum_apply]; exact waveOp_eq_sum_modelOp L hΞ 𝔓 f x
  rw [hfun]
  refine (eLpNorm_sum_le hp0).trans ?_
  calc ∑ ρ : RIdx, eLpNorm (modelOp ρ.choice L (Multitile.ofTiles ρ.toIdx 𝔓) f)
        (ENNReal.ofReal p) volume
      ≤ ∑ _ρ : RIdx, ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume :=
        Finset.sum_le_sum fun ρ _ => h ρ L hΞ 𝔓 hf
    _ = ENNReal.ofReal (10 * C) * eLpNorm f (ENNReal.ofReal p) volume := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (by norm_num)]
        have hc : Fintype.card RIdx = 10 := by decide
        rw [hc, ← mul_assoc]
        norm_num

end PrimeCarleson.Proof.Oplus

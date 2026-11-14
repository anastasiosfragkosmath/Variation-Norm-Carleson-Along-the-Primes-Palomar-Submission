module

public import PrimeCarleson.Proof.Paper.P10.Final
public import PrimeCarleson.Proof.Paper.P9.Truncation

/-!
# The `ℓ²` bound for `C^Q`: summation over the blocks

Source: main paper `s:number`, L1742–L1745, L1938–L1941 and L2544–L2553. The paper does not write
out the derivation of this bound from the transference estimate; it is proved here.

`C^Q f ≤ ∑_B C^Q_B f` (`CQ_le_sum_CQB` of `P5/Blocks.lean`), the `ℓ²` triangle inequality,
`p:transferprop`
(`transferprop`: `‖C^Q_B f‖ ≲ Q^{ε/10} 𝔪_B ‖f‖`), `𝔪_B ≲ Q^{κ-1-ε}` (the
`periodicBlockMax_bound`, through `mB_le_of_blockPartition`) and `#blocks ≤ 48 Q^{1-κ}`
(`blocks_card_le`) give `‖C^Q f‖_{ℓ²} ≲ Q^{-9ε/10} ‖f‖_{ℓ²} ≤ Q^{-ε/2} ‖f‖_{ℓ²}`.

**The small-`Q` regime.** The paper's derivation needs `Q ≥ Q₀(ε)`; here every ingredient holds for
*every* dyadic `Q = 2^j` with a constant independent of `j`: `p:transferprop` for all `Q` (under the
support condition `SupportBlock`, which is the paper's "`φ̂` supported in a sufficiently small
neighbourhood of `0`" for the finitely many small `Q`, L2224), and `periodicBlockMax_bound` for all
`j`. So no threshold `Q₀` and no separate treatment of small `Q` is needed
(`cqL2Saving_of_kappa_le`).

The threshold `κ₀` of the `periodicBlockMax_bound` (`D₀` sufficiently large, L1188) is the
named constant `blockKappaZero` (`≤ 1/2`); the hypothesis `κ ≤ blockKappaZero` is the paper's "`D₀`
large".
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-- The threshold `κ₀ ≤ 1/2` of the `periodicBlockMax_bound` (`D₀` large: `κ = 1/D₀ - ε
≤ κ₀`), capped at `1/2`. -/
def blockKappaZero : ℝ := min (Classical.choose mB_le_of_blockPartition) (1 / 2)

theorem blockKappaZero_pos : 0 < blockKappaZero :=
  lt_min (Classical.choose_spec mB_le_of_blockPartition).1 (by norm_num)

theorem blockKappaZero_le_half : blockKappaZero ≤ 1 / 2 := min_le_right _ _

/-- The bound `𝔪_B ≲ Q^{κ-1-ε}` for the blocks of a partition, for `κ ≤ blockKappaZero`. -/
theorem mB_le_of_kappa_le {κ : ℝ} (hκ : 0 < κ) (hκ0 : κ ≤ blockKappaZero) {ε : ℝ} (hε : 0 < ε)
    (hεκ : ε ≤ κ / 100) (A : ℝ) :
    ∃ C : ℝ, ∀ (j : ℕ) (π : BlockPartition j κ A), ∀ B ∈ π.blocks,
      mB B ≤ |C| * ((2 : ℝ) ^ j) ^ (κ - 1 - ε) :=
  (Classical.choose_spec mB_le_of_blockPartition).2 κ hκ (hκ0.trans (min_le_left _ _)) ε hε hεκ A

/-- **Summation over the blocks** (Source: main paper, L2544; the paper does not write it): under
`[O+]`, (C1)
`SupportBlock` and `κ ≤ blockKappaZero`, there is `C` with
`‖C^Q f‖_{ℓ²} ≤ C Q^{-9ε/10} ‖f‖_{ℓ²}` for every dyadic `Q = 2^j` and finitely supported `f`. -/
theorem block_sum (hO : OplusVariationBound) (S : KQSetup) (hS : S.P.SupportBlock S.δ)
    (hκ : S.P.kappa ≤ blockKappaZero) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (f : ℤ →₀ ℂ),
      eLpNorm (S.CQ (2 ^ j) (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-(9 * S.P.ε / 10))) *
          eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by
  classical
  have hε := S.P.ε_pos
  have hκ0 := S.P.kappa_pos
  have hκ1 : S.P.kappa < 1 := by linarith [blockKappaZero_le_half]
  obtain ⟨C₁, hC₁⟩ := mB_le_of_kappa_le hκ0 hκ hε (by linarith [S.P.hundred_eps_le_kappa]) 24
  obtain ⟨C, hC0, hC⟩ := transferprop hO S hS hκ1
  refine ⟨48 * C * |C₁|, by positivity, fun j f => ?_⟩
  obtain ⟨π⟩ := exists_blockPartition_24 j hκ0.le hκ1.le
  set Qr : ℝ := (2 : ℝ) ^ j with hQr
  have hQ1 : 1 ≤ Qr := one_le_pow₀ (by norm_num)
  have hQ0 : 0 < Qr := by linarith
  set F : ℝ≥0∞ := eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count with hF
  -- pointwise decomposition and Minkowski
  have hpt : ∀ x : ℤ, S.CQ (2 ^ j) (⇑f) x ≤ ∑ B ∈ π.blocks, S.CQB (2 ^ j) B (⇑f) x :=
    fun x => S.CQ_le_sum_CQB π (⇑f)
      (f.support.finite_toSet.subset fun y hy => Finsupp.mem_support_iff.2 hy) x
  have h1 : eLpNorm (S.CQ (2 ^ j) (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
      ∑ B ∈ π.blocks, eLpNorm (S.CQB (2 ^ j) B (⇑f)) (ENNReal.ofReal 2) Measure.count := by
    simp_rw [eLpNorm_two_eq_tsum_sq]
    exact (ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum fun x => pow_le_pow_left' (hpt x) 2)
      (by norm_num)).trans (tsum_sq_sum_le π.blocks fun B x => S.CQB (2 ^ j) B (⇑f) x)
  -- each block
  have hblock : ∀ B ∈ π.blocks, eLpNorm (S.CQB (2 ^ j) B (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
      ENNReal.ofReal (C * Qr ^ (S.P.ε / 10) * (|C₁| * Qr ^ (S.P.kappa - 1 - S.P.ε))) * F := by
    intro B hB
    refine (hC j B (π.subset_sqfreeSet hB) (π.nonempty_of_mem hB)
      (π.card_le_hundred (by norm_num) hB) f).trans ?_
    rw [← hF]
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    have := hC₁ j π B hB
    have hCQ : 0 ≤ C * Qr ^ (S.P.ε / 10) := by positivity
    calc C * Qr ^ (S.P.ε / 10) * mB B ≤ C * Qr ^ (S.P.ε / 10) *
          (|C₁| * Qr ^ (S.P.kappa - 1 - S.P.ε)) := mul_le_mul_of_nonneg_left this hCQ
      _ = _ := rfl
  have hcard : ((π.blocks.card : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (48 * Qr ^ (1 - S.P.kappa)) := by
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    have := π.blocks_card_le (by norm_num : (0 : ℝ) < 24)
    linarith
  calc eLpNorm (S.CQ (2 ^ j) (⇑f)) (ENNReal.ofReal 2) Measure.count
      ≤ ∑ B ∈ π.blocks, eLpNorm (S.CQB (2 ^ j) B (⇑f)) (ENNReal.ofReal 2) Measure.count := h1
    _ ≤ ∑ _B ∈ π.blocks, ENNReal.ofReal (C * Qr ^ (S.P.ε / 10) *
          (|C₁| * Qr ^ (S.P.kappa - 1 - S.P.ε))) * F := Finset.sum_le_sum hblock
    _ = ((π.blocks.card : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (C * Qr ^ (S.P.ε / 10) *
          (|C₁| * Qr ^ (S.P.kappa - 1 - S.P.ε))) * F) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (48 * Qr ^ (1 - S.P.kappa)) * (ENNReal.ofReal (C * Qr ^ (S.P.ε / 10) *
          (|C₁| * Qr ^ (S.P.kappa - 1 - S.P.ε))) * F) := mul_le_mul_left hcard _
    _ = ENNReal.ofReal (48 * C * |C₁| * Qr ^ (-(9 * S.P.ε / 10))) * F := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        have h3 : Qr ^ (1 - S.P.kappa) * Qr ^ (S.P.ε / 10) * Qr ^ (S.P.kappa - 1 - S.P.ε) =
            Qr ^ (-(9 * S.P.ε / 10)) := by
          rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
          congr 1
          ring
        calc 48 * Qr ^ (1 - S.P.kappa) * (C * Qr ^ (S.P.ε / 10) *
              (|C₁| * Qr ^ (S.P.kappa - 1 - S.P.ε)))
            = 48 * C * |C₁| * (Qr ^ (1 - S.P.kappa) * Qr ^ (S.P.ε / 10) *
              Qr ^ (S.P.kappa - 1 - S.P.ε)) := by ring
          _ = _ := by rw [h3]

/-- **The `ℓ²` saving for `C^Q`** (Source: main paper `s:number`, L1742–L1745, L1938–L1941; the
form `CQL2Saving` consumed in `P6b/`): under `[O+]` (`hO`), the support condition (C1)
`SupportBlock` and `D₀` large (`κ = 1/D₀ - ε ≤ blockKappaZero`, `ε ≤ κ/100` being part of
`KQParams`), there is `C` with `‖C^Q f‖_{ℓ²} ≤ C Q^{-ε/2} ‖f‖_{ℓ²}` for every dyadic `Q = 2^j` and
finitely supported `f`. The statement is exactly `CQL2Saving S` of `P6b/Saving.lean`. -/
theorem cqL2Saving_of_kappa_le (hO : OplusVariationBound) (S : KQSetup)
    (hS : S.P.SupportBlock S.δ) (hκ : S.P.kappa ≤ blockKappaZero) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (f : ℤ →₀ ℂ),
      eLpNorm (S.CQ (2 ^ j) (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-(S.P.ε / 2))) *
          eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by
  obtain ⟨C, hC0, hC⟩ := block_sum hO S hS hκ
  refine ⟨C, hC0, fun j f => (hC j f).trans ?_⟩
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  have hQ1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hε := S.P.ε_pos
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ1 ?_) hC0
  linarith

/-- `D₀` large: there is `D₁` such that every `S` with `D₁ ≤ D₀` and `SupportBlock` has the
`ℓ²` saving `CQL2Saving S`, with the threshold `D₁` quantified. -/
theorem exists_D₀_cqL2Saving (hO : OplusVariationBound) :
    ∃ D₁ : ℝ, ∀ S : KQSetup, D₁ ≤ S.P.D₀ → S.P.SupportBlock S.δ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (f : ℤ →₀ ℂ),
        eLpNorm (S.CQ (2 ^ j) (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
          ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-(S.P.ε / 2))) *
            eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by
  refine ⟨1 / blockKappaZero, fun S hD hS => cqL2Saving_of_kappa_le hO S hS ?_⟩
  have hk0 := blockKappaZero_pos
  have hD0 := S.P.D₀_pos
  have hε := S.P.ε_pos
  have h1 : 1 / S.P.D₀ ≤ blockKappaZero := by
    rw [div_le_iff₀ hD0]
    rw [div_le_iff₀ hk0] at hD
    linarith
  unfold KQParams.kappa
  linarith

end PrimeCarleson.Proof.Paper

module

public import PrimeCarleson.Proof.Paper.P7.Basic
public import PrimeCarleson.Proof.Paper.P7.Sums

/-!
# Translation invariance of the `ℓ^p(ℤ)` norm

A small piece of API: the `ℓ^p(ℤ)` norm of an `ℝ≥0∞`-valued sequence is invariant under
translation (`eLpNorm_count_translate`, for `0 < p`), by the formula of `eLpNorm_count_eq_tsum_enn`
and the reindexing `x ↦ x - k` of the sum over `ℤ`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.MswTransference

/-- Translation invariance of the `ℓ^p(ℤ)` norm of an `ℝ≥0∞`-valued sequence. -/
theorem eLpNorm_count_translate {p : ℝ} (hp : 0 < p) (F : ℤ → ℝ≥0∞) (k : ℤ) :
    eLpNorm (fun x => F (x - k)) (ENNReal.ofReal p) Measure.count =
      eLpNorm F (ENNReal.ofReal p) Measure.count := by
  rw [eLpNorm_count_eq_tsum_enn _ hp, eLpNorm_count_eq_tsum_enn _ hp]
  congr 1
  exact (Equiv.subRight k).tsum_eq (fun x => F x ^ p)

end PrimeCarleson.Proof.Paper

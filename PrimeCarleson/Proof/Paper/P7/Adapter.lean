module

public import PrimeCarleson.Proof.Paper.P7.VarcarZ
public import PrimeCarleson.Proof.Paper.P9.VarCarInput

/-!
# Adapter: `∀ s > 2, ∃ C ≥ 0, LVarCarZ s C` from the Euclidean estimate

The file `P9/VarCarInput.lean` takes `l:varcarZ` as the hypothesis `LVarCarZ s C`, for finitely
supported `f` and finite `T ⊆ [0, 1)`. Here it is proved, for every `s > 2`, from
`OplusVariationBound` (the statement of the theorem `variation_norm_carleson_real`):
`lVarCarZ_of_oplus`. With it `global_shell_var` of `P9/` is conditional only on
`OplusVariationBound`:
`global_shell_var S hS hSc hρ hδ (lVarCarZ_of_oplus hO)`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

/-- **`l:varcarZ` for `P9/`** (conditional on `hO : OplusVariationBound`): for every `s > 2`
there is `C ≥ 0` with `LVarCarZ s C`.

Source: main paper `l:varcarZ`, L1771–L1776. -/
theorem lVarCarZ_of_oplus (hO : OplusVariationBound) :
    ∀ s : ℝ, 2 < s → ∃ C : ℝ, 0 ≤ C ∧ LVarCarZ s C := by
  intro s hs
  obtain ⟨C, hC0, hC⟩ := varcarZ_of_oplus hO hs
  refine ⟨C, hC0, fun khat c₀ u hk hsupp hvar f T _ hT01 => ?_⟩
  have h := hC khat c₀ u hk hsupp hvar f T hT01
  simp_rw [dilSum_one_apply] at h
  exact h

end PrimeCarleson.Proof.Paper

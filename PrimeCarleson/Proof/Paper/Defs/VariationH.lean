module

public import PrimeCarleson.Frozen.RVariationOn
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# The `r`-variation of a normed-group-valued family

The `PrimeCarleson.rVariationOn` is `ℂ`-valued. The entropy lemma `l:entest`
(`sources/Variational_Carleson.tex` L1824-L1860) needs the same `V^r(c_t : t ∈ T)` for a family
`(c_t)` in a finite-dimensional Hilbert space `ℋ ≅ ℓ²(Ξ)`; `rVariationOnH` is the definition of
`rVariationOn` for any seminormed additive group `H`:

`V^r(c_t : t ∈ S) = sup_{t₀ < ⋯ < t_J in S} (∑ᵢ ‖c_{tᵢ} - c_{tᵢ₊₁}‖^r)^{1/r}`, `ℝ≥0∞`-valued.

`rVariationOnH_complex` identifies the case `H = ℂ` with the definition (`rfl`), and
`rVariationOnH_le_iff` and `le_rVariationOnH` give the supremum characterization.

This is the seminorm `V^s_t(ℋ)` only. The norm `Ṽ^s_t(ℋ)` of `l:entest` (L1824–L1848) adds the
supremum of `‖c_t‖_ℋ` (the inhomogeneous norm of L625–L644); the file that proves the entropy
lemma accounts for it through a base-point term `‖c_{u₀}‖_ℋ`.
-/

@[expose] public noncomputable section

open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

variable {H : Type*} [SeminormedAddCommGroup H]

/-- The `r`-variation of a family `c : ℝ → H` over the index set `S ⊆ ℝ` with values in a
seminormed additive group: the supremum over finite increasing sequences `t₀ < ⋯ < t_J` in `S` of
`(∑ᵢ ‖c_{tᵢ} - c_{tᵢ₊₁}‖^r)^{1/r}`; only `0 < r` has source meaning. -/
def rVariationOnH (r : ℝ) (S : Set ℝ) (c : ℝ → H) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (t : Fin (J + 1) → ℝ) (_ : StrictMono t) (_ : ∀ i, t i ∈ S),
    (∑ i : Fin J, ‖c (t i.castSucc) - c (t i.succ)‖ₑ ^ r) ^ (1 / r)

/-- For `H = ℂ` this is the `rVariationOn`. -/
theorem rVariationOnH_complex (r : ℝ) (S : Set ℝ) (a : ℝ → ℂ) :
    rVariationOnH r S a = PrimeCarleson.rVariationOn r S a := rfl

/-- Every finite increasing subsequence of `S` gives at most `V^r`. -/
theorem le_rVariationOnH {r : ℝ} {S : Set ℝ} {c : ℝ → H} {J : ℕ} {t : Fin (J + 1) → ℝ}
    (hm : StrictMono t) (hS : ∀ i, t i ∈ S) :
    (∑ i : Fin J, ‖c (t i.castSucc) - c (t i.succ)‖ₑ ^ r) ^ (1 / r) ≤ rVariationOnH r S c :=
  le_iSup₂_of_le J t <| le_iSup₂_of_le hm hS le_rfl

/-- `V^r ≤ B` exactly when every finite increasing subsequence of `S` gives at most `B`. -/
theorem rVariationOnH_le_iff {r : ℝ} {S : Set ℝ} {c : ℝ → H} {B : ℝ≥0∞} :
    rVariationOnH r S c ≤ B ↔ ∀ (J : ℕ) (t : Fin (J + 1) → ℝ), StrictMono t → (∀ i, t i ∈ S) →
      (∑ i : Fin J, ‖c (t i.castSucc) - c (t i.succ)‖ₑ ^ r) ^ (1 / r) ≤ B :=
  ⟨fun h _ _ hm hS => (le_rVariationOnH hm hS).trans h,
    fun h => iSup_le fun J => iSup_le fun t => iSup_le fun hm => iSup_le fun hS => h J t hm hS⟩

/-- The variation only depends on the values of the family on the index set. -/
theorem rVariationOnH_congr {r : ℝ} {S : Set ℝ} {c c' : ℝ → H} (h : ∀ t ∈ S, c t = c' t) :
    rVariationOnH r S c = rVariationOnH r S c' := by
  unfold rVariationOnH
  refine iSup_congr fun J => iSup_congr fun t => iSup_congr fun _ => iSup_congr fun ht => ?_
  refine congrArg (· ^ (1 / r)) (Finset.sum_congr rfl fun i _ => ?_)
  rw [h _ (ht _), h _ (ht _)]

end PrimeCarleson.Proof.Paper

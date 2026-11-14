module

public import PrimeCarleson.Proof.Common.VariationDyadic
public import PrimeCarleson.Proof.Paper.Defs.Basic
public import Mathlib.Data.Fin.Tuple.Sort

/-!
# The splitting inequality for the `r`-variation

An inequality of the "Variational Preliminaries" of `sources/Variational_Carleson.tex`
(L901-L904), proved for the `PrimeCarleson.rVariationOn` with absolute constants. It is a
wrapper of `Common/VariationDyadic.lean`, in the form the paper states it.

* `e:split` (Source: main paper `e:split`, L901–L904; consumers `e:embed`, L1115, and the proofs
  of `p:global-shell-var`, L1960, and `p:disc`, L2964): let `J ⊆ ℝ` be covered by
  `N` intervals `[Aₙ, Bₙ]` with `Bₙ ∈ J`, and let the pieces `Jₙ := J ∩ [Aₙ, Bₙ]` be pairwise
  disjoint (a disjoint partition of `J`). Then for `1 ≤ r`
  `V^r(a : J) ≤ 3 (∑ₙ V^r(a : Jₙ)^r)^{1/r} + V^r(a_{Bₙ} : n)` and
  `V^r(a_{Bₙ} : n) ≤ 2 (∑ₙ |a_{Bₙ}|^r)^{1/r}`, hence the second line
  `V^r(a : J) ≲ (∑ₙ V^r(a : Jₙ)^r)^{1/r} + (∑ₙ |a_{Bₙ}|^r)^{1/r}` (`split_inequality`,
  `split_inequality_norm`). The ordering of the intervals, implicit in the paper (and needed to
  read `V^r(a_{Bₙ} : n)` as a variation), is derived from the disjointness of the pieces: the
  endpoints `Bₙ` are distinct, and the variation of the sequence `(a_{Bₙ})` is the variation
  of `a` over the set `{Bₙ}` of its indices in increasing order (`Set.range B`).
  `split_inequality_ordered` is the version with the intervals already ordered.
  The exponent range is `1 ≤ r` (every consumer has `r ≥ 2`): for `r < 1` the constant of the
  second line cannot be absolute (it is `2^{1/r}` for `a = (1, 0, 1, 0, …)`).
-/

@[expose] public noncomputable section

open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-! ### `e:split` -/

/-- **`e:split`, ordered form** (Source: main paper `e:split`, L901–L904): intervals
`[Aₙ, Bₙ]` ordered
(`Bₙ < Aₙ'` for `n < n'`) with right endpoints `Bₙ ∈ J` covering `J`, split as
`Jₙ = J ∩ [Aₙ, Bₙ]`. For `1 ≤ r`,
`V^r(a : J) ≤ 3 (∑ₙ V^r(a : Jₙ)^r)^{1/r} + V^r(a_{Bₙ} : n)` with
`V^r(a_{Bₙ} : n) ≤ 2 (∑ₙ |a_{Bₙ}|^r)^{1/r}`. -/
theorem split_inequality_ordered {r : ℝ} (hr : 1 ≤ r) {N : ℕ} (A B : Fin N → ℝ) (J : Set ℝ)
    (hAB : ∀ n, A n ≤ B n) (hlt : ∀ n n' : Fin N, n < n' → B n < A n')
    (hJ : J ⊆ ⋃ n, Set.Icc (A n) (B n)) (hB : ∀ n, B n ∈ J) (a : ℝ → ℂ) :
    rVariationOn r J a ≤
        3 * (∑ n, rVariationOn r (J ∩ Set.Icc (A n) (B n)) a ^ r) ^ (1 / r) +
          rVariationOn r (Set.range B) a ∧
      rVariationOn r (Set.range B) a ≤ 2 * (∑ n, ‖a (B n)‖ₑ ^ r) ^ (1 / r) := by
  have hBmono : StrictMono B := fun n n' h => lt_of_lt_of_le (hlt n n' h) (hAB n')
  exact ⟨Common.rVariationOn_split_Icc hr A B J hAB hlt hJ hB a,
    Common.rVariationOn_range_le hr hBmono.injective a⟩

/-- The endpoints `Bₙ` of pairwise disjoint pieces `J ∩ [Aₙ, Bₙ]` with `Bₙ ∈ J` are distinct. -/
theorem injective_endpoints_of_disjoint {N : ℕ} (A B : Fin N → ℝ) (J : Set ℝ)
    (hAB : ∀ n, A n ≤ B n) (hB : ∀ n, B n ∈ J)
    (hdisj : Pairwise fun n n' => Disjoint (J ∩ Set.Icc (A n) (B n)) (J ∩ Set.Icc (A n') (B n'))) :
    Function.Injective B := by
  intro n n' h
  by_contra hne
  refine Set.disjoint_left.1 (hdisj hne)
    (⟨hB n, hAB n, le_rfl⟩ : B n ∈ J ∩ Set.Icc (A n) (B n)) ?_
  rw [h]
  exact ⟨hB n', hAB n', le_rfl⟩

/-- **`e:split`, disjoint partition form** (Source: main paper `e:split`, L901–L904),
exactly the
paper's hypotheses: `J = ⋃ₙ Jₙ` with `Jₙ = J ∩ [Aₙ, Bₙ]` a disjoint partition and `Bₙ ∈ J`
(`Jₙ` need not be listed in increasing order). For `1 ≤ r`, with absolute constants,
`V^r(a_λ : λ ∈ J) ≤ 3 (∑ₙ V^r(a_λ : λ ∈ Jₙ)^r)^{1/r} + V^r(a_{Bₙ} : n)` and
`V^r(a_{Bₙ} : n) ≤ 2 (∑ₙ |a_{Bₙ}|^r)^{1/r}`; `V^r(a_{Bₙ} : n)` is the `r`-variation of `a` over
the set `{Bₙ : n}` of the (distinct) endpoints. -/
theorem split_inequality {r : ℝ} (hr : 1 ≤ r) {N : ℕ} (A B : Fin N → ℝ) (J : Set ℝ)
    (hAB : ∀ n, A n ≤ B n) (hB : ∀ n, B n ∈ J) (hJ : J ⊆ ⋃ n, Set.Icc (A n) (B n))
    (hdisj : Pairwise fun n n' => Disjoint (J ∩ Set.Icc (A n) (B n)) (J ∩ Set.Icc (A n') (B n')))
    (a : ℝ → ℂ) :
    rVariationOn r J a ≤
        3 * (∑ n, rVariationOn r (J ∩ Set.Icc (A n) (B n)) a ^ r) ^ (1 / r) +
          rVariationOn r (Set.range B) a ∧
      rVariationOn r (Set.range B) a ≤ 2 * (∑ n, ‖a (B n)‖ₑ ^ r) ^ (1 / r) := by
  classical
  have hBinj := injective_endpoints_of_disjoint A B J hAB hB hdisj
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin N), Monotone (B ∘ σ) :=
    ⟨Tuple.sort B, Tuple.monotone_sort B⟩
  have hσs : StrictMono (B ∘ σ) := hσ.strictMono_of_injective (hBinj.comp σ.injective)
  have hlt : ∀ n n' : Fin N, n < n' → B (σ n) < A (σ n') := by
    intro n n' hnn'
    by_contra hge
    push Not at hge
    have hBlt : B (σ n) < B (σ n') := hσs hnn'
    exact Set.disjoint_left.1 (hdisj (σ.injective.ne hnn'.ne))
      (⟨hB _, hAB _, le_rfl⟩ : B (σ n) ∈ J ∩ Set.Icc (A (σ n)) (B (σ n)))
      ⟨hB _, hge, hBlt.le⟩
  have hJ' : J ⊆ ⋃ n, Set.Icc (A (σ n)) (B (σ n)) := by
    refine hJ.trans fun x hx => ?_
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    obtain ⟨n, rfl⟩ := σ.surjective i
    exact Set.mem_iUnion.2 ⟨n, hi⟩
  obtain ⟨h1, h2⟩ := split_inequality_ordered hr (fun n => A (σ n)) (fun n => B (σ n)) J
    (fun n => hAB _) hlt hJ' (fun n => hB _) a
  have hrange : Set.range (fun n => B (σ n)) = Set.range B := σ.surjective.range_comp B
  have hsum1 : ∑ n, rVariationOn r (J ∩ Set.Icc (A (σ n)) (B (σ n))) a ^ r =
      ∑ n, rVariationOn r (J ∩ Set.Icc (A n) (B n)) a ^ r :=
    Equiv.sum_comp σ fun n => rVariationOn r (J ∩ Set.Icc (A n) (B n)) a ^ r
  have hsum2 : ∑ n, ‖a (B (σ n))‖ₑ ^ r = ∑ n, ‖a (B n)‖ₑ ^ r :=
    Equiv.sum_comp σ fun n => ‖a (B n)‖ₑ ^ r
  rw [hrange, hsum1] at h1
  rw [hrange, hsum2] at h2
  exact ⟨h1, h2⟩

/-- **`e:split`, second line** (Source: main paper `e:split`, L901–L904): in the
hypotheses of
`split_inequality`, `V^r(a_λ : λ ∈ J) ≤ 3 (∑ₙ V^r(a_λ : λ ∈ Jₙ)^r)^{1/r} +
2 (∑ₙ |a_{Bₙ}|^r)^{1/r}`, for `1 ≤ r`. -/
theorem split_inequality_norm {r : ℝ} (hr : 1 ≤ r) {N : ℕ} (A B : Fin N → ℝ) (J : Set ℝ)
    (hAB : ∀ n, A n ≤ B n) (hB : ∀ n, B n ∈ J) (hJ : J ⊆ ⋃ n, Set.Icc (A n) (B n))
    (hdisj : Pairwise fun n n' => Disjoint (J ∩ Set.Icc (A n) (B n)) (J ∩ Set.Icc (A n') (B n')))
    (a : ℝ → ℂ) :
    rVariationOn r J a ≤
      3 * (∑ n, rVariationOn r (J ∩ Set.Icc (A n) (B n)) a ^ r) ^ (1 / r) +
        2 * (∑ n, ‖a (B n)‖ₑ ^ r) ^ (1 / r) := by
  obtain ⟨h1, h2⟩ := split_inequality hr A B J hAB hB hJ hdisj a
  exact h1.trans (add_le_add_right h2 _)

end PrimeCarleson.Proof.Paper

module

public import PrimeCarleson.Proof.Fplus31.C2.Descent
public import OAI.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity
public import OAI.Combinatorics.Progressions.Nilpotent.LinearBCHAbelian
public import PrimeCarleson.Proof.Fplus31.C2.Symbol
public import PrimeCarleson.Proof.Fplus31.G1.Start

/-!
# The sub-step, the state of the iteration

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). The next
state of the iteration after a stage (the extrapolation step, lift, freezing, sub-model) is a
niltest on a model of smaller dimension or degree. The two forms the iteration iterates:

* `VerticalNiltest deg p`: a one-variable niltest of complexity `p` on a model of degree `deg` with
  a vertical frequency `η` of height `≤ p` (a `LengStart` without the adapted basis, the
  nonvanishing of `η` and the correlation); the frequency is kept from the previous stage, which is
  what makes the flag (`[gr₁, gr₁] ⊆ ker η`) automatic on the sub-model;
* `NiltestData deg` (`Descent.lean`): a niltest without frequency, after a degree drop, to which the
  start step (`exists_leng_start_or_top_invariant`) is applied again.

* `finrank_gradedRefiltrationSubalgebra_lt`, `finrank_lt_or_flag`: the potential: for
  `K = W + [gr, gr]` the sub-model has strictly smaller dimension, or the flag holds;
* `gradedFrequency_kills_top_of_flag`: with the flag, `η` kills the top layer of `K`, so the next
  stage descends in degree.
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators NNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Module NilpotentLieFiltration VectorPolynomial RationalFilteredNilmanifold
  NilpotentLieBCHGroup

/-- A vertical niltest: a one-variable niltest `T` of complexity `p` and norm at most one on a
rational filtered nilmanifold of degree `deg`, which is a vertical character of the top layer with
the rational frequency `η` of height at most `p`. -/
structure VerticalNiltest (deg : ℕ) (p : ℝ) where
  /-- The Lie algebra. -/
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  /-- The dimension. -/
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  /-- The model. -/
  D : RationalFilteredNilmanifold L deg dim
  /-- The niltest. -/
  T : D.Niltest (fun _ : Unit => 1)
  /-- The vertical frequency. -/
  η : L →ₗ[ℚ] ℚ
  complexity : T.ComplexityLE p
  norm_le : T.normBound ≤ 1
  eta_height : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p
  vertical : ∀ z ∈ D.filtration.realification.subgroup deg, ∀ x,
    T.observable (z • x) =
      CircleFourier.character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
        T.observable x

attribute [instance] VerticalNiltest.lie VerticalNiltest.algebra VerticalNiltest.topology
  VerticalNiltest.topologicalAdd VerticalNiltest.continuousSMul VerticalNiltest.hausdorff

namespace VerticalNiltest

variable {deg : ℕ} {p q : ℝ}

/-- A vertical niltest of complexity `p` is one of every larger complexity. -/
def mono (V : VerticalNiltest deg p) (hpq : p ≤ q) : VerticalNiltest deg q where
  L := V.L
  dim := V.dim
  D := V.D
  T := V.T
  η := V.η
  complexity := V.complexity.mono hpq
  norm_le := V.norm_le
  eta_height := fun i => (V.eta_height i).trans hpq
  vertical := V.vertical

end VerticalNiltest

section Flag

variable {ι L : Type*} [Finite ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

omit [Finite ι] in
/-- **The dimension drops, or the flag already holds.**  If some weight-one element of `gr` is not
in `K`, the refiltered subgroup `gradedRefiltrationSubalgebra K` is a proper subalgebra, of strictly
smaller dimension. -/
theorem finrank_gradedRefiltrationSubalgebra_lt [Module.Finite ℚ L]
    (K : LieSubalgebra ℚ F.AssociatedGraded)
    (h : ∃ x, basisGradeProjection (F.associatedGradedBasis b ω hF) ω 1 x = x ∧ x ∉ K) :
    finrank ℚ (F.gradedRefiltrationSubalgebra K) < finrank ℚ L := by
  obtain ⟨x, hx1, hxK⟩ := h
  obtain ⟨v, hv⟩ := F.exists_associatedGradedPieceMap_of_pure b ω hF 1 x hx1
  have hvH : (v : L) ∉ (F.gradedRefiltrationSubalgebra K).toSubmodule := by
    intro hmem
    exact hxK (hv ▸ (F.mem_gradedRefiltrationLayer_iff K 1 v).mp hmem)
  exact Submodule.finrank_lt (fun h => hvH (h ▸ Submodule.mem_top))

omit [LieRing L] [LieAlgebra ℚ L] in
/-- The weight projection is idempotent. -/
theorem gradeProjection_idem {V : Type*} [AddCommGroup V] [Module ℚ V] {κ : Type*}
    (B : Basis κ ℚ V) (ω : κ → ℕ) (j : ℕ) (x : V) :
    basisGradeProjection B ω j (basisGradeProjection B ω j x) = basisGradeProjection B ω j x := by
  apply B.repr.injective
  ext i
  rw [basisGradeProjection_repr, basisGradeProjection_repr]
  by_cases h : ω i = j
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

/-- In a step-two graded Lie algebra the bracket only sees the weight-one parts. -/
theorem lie_eq_lie_gradeProjection_one {V : Type*} [LieRing V] [LieAlgebra ℚ V] {κ : Type*}
    [Finite κ] {B : Basis κ ℚ V} {ω : κ → ℕ} (hB : Step2Graded B ω) (x y : V) :
    ⁅x, y⁆ = ⁅basisGradeProjection B ω 1 x, basisGradeProjection B ω 1 y⁆ := by
  have := Fintype.ofFinite κ
  apply B.repr.injective
  ext k
  rcases hB.weight k with hk | hk
  · rw [repr_lie_eq_zero_of_weight B ω hB.weight hB.bracket x y hk,
      repr_lie_eq_zero_of_weight B ω hB.weight hB.bracket _ _ hk]
  · rw [repr_lie_eq_sum_idx B ω hB.weight hB.bracket x y hk,
      repr_lie_eq_sum_idx B ω hB.weight hB.bracket _ _ hk]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [basisGradeProjection_repr, basisGradeProjection_repr, ite_eq_left i.2, ite_eq_left j.2]

/-- **The kill lemma for the descending stage.** If `η` kills the top layer of `W` and the flag
holds (`η ⁅x, y⁆ = 0` for weight-one `x, y`), then `η` kills the top layer of `K = W + [gr, gr]`; so
the refiltered top layer of `K` is killed and the frozen niltests descend
(`exists_frozen_descent_models`). -/
theorem gradedFrequency_kills_top_of_flag (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (η : L →ₗ[ℚ] ℚ)
    {W K : LieSubalgebra ℚ F.AssociatedGraded}
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (hη : ∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF η x = 0)
    (hK : K.toSubmodule = W.toSubmodule ⊔ commutatorSubmodule F.AssociatedGraded)
    (hflag : ∀ x y : F.AssociatedGraded,
      basisGradeProjection (F.associatedGradedBasis b ω hF) ω 1 x = x →
      basisGradeProjection (F.associatedGradedBasis b ω hF) ω 1 y = y →
      F.gradedFrequency b ω hF η ⁅x, y⁆ = 0) :
    ∀ x ∈ K, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF η x = 0 := by
  have hB := step2Graded_associatedGraded F b ω hF hs2
  have hcomm : ∀ c ∈ commutatorSubmodule F.AssociatedGraded, F.gradedFrequency b ω hF η c = 0 := by
    have hle : commutatorSubmodule F.AssociatedGraded ≤
        LinearMap.ker (F.gradedFrequency b ω hF η) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, y, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, lie_eq_lie_gradeProjection_one hB x y]
      exact hflag _ _ (gradeProjection_idem _ ω 1 x) (gradeProjection_idem _ ω 1 y)
    exact fun c hc => hle hc
  intro x hx hxs
  have hx' : x ∈ K.toSubmodule := hx
  rw [hK] at hx'
  obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp hx'
  have hc1 := gradeProjection_one_of_mem_commutator hB hc
  have hcη := hcomm c hc
  rw [map_add, hcη, add_zero]
  have hωs := F.adaptedBasis_weight_le_step b ω hF
  rcases Nat.lt_or_ge s 2 with hlt | hge
  · obtain rfl : s = 1 := by omega
    have hall : ∀ z, basisGradeProjection (F.associatedGradedBasis b ω hF) ω 1 z = z := by
      intro z
      apply (F.associatedGradedBasis b ω hF).repr.injective
      ext i
      rw [basisGradeProjection_repr, ite_eq_left (by have := hωs i; have := hB.weight i; omega)]
    have hc0 : c = 0 := by rw [← hall c, hc1]
    rw [hc0, add_zero] at hxs
    exact hη w hw hxs
  · obtain rfl : s = 2 := by omega
    have hc2 : basisGradeProjection (F.associatedGradedBasis b ω hF) ω 2 c = c := by
      apply (F.associatedGradedBasis b ω hF).repr.injective
      ext i
      rw [basisGradeProjection_repr]
      by_cases h2 : ω i = 2
      · rw [ite_eq_left h2]
      · have h1 : ω i = 1 := by have := hB.weight i; omega
        rw [ite_eq_right h2]
        have := congrArg (fun v => (F.associatedGradedBasis b ω hF).repr v i) hc1
        simp only [basisGradeProjection_repr, ite_eq_left h1, map_zero, Finsupp.zero_apply] at this
        exact this.symm
    rw [map_add, hc2] at hxs
    exact hη w hw (add_right_cancel hxs)

/-- **Flag-or-dimension (the potential of the iteration).** For `K = W + [gr, gr]` with `W`
basis-graded and `η` killing the top layer of `W`: either the sub-model
`gradedRefiltrationSubalgebra K` has strictly smaller dimension, or the flag holds (`η ⁅x, y⁆ = 0`
for all weight-one `x, y`). -/
theorem finrank_lt_or_flag [Module.Finite ℚ L] (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (η : L →ₗ[ℚ] ℚ)
    {W K : LieSubalgebra ℚ F.AssociatedGraded}
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (hη : ∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF η x = 0)
    (hK : K.toSubmodule = W.toSubmodule ⊔ commutatorSubmodule F.AssociatedGraded) :
    finrank ℚ (F.gradedRefiltrationSubalgebra K) < finrank ℚ L ∨
      ∀ x y : F.AssociatedGraded,
        basisGradeProjection (F.associatedGradedBasis b ω hF) ω 1 x = x →
        basisGradeProjection (F.associatedGradedBasis b ω hF) ω 1 y = y →
        F.gradedFrequency b ω hF η ⁅x, y⁆ = 0 := by
  by_cases hall : ∀ x, basisGradeProjection (F.associatedGradedBasis b ω hF) ω 1 x = x → x ∈ K
  · exact Or.inr fun x y hx hy =>
      gradedFrequency_lie_eq_zero F b ω hF hs1 hs2 η hW hη hK (hall x hx) (hall y hy) hx hy
  · push Not at hall
    exact Or.inl (finrank_gradedRefiltrationSubalgebra_lt F b ω hF K hall)

end Flag

end PrimeCarleson.Proof.Fplus31

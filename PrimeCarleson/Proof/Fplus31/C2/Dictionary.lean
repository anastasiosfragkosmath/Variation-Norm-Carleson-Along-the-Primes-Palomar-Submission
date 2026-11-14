module

public import PrimeCarleson.Proof.Fplus31.Extrapolation.Main
public import OAI.Combinatorics.Progressions.Estimates.RealifiedMultidegree
public import OAI.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis
public import OAI.Combinatorics.Progressions.Nilpotent.FilteredAdjointFirstBracket

/-!
# The extrapolation step on the library's types: the dictionary

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). The
abstract extrapolation of `Extrapolation/Main.lean` is over the graded step-two Lie algebra
`(g₁, g₂, β)` of `Extrapolation/Model.lean`, its group `SymbolGroup a` and the graded subalgebras
`GradedSubalg a`. This file identifies those objects with the real BCH group and the basis-graded
Lie subalgebras of a `ℚ`-Lie algebra `V` with a basis `B` of weights `ω ∈ {1, 2}` whose brackets
respect the weights (`Step2Graded B ω`; the vendored library's `F.AssociatedGraded` with
`F.associatedGradedBasis` is one, see `C2/Symbol.lean`). Nothing here mentions the vendored
library's niltest or symbol types.

* `stepTwoAlgebra B ω`: the structure constants `c i j k = B.repr ⁅B i, B j⁆ k` for
  `i, j ∈ ι₁ = {ω = 1}` and `k ∈ ι₂ = {ω = 2}`;
* `lieBCH_eq_quadratic_of_step_le_two`: `lieBCH s a b = a + b + ½ ⁅a, b⁆` for `s ∈ {1, 2}`;
* `groupEquiv`: the isomorphism `SymbolGroup (stepTwoAlgebra B ω) ≃* NilpotentLieBCHGroup (ℝ ⊗ V) s`
  (coordinates `ι = ι₁ ⊕ ι₂`), with the dilation compatibility `repr_groupEquiv_dil`;
* `phi`, `phiR`: the coordinate isomorphisms `V ≃ g₁ × g₂` and `ℝ ⊗ V ≃ g₁ × g₂` (over `ℝ`);
* `toGraded`, `ofGraded`: basis-graded Lie subalgebras of `V` and `GradedSubalg`s correspond;
  `mem_ofGraded_plusDerived` identifies `W + D` with `W + [V, V]`;
* `mem_baseChange_iff`: the real span `realSpan` of the datum is `S ⊗ ℝ`;
* `gen_iff`: the generation clause (`≤ d` vectors of height `≤ p`).
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

section Coord

variable {K M ι : Type*} [Field K] [LieRing M] [LieAlgebra K M] [Fintype ι]

/-- The coordinates of a bracket in terms of the structure constants of a basis. -/
theorem repr_lie_eq_sum (e : Module.Basis ι K M) (x y : M) (k : ι) :
    e.repr ⁅x, y⁆ k = ∑ i, ∑ j, e.repr x i * e.repr y j * e.repr ⁅e i, e j⁆ k := by
  conv_lhs => rw [← e.sum_repr x, ← e.sum_repr y]
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Coord

/-- For a Lie algebra with `lowerCentralSeries s = ⊥`, `s ∈ {1, 2}`, the BCH product of step `s` is
`a + b + ½ ⁅a, b⁆`. -/
theorem lieBCH_eq_quadratic_of_step_le_two {M : Type*} [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (hnil : LieModule.lowerCentralSeries ℚ M M s = ⊥) (a b : M) :
    lieBCH s a b = a + b + (1 / 2 : ℚ) • ⁅a, b⁆ := by
  rcases Nat.lt_or_ge s 2 with h | h
  · obtain rfl : s = 1 := by omega
    have hab : ⁅a, b⁆ = 0 := by
      have hmem : ⁅a, b⁆ ∈ LieModule.lowerCentralSeries ℚ M M 1 := by
        rw [LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_zero]
        exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _)
      rw [hnil] at hmem
      simpa using hmem
    rw [lieBCH_eq_add_of_lie_eq_zero hnil hab, hab]
    simp
  · obtain rfl : s = 2 := by omega
    exact lieBCH_eq_quadratic_of_step_two le_rfl hnil a b

section Idx

variable {ι : Type*}

/-- Layer-one index set. -/
abbrev Idx1 (ω : ι → ℕ) := {i : ι // ω i = 1}

/-- Layer-two index set. -/
abbrev Idx2 (ω : ι → ℕ) := {i : ι // ω i = 2}

/-- A sum over `ι` of a function supported on the weight-one indices is a sum over `Idx1 ω`. -/
theorem sum_idx1 [Fintype ι] (ω : ι → ℕ) {R : Type*} [AddCommMonoid R] (f : ι → R)
    (hf : ∀ i, ω i ≠ 1 → f i = 0) : ∑ i, f i = ∑ i : Idx1 ω, f i.1 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun i => ω i = 1)) (by simp) f,
    Finset.sum_filter_of_ne]
  intro i _ hi
  by_contra h
  exact hi (hf i h)

end Idx

section Weighted

variable {K M ι : Type*} [Field K] [LieRing M] [LieAlgebra K M] [Fintype ι]
  (e : Module.Basis ι K M) (ω : ι → ℕ)

omit [Fintype ι] in
/-- The weight-one coordinates of a bracket vanish (weights `1` or `2`, brackets add weights). -/
theorem repr_lie_eq_zero_of_weight [Finite ι] (hw : ∀ i, ω i = 1 ∨ ω i = 2)
    (hbr : ∀ i j k, e.repr ⁅e i, e j⁆ k ≠ 0 → ω i + ω j = ω k) (x y : M) {k : ι}
    (hk : ω k = 1) : e.repr ⁅x, y⁆ k = 0 := by
  have := Fintype.ofFinite ι
  rw [repr_lie_eq_sum]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  have : e.repr ⁅e a, e b⁆ k = 0 := by
    by_contra h
    have h1 := hbr a b k h
    rcases hw a with h2 | h2 <;> rcases hw b with h3 | h3 <;> omega
  rw [this, mul_zero]

/-- The weight-two coordinates of a bracket only see the weight-one coordinates. -/
theorem repr_lie_eq_sum_idx (hw : ∀ i, ω i = 1 ∨ ω i = 2)
    (hbr : ∀ i j k, e.repr ⁅e i, e j⁆ k ≠ 0 → ω i + ω j = ω k) (x y : M) {k : ι}
    (hk : ω k = 2) :
    e.repr ⁅x, y⁆ k =
      ∑ i : Idx1 ω, ∑ j : Idx1 ω, e.repr x i.1 * e.repr y j.1 * e.repr ⁅e i.1, e j.1⁆ k := by
  rw [repr_lie_eq_sum]
  have hz : ∀ a b, (ω a ≠ 1 ∨ ω b ≠ 1) → e.repr ⁅e a, e b⁆ k = 0 := by
    intro a b hab
    by_contra h
    have h1 := hbr a b k h
    rcases hw a with h2 | h2 <;> rcases hw b with h3 | h3 <;> omega
  rw [sum_idx1 ω]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_idx1 ω]
    intro b hb
    rw [hz a.1 b (Or.inr hb), mul_zero]
  · intro a ha
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [hz a b (Or.inl ha), mul_zero]

end Weighted


section Dict

variable {V : Type*} [LieRing V] [LieAlgebra ℚ V] {ι : Type*} [Fintype ι]
  (B : Module.Basis ι ℚ V) (ω : ι → ℕ)

/-- A basis of a Lie algebra with weights `1` and `2` whose brackets respect the weights. -/
structure Step2Graded : Prop where
  weight : ∀ i, ω i = 1 ∨ ω i = 2
  bracket : ∀ i j k, B.repr ⁅B i, B j⁆ k ≠ 0 → ω i + ω j = ω k

/-- The structure constants of the graded step-two Lie algebra. -/
def stepTwoAlgebra : Step2Algebra (Idx1 ω) (Idx2 ω) where
  c i j k := B.repr ⁅B i.1, B j.1⁆ k.1
  c_neg i j k := by
    have h : ⁅B j.1, B i.1⁆ = -⁅B i.1, B j.1⁆ := neg_eq_iff_eq_neg.mp (lie_skew _ _)
    change B.repr ⁅B j.1, B i.1⁆ k.1 = -B.repr ⁅B i.1, B j.1⁆ k.1
    rw [h, map_neg, Finsupp.neg_apply]

/-- The real coordinates of an element of the symbol group. -/
def realCoords (x : SymbolGroup (stepTwoAlgebra B ω)) : ι → ℝ :=
  fun i => if h : ω i = 1 then x.fst ⟨i, h⟩ else if h : ω i = 2 then x.snd ⟨i, h⟩ else 0

/-- The element of `ℝ ⊗ V` with the coordinates of `x`. -/
def realElt (x : SymbolGroup (stepTwoAlgebra B ω)) : ℝ ⊗[ℚ] V :=
  (B.baseChange ℝ).equivFun.symm (realCoords B ω x)

/-- The coordinates of an element of `ℝ ⊗ V` as an element of the symbol group. -/
def symbolOf (X : ℝ ⊗[ℚ] V) : SymbolGroup (stepTwoAlgebra B ω) :=
  ⟨fun i => (B.baseChange ℝ).repr X i.1, fun k => (B.baseChange ℝ).repr X k.1⟩

/-- The coordinates of `realElt x` are `realCoords x`. -/
theorem repr_realElt (x : SymbolGroup (stepTwoAlgebra B ω)) (i : ι) :
    (B.baseChange ℝ).repr (realElt B ω x) i = realCoords B ω x i := by
  rw [realElt, Module.Basis.equivFun_symm_apply, Module.Basis.repr_sum_self]

/-- The weight-one coordinates of `realElt x` are those of `x₁`. -/
theorem repr_realElt_fst (x : SymbolGroup (stepTwoAlgebra B ω)) (i : Idx1 ω) :
    (B.baseChange ℝ).repr (realElt B ω x) i.1 = x.fst i := by
  rw [repr_realElt, realCoords, dite_eq_left i.2]

/-- The weight-two coordinates of `realElt x` are those of `x₂`. -/
theorem repr_realElt_snd (x : SymbolGroup (stepTwoAlgebra B ω)) (k : Idx2 ω) :
    (B.baseChange ℝ).repr (realElt B ω x) k.1 = x.snd k := by
  have h1 : ¬ ω k.1 = 1 := by have := k.2; omega
  rw [repr_realElt, realCoords, dite_eq_right h1, dite_eq_left k.2]

/-- `symbolOf` is a left inverse of `realElt`. -/
theorem symbolOf_realElt (x : SymbolGroup (stepTwoAlgebra B ω)) :
    symbolOf B ω (realElt B ω x) = x := by
  ext1
  · funext i
    simp only [symbolOf, repr_realElt, realCoords, dite_eq_left i.2]
  · funext k
    have h1 : ¬ ω k.1 = 1 := by have := k.2; omega
    simp only [symbolOf, repr_realElt, realCoords, dite_eq_right h1, dite_eq_left k.2]

variable {B ω}

/-- `realElt` is a left inverse of `symbolOf`. -/
theorem realElt_symbolOf (hB : Step2Graded B ω) (X : ℝ ⊗[ℚ] V) :
    realElt B ω (symbolOf B ω X) = X := by
  apply (B.baseChange ℝ).repr.injective
  ext i
  rw [repr_realElt]
  rcases hB.weight i with h | h
  · simp only [realCoords, dite_eq_left h, symbolOf]
  · have h1 : ¬ ω i = 1 := by omega
    simp only [realCoords, dite_eq_right h1, dite_eq_left h, symbolOf]

omit [Fintype ι] in
/-- The real extension of a weight-respecting basis respects the weights. -/
theorem bracket_real (hB : Step2Graded B ω) :
    ∀ i j k, (B.baseChange ℝ).repr ⁅(B.baseChange ℝ) i, (B.baseChange ℝ) j⁆ k ≠ 0 →
      ω i + ω j = ω k := by
  intro i j k h
  rw [realLieBasis_structure] at h
  exact hB.bracket i j k (fun h0 => h (by simp [lieStructureConstants, h0]))

omit [Fintype ι] in
/-- The weight-one coordinates of a real bracket vanish. -/
theorem repr_lie_real_fst [Finite ι] (hB : Step2Graded B ω) (X Y : ℝ ⊗[ℚ] V) (i : Idx1 ω) :
    (B.baseChange ℝ).repr ⁅X, Y⁆ i.1 = 0 :=
  repr_lie_eq_zero_of_weight (B.baseChange ℝ) ω hB.weight (bracket_real hB) X Y i.2

/-- The weight-two coordinates of a real bracket are `β` of the weight-one coordinates. -/
theorem repr_lie_real_snd (hB : Step2Graded B ω) (X Y : ℝ ⊗[ℚ] V) (k : Idx2 ω) :
    (B.baseChange ℝ).repr ⁅X, Y⁆ k.1 =
      (stepTwoAlgebra B ω).br (symbolOf B ω X).fst (symbolOf B ω Y).fst k := by
  rw [repr_lie_eq_sum_idx (B.baseChange ℝ) ω hB.weight (bracket_real hB) X Y k.2,
    Step2Algebra.br_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [realLieBasis_structure]
  rfl

omit [Fintype ι] in
/-- The coordinates of a rational multiple. -/
theorem repr_rat_smul (Z : ℝ ⊗[ℚ] V) (q : ℚ) (i : ι) :
    (B.baseChange ℝ).repr (q • Z) i = (q : ℝ) * (B.baseChange ℝ).repr Z i := by
  rw [map_rat_smul, Finsupp.smul_apply, Rat.smul_def]

/-- `symbolOf` turns the BCH product of step `s ∈ {1, 2}` into the product of the symbol group. -/
theorem symbolOf_lieBCH (hB : Step2Graded B ω) {s : ℕ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2)
    (hnil : LieModule.lowerCentralSeries ℚ (ℝ ⊗[ℚ] V) (ℝ ⊗[ℚ] V) s = ⊥) (X Y : ℝ ⊗[ℚ] V) :
    symbolOf B ω (lieBCH s X Y) = symbolOf B ω X * symbolOf B ω Y := by
  rw [lieBCH_eq_quadratic_of_step_le_two hs1 hs2 hnil]
  ext1
  · funext i
    simp only [symbolOf, SymbolGroup.mul_fst, Pi.add_apply, map_add, Finsupp.add_apply,
      repr_rat_smul, repr_lie_real_fst hB, mul_zero, add_zero]
  · funext k
    simp only [symbolOf, SymbolGroup.mul_snd, Pi.add_apply, map_add, Finsupp.add_apply,
      repr_rat_smul, repr_lie_real_snd hB, Pi.smul_apply, smul_eq_mul]
    push_cast
    rfl

/-- **The isomorphism of the symbol group of the graded step-two Lie algebra with the BCH group
of `ℝ ⊗ V`.** -/
def groupEquiv (hB : Step2Graded B ω) {s : ℕ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2)
    (hV : LieModule.lowerCentralSeries ℚ V V s = ⊥) :
    SymbolGroup (stepTwoAlgebra B ω) ≃*
      NilpotentLieBCHGroup (ℝ ⊗[ℚ] V) s (realification_lowerCentralSeries_eq_bot hV) where
  toFun x := ⟨realElt B ω x⟩
  invFun g := symbolOf B ω g.coord
  left_inv x := symbolOf_realElt B ω x
  right_inv g := NilpotentLieBCHGroup.ext (realElt_symbolOf hB g.coord)
  map_mul' x y := by
    apply NilpotentLieBCHGroup.ext
    change realElt B ω (x * y) = lieBCH s (realElt B ω x) (realElt B ω y)
    have h := symbolOf_lieBCH hB hs1 hs2 (realification_lowerCentralSeries_eq_bot hV)
      (realElt B ω x) (realElt B ω y)
    rw [symbolOf_realElt, symbolOf_realElt] at h
    rw [← h, realElt_symbolOf hB]

end Dict

section Phi

variable {V : Type*} [LieRing V] [LieAlgebra ℚ V] {ι : Type*} [Fintype ι]
  {B : Module.Basis ι ℚ V} {ω : ι → ℕ}

/-- The index equivalence `ι₁ ⊕ ι₂ ≃ ι`. -/
def splitIndexEquiv (hB : Step2Graded B ω) : Idx1 ω ⊕ Idx2 ω ≃ ι :=
  Equiv.ofBijective (Sum.elim Subtype.val Subtype.val) (by
    refine ⟨?_, fun i => ?_⟩
    · rintro (a | a) (b | b) h
      · exact congrArg Sum.inl (Subtype.ext h)
      · have h1 := a.2
        have h2 := b.2
        change a.1 = b.1 at h
        rw [h] at h1
        omega
      · have h1 := a.2
        have h2 := b.2
        change a.1 = b.1 at h
        rw [h] at h1
        omega
      · exact congrArg Sum.inr (Subtype.ext h)
    · rcases hB.weight i with h | h
      · exact ⟨Sum.inl ⟨i, h⟩, rfl⟩
      · exact ⟨Sum.inr ⟨i, h⟩, rfl⟩)

/-- `|ι| = |ι₁| + |ι₂|`. -/
theorem card_split (hB : Step2Graded B ω) :
    Fintype.card ι = Fintype.card (Idx1 ω) + Fintype.card (Idx2 ω) := by
  rw [← Fintype.card_sum]
  exact (Fintype.card_congr (splitIndexEquiv hB)).symm

/-- The coordinate isomorphism `V ≃ g₁ × g₂`. -/
def phi (hB : Step2Graded B ω) : V ≃ₗ[ℚ] (Idx1 ω → ℚ) × (Idx2 ω → ℚ) :=
  B.equivFun.trans ((LinearEquiv.funCongrLeft ℚ ℚ (splitIndexEquiv hB)).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ ℚ ℚ))

/-- The coordinates of `phi`. -/
theorem phi_apply (hB : Step2Graded B ω) (x : V) :
    phi hB x = (fun i => B.repr x i.1, fun k => B.repr x k.1) := rfl

/-- `phi` turns the bracket of `V` into `β`: `phi ⁅x, y⁆ = (0, β x₁ y₁)`. -/
theorem phi_lie (hB : Step2Graded B ω) (x y : V) :
    phi hB ⁅x, y⁆ = (0, (stepTwoAlgebra B ω).br (phi hB x).1 (phi hB y).1) := by
  refine Prod.ext (funext fun i => ?_) (funext fun k => ?_)
  · exact repr_lie_eq_zero_of_weight B ω hB.weight hB.bracket x y i.2
  · change B.repr ⁅x, y⁆ k.1 = (stepTwoAlgebra B ω).br (phi hB x).1 (phi hB y).1 k
    rw [repr_lie_eq_sum_idx B ω hB.weight hB.bracket x y k.2, Step2Algebra.br_apply]
    rfl

/-- The weight-one projection in the coordinates of `phi`. -/
theorem phi_gradeProjection_one (hB : Step2Graded B ω) (x : V) :
    phi hB (basisGradeProjection B ω 1 x) = ((phi hB x).1, 0) := by
  refine Prod.ext (funext fun i => ?_) (funext fun k => ?_)
  · change B.repr (basisGradeProjection B ω 1 x) i.1 = B.repr x i.1
    rw [basisGradeProjection_repr, ite_eq_left i.2]
  · change B.repr (basisGradeProjection B ω 1 x) k.1 = 0
    have : ¬ ω k.1 = 1 := by have := k.2; omega
    rw [basisGradeProjection_repr, ite_eq_right this]

/-- The weight-two projection in the coordinates of `phi`. -/
theorem phi_gradeProjection_two (hB : Step2Graded B ω) (x : V) :
    phi hB (basisGradeProjection B ω 2 x) = (0, (phi hB x).2) := by
  refine Prod.ext (funext fun i => ?_) (funext fun k => ?_)
  · change B.repr (basisGradeProjection B ω 2 x) i.1 = 0
    have : ¬ ω i.1 = 2 := by have := i.2; omega
    rw [basisGradeProjection_repr, ite_eq_right this]
  · change B.repr (basisGradeProjection B ω 2 x) k.1 = B.repr x k.1
    rw [basisGradeProjection_repr, ite_eq_left k.2]

/-- The other weight projections vanish. -/
theorem phi_gradeProjection_other (hB : Step2Graded B ω) {j : ℕ} (h1 : j ≠ 1) (h2 : j ≠ 2)
    (x : V) : phi hB (basisGradeProjection B ω j x) = 0 := by
  refine Prod.ext (funext fun i => ?_) (funext fun k => ?_)
  · change B.repr (basisGradeProjection B ω j x) i.1 = 0
    have : ¬ ω i.1 = j := by have := i.2; omega
    rw [basisGradeProjection_repr, ite_eq_right this]
  · change B.repr (basisGradeProjection B ω j x) k.1 = 0
    have : ¬ ω k.1 = j := by have := k.2; omega
    rw [basisGradeProjection_repr, ite_eq_right this]

/-- The graded subalgebra of `g` corresponding to a basis-graded Lie subalgebra of `V`. -/
def toGraded (hB : Step2Graded B ω) (W : LieSubalgebra ℚ V)
    (hW : BasisGradedSubmodule B ω W.toSubmodule) : GradedSubalg (stepTwoAlgebra B ω) where
  toSubmodule := W.toSubmodule.comap (phi hB).symm.toLinearMap
  fst_mem w hw := by
    have h : (phi hB).symm (w.1, 0) = basisGradeProjection B ω 1 ((phi hB).symm w) := by
      apply (phi hB).injective
      simp only [phi_gradeProjection_one, LinearEquiv.apply_symm_apply]
    change (phi hB).symm (w.1, 0) ∈ W.toSubmodule
    rw [h]
    exact hW 1 _ hw
  snd_mem w hw := by
    have h : (phi hB).symm (0, w.2) = basisGradeProjection B ω 2 ((phi hB).symm w) := by
      apply (phi hB).injective
      simp only [phi_gradeProjection_two, LinearEquiv.apply_symm_apply]
    change (phi hB).symm (0, w.2) ∈ W.toSubmodule
    rw [h]
    exact hW 2 _ hw
  bracket_mem x hx y hy := by
    have h : (phi hB).symm (0, (stepTwoAlgebra B ω).br x.1 y.1) =
        ⁅(phi hB).symm x, (phi hB).symm y⁆ := by
      apply (phi hB).injective
      simp only [phi_lie, LinearEquiv.apply_symm_apply]
    change (phi hB).symm (0, (stepTwoAlgebra B ω).br x.1 y.1) ∈ W.toSubmodule
    rw [h]
    exact W.lie_mem hx hy

/-- The basis-graded Lie subalgebra of `V` corresponding to a graded subalgebra of `g`. -/
def ofGraded (hB : Step2Graded B ω) (U : GradedSubalg (stepTwoAlgebra B ω)) :
    LieSubalgebra ℚ V :=
  { U.toSubmodule.comap (phi hB).toLinearMap with
    lie_mem' := fun {x y} hx hy => by
      change phi hB ⁅x, y⁆ ∈ U.toSubmodule
      rw [phi_lie]
      exact U.bracket_mem _ hx _ hy }

/-- Membership in `ofGraded`. -/
theorem mem_ofGraded (hB : Step2Graded B ω) (U : GradedSubalg (stepTwoAlgebra B ω)) (x : V) :
    x ∈ ofGraded hB U ↔ phi hB x ∈ U.toSubmodule := Iff.rfl

/-- `ofGraded U` is basis-graded. -/
theorem basisGraded_ofGraded (hB : Step2Graded B ω) (U : GradedSubalg (stepTwoAlgebra B ω)) :
    BasisGradedSubmodule B ω (ofGraded hB U).toSubmodule := by
  intro j x hx
  change phi hB x ∈ U.toSubmodule at hx
  change phi hB (basisGradeProjection B ω j x) ∈ U.toSubmodule
  by_cases h1 : j = 1
  · subst h1
    rw [phi_gradeProjection_one]
    exact U.fst_mem _ hx
  by_cases h2 : j = 2
  · subst h2
    rw [phi_gradeProjection_two]
    exact U.snd_mem _ hx
  rw [phi_gradeProjection_other hB h1 h2]
  exact U.toSubmodule.zero_mem

/-- The span of the brackets of `V`, the derived algebra `[V, V]`. -/
def commutatorSubmodule (V : Type*) [LieRing V] [LieAlgebra ℚ V] : Submodule ℚ V :=
  Submodule.span ℚ {z | ∃ x y : V, z = ⁅x, y⁆}

/-- A bracket lies in the commutator submodule. -/
theorem lie_mem_commutator (x y : V) : ⁅x, y⁆ ∈ commutatorSubmodule V :=
  Submodule.subset_span ⟨x, y, rfl⟩

/-- The elements of `D = β(g₁, g₁)` correspond to elements of `[V, V]`. -/
theorem symm_zero_mem_commutator (hB : Step2Graded B ω) {d : Idx2 ω → ℚ}
    (hd : d ∈ derived (stepTwoAlgebra B ω)) : (phi hB).symm (0, d) ∈ commutatorSubmodule V := by
  have hle : derived (stepTwoAlgebra B ω) ≤
      (commutatorSubmodule V).comap
        ((phi hB).symm.toLinearMap.comp (LinearMap.inr ℚ (Idx1 ω → ℚ) (Idx2 ω → ℚ))) := by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨x, y, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    change (phi hB).symm (0, (stepTwoAlgebra B ω).br x y) ∈ commutatorSubmodule V
    have : (phi hB).symm (0, (stepTwoAlgebra B ω).br x y) =
        ⁅(phi hB).symm (x, 0), (phi hB).symm (y, 0)⁆ := by
      apply (phi hB).injective
      simp only [phi_lie, LinearEquiv.apply_symm_apply]
    rw [this]
    exact lie_mem_commutator _ _
  exact hle hd

/-- Conversely `[V, V]` corresponds to `D`. -/
theorem commutator_le_comap (hB : Step2Graded B ω) :
    commutatorSubmodule V ≤
      (Submodule.prod ⊥ (derived (stepTwoAlgebra B ω))).comap (phi hB).toLinearMap := by
  refine Submodule.span_le.mpr ?_
  rintro z ⟨x, y, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  change phi hB ⁅x, y⁆ ∈ Submodule.prod ⊥ (derived (stepTwoAlgebra B ω))
  rw [phi_lie]
  exact Submodule.mem_prod.mpr ⟨Submodule.zero_mem _, br_mem_derived _ _⟩

/-- `W + [V, V]` is the Lie subalgebra of `V` that corresponds to `W + D` of the abstract model. -/
theorem mem_ofGraded_plusDerived (hB : Step2Graded B ω) (W : LieSubalgebra ℚ V)
    (hW : BasisGradedSubmodule B ω W.toSubmodule) (z : V) :
    z ∈ ofGraded hB (toGraded hB W hW).plusDerived ↔
      z ∈ W.toSubmodule ⊔ commutatorSubmodule V := by
  rw [mem_ofGraded]
  constructor
  · intro h
    change phi hB z ∈ (toGraded hB W hW).toSubmodule ⊔
      Submodule.prod ⊥ (derived (stepTwoAlgebra B ω)) at h
    obtain ⟨y, hy, d, hd, hyd⟩ := Submodule.mem_sup.mp h
    have hz : z = (phi hB).symm y + (phi hB).symm d := by
      rw [← map_add, hyd, LinearEquiv.symm_apply_apply]
    rw [hz]
    refine Submodule.add_mem_sup hy ?_
    obtain ⟨hd1, hd2⟩ := Submodule.mem_prod.mp hd
    have hd0 : d = (0, d.2) := Prod.ext (by simpa using hd1) rfl
    rw [hd0]
    exact symm_zero_mem_commutator hB hd2
  · intro h
    obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp h
    rw [map_add]
    refine Submodule.add_mem_sup ?_ (commutator_le_comap hB hc)
    change (phi hB).symm (phi hB w) ∈ W.toSubmodule
    rwa [LinearEquiv.symm_apply_apply]

omit [Fintype ι] in
/-- The derived algebra has no component of weight one. -/
theorem gradeProjection_one_of_mem_commutator [Finite ι] (hB : Step2Graded B ω) {z : V}
    (hz : z ∈ commutatorSubmodule V) : basisGradeProjection B ω 1 z = 0 := by
  have hle : commutatorSubmodule V ≤ LinearMap.ker (basisGradeProjection B ω 1) := by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨x, y, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    apply B.repr.injective
    ext i
    rw [basisGradeProjection_repr]
    by_cases h : ω i = 1
    · rw [ite_eq_left h, map_zero, Finsupp.zero_apply]
      exact repr_lie_eq_zero_of_weight B ω hB.weight hB.bracket x y h
    · rw [ite_eq_right h, map_zero, Finsupp.zero_apply]
  exact hle hz

end Phi

section Real

variable {V : Type*} [LieRing V] [LieAlgebra ℚ V] {ι : Type*} [Fintype ι]
  {B : Module.Basis ι ℚ V} {ω : ι → ℕ}

/-- The real coordinate isomorphism `ℝ ⊗ V ≃ g₁ ⊗ ℝ × g₂ ⊗ ℝ`. -/
def phiR (hB : Step2Graded B ω) : (ℝ ⊗[ℚ] V) ≃ₗ[ℝ] (Idx1 ω → ℝ) × (Idx2 ω → ℝ) :=
  (B.baseChange ℝ).equivFun.trans ((LinearEquiv.funCongrLeft ℝ ℝ (splitIndexEquiv hB)).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ))

/-- The coordinates of `phiR`. -/
theorem phiR_apply (hB : Step2Graded B ω) (X : ℝ ⊗[ℚ] V) :
    phiR hB X = ((symbolOf B ω X).fst, (symbolOf B ω X).snd) := rfl

/-- `phiR` extends `phi`: the coordinates of `1 ⊗ w` are those of `w`. -/
theorem phiR_tmul (hB : Step2Graded B ω) (w : V) :
    phiR hB ((1 : ℝ) ⊗ₜ[ℚ] w) = realCast (phi hB w) := by
  refine Prod.ext (funext fun i => ?_) (funext fun k => ?_)
  · simp [phiR_apply, symbolOf, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, realCast,
      phi_apply]
  · simp [phiR_apply, symbolOf, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, realCast,
      phi_apply]

/-- `S ⊗ ℝ` and `realSpan` correspond under `phiR`. -/
theorem phiR_baseChange (hB : Step2Graded B ω) (S : Submodule ℚ V) :
    (S.baseChange ℝ).map (phiR hB).toLinearMap = realSpan (S.comap (phi hB).symm.toLinearMap) := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span, realSpan]
  congr 1
  ext Y
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨phi hB w, ?_, ?_⟩
    · change (phi hB).symm (phi hB w) ∈ S
      rwa [LinearEquiv.symm_apply_apply]
    · exact (phiR_tmul hB w).symm
  · rintro ⟨t, ht, rfl⟩
    refine ⟨_, ⟨(phi hB).symm t, ht, rfl⟩, ?_⟩
    change phiR hB ((1 : ℝ) ⊗ₜ[ℚ] (phi hB).symm t) = realCast t
    rw [phiR_tmul, LinearEquiv.apply_symm_apply]

/-- A real vector lies in the real span `S_ℝ` of a rational subspace iff its coordinates lie in
the real span of the corresponding subspace of `g`. -/
theorem mem_baseChange_iff (hB : Step2Graded B ω) (S : Submodule ℚ V) (Y : ℝ ⊗[ℚ] V) :
    Y ∈ S.baseChange ℝ ↔
      ((symbolOf B ω Y).fst, (symbolOf B ω Y).snd) ∈
        realSpan (S.comap (phi hB).symm.toLinearMap) := by
  rw [← phiR_baseChange hB, ← phiR_apply hB, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

end Real

section Gen

variable {V : Type*} [LieRing V] [LieAlgebra ℚ V] {ι : Type*} [Fintype ι]
  {B : Module.Basis ι ℚ V} {ω : ι → ℕ}

/-- The generation clause of the datum (`≤ d` vectors of height `≤ p`) corresponds to the generation
clause of the vendored library's `ControlledSymbolFactorization`. -/
theorem gen_iff (hB : Step2Graded B ω) (W : GradedSubalg (stepTwoAlgebra B ω))
    (S : Submodule ℚ V) (hWS : W.toSubmodule = S.comap (phi hB).symm.toLinearMap) (p : ℝ) :
    W.Gen p ↔ ∃ v : ι → V, Submodule.span ℚ (Set.range v) = S ∧
      ∀ i j, ratLogHeight (B.repr (v i) j) ≤ p := by
  set e : Fin (Fintype.card (Idx1 ω) + Fintype.card (Idx2 ω)) ≃ ι :=
    (Fintype.equivFinOfCardEq (card_split hB)).symm with he
  have hWS' : W.toSubmodule = S.map (phi hB).toLinearMap := by
    rw [hWS, Submodule.comap_equiv_eq_map_symm, LinearEquiv.symm_symm]
  constructor
  · rintro ⟨v', hv', hh⟩
    refine ⟨fun i => (phi hB).symm (v' (e.symm i)), ?_, ?_⟩
    · have hr : Set.range (fun i => (phi hB).symm (v' (e.symm i))) =
          (phi hB).symm '' Set.range v' := by
        ext z
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨v' (e.symm i), ⟨e.symm i, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
          exact ⟨e r, by simp⟩
      have h1 : Submodule.span ℚ (Set.range (fun i => (phi hB).symm (v' (e.symm i)))) =
          (Submodule.span ℚ (Set.range v')).map (phi hB).symm.toLinearMap := by
        rw [hr, Submodule.map_span]
        rfl
      rw [h1, hv', hWS, Submodule.map_comap_eq_of_surjective]
      exact (phi hB).symm.surjective
    · intro i j
      rcases hB.weight j with h | h
      · have : B.repr ((phi hB).symm (v' (e.symm i))) j = (v' (e.symm i)).1 ⟨j, h⟩ := by
          have := congrArg (fun y => y.1 ⟨j, h⟩) ((phi hB).apply_symm_apply (v' (e.symm i)))
          exact this
        rw [this]
        exact (hh _).1 _
      · have : B.repr ((phi hB).symm (v' (e.symm i))) j = (v' (e.symm i)).2 ⟨j, h⟩ := by
          have := congrArg (fun y => y.2 ⟨j, h⟩) ((phi hB).apply_symm_apply (v' (e.symm i)))
          exact this
        rw [this]
        exact (hh _).2 _
  · rintro ⟨v, hv, hh⟩
    refine ⟨fun r => phi hB (v (e r)), ?_, fun r => ⟨fun i => hh _ _, fun k => hh _ _⟩⟩
    have hr : Set.range (fun r => phi hB (v (e r))) = (phi hB) '' Set.range v := by
      ext z
      constructor
      · rintro ⟨r, rfl⟩
        exact ⟨v (e r), ⟨e r, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨e.symm i, by simp⟩
    have hr2 : Submodule.span ℚ (Set.range (fun r => phi hB (v (e r)))) =
        (Submodule.span ℚ (Set.range v)).map (phi hB).toLinearMap := by
      rw [hr, Submodule.map_span]
      rfl
    rw [hr2, hv, hWS']

/-- `toGraded (ofGraded U) = U` at the level of submodules. -/
theorem toSubmodule_eq_comap_ofGraded (hB : Step2Graded B ω)
    (U : GradedSubalg (stepTwoAlgebra B ω)) :
    U.toSubmodule = (ofGraded hB U).toSubmodule.comap (phi hB).symm.toLinearMap := by
  ext z
  change z ∈ U.toSubmodule ↔ phi hB ((phi hB).symm z) ∈ U.toSubmodule
  rw [LinearEquiv.apply_symm_apply]

omit [Fintype ι] in
/-- A bracket lies in the top layer of a filtration of degree `s ∈ {1, 2}`. -/
theorem gradeProjection_lie_top [Finite ι] (hB : Step2Graded B ω) {s : ℕ} (hs1 : 1 ≤ s)
    (hs2 : s ≤ 2) (hωs : ∀ i, ω i ≤ s) (x y : V) :
    basisGradeProjection B ω s ⁅x, y⁆ = ⁅x, y⁆ := by
  apply B.repr.injective
  ext i
  rw [basisGradeProjection_repr]
  by_cases h : ω i = s
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    rcases hB.weight i with h1 | h1
    · exact (repr_lie_eq_zero_of_weight B ω hB.weight hB.bracket x y h1).symm
    · have := hωs i
      omega

omit [Fintype ι] in
/-- A statement about every index is a statement about both layers. -/
theorem forall_idx (hB : Step2Graded B ω) {P : ι → Prop} :
    (∀ i, P i) ↔ (∀ i : Idx1 ω, P i.1) ∧ (∀ k : Idx2 ω, P k.1) := by
  constructor
  · exact fun h => ⟨fun i => h _, fun k => h _⟩
  · rintro ⟨h1, h2⟩ i
    rcases hB.weight i with h | h
    · exact h1 ⟨i, h⟩
    · exact h2 ⟨i, h⟩

/-- The grading dilation `δ_r` of the symbol group acts on the coordinate of weight `ω i` by
`r ^ ω i`. -/
theorem repr_groupEquiv_dil (hB : Step2Graded B ω) {s : ℕ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2)
    (hV : LieModule.lowerCentralSeries ℚ V V s = ⊥) (r : ℝ)
    (x : SymbolGroup (stepTwoAlgebra B ω)) (i : ι) :
    (B.baseChange ℝ).repr (groupEquiv hB hs1 hs2 hV (SymbolGroup.dil r x)).coord i =
      r ^ ω i * (B.baseChange ℝ).repr (groupEquiv hB hs1 hs2 hV x).coord i := by
  change (B.baseChange ℝ).repr (realElt B ω (SymbolGroup.dil r x)) i =
    r ^ ω i * (B.baseChange ℝ).repr (realElt B ω x) i
  rw [repr_realElt, repr_realElt]
  rcases hB.weight i with h | h
  · rw [realCoords, realCoords, dite_eq_left h, dite_eq_left h, h, pow_one]
    simp
  · have h1 : ¬ ω i = 1 := by omega
    rw [realCoords, realCoords, dite_eq_right h1, dite_eq_right h1, dite_eq_left h,
      dite_eq_left h, h]
    simp

end Gen

end PrimeCarleson.Proof.Fplus31

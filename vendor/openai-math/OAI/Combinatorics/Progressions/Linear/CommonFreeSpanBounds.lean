/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/CommonFreeSpanBounds.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.CommonFreeSunflower
public import OAI.Combinatorics.Progressions.Nilpotent.FreeDegreeRankNilmanifold
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {X : Type*} [Fintype X] {s r : ℕ} {w : X → ℕ} {hw : ∀ x, 0 < w x}

structure FreeCoordinateFrame
    (b : Basis (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
      (FreeDegreeRankLieAlgebra X s r w hw)) (p : ℝ) where
  tree_height : ∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
    rationalLogHeight (b.repr (FreeDegreeRankLieAlgebra.projection X s r w hw x) i) ≤ p
  sourceBasis : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ
    (FreeNilpotentLieAlgebra X s)
  sourceBasis_trees : ∀ i, sourceBasis i ∈ FreeNilpotentLieAlgebra.treeGenerators X s
  sourceDimension : (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ p
  sectionMatrix : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s)))
    (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
  section_right_inverse : LinearMap.toMatrix sourceBasis b
    (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap * sectionMatrix = 1
  section_height : ∀ i j, rationalLogHeight (sectionMatrix i j) ≤ p

namespace FreeCoordinateFrame

variable {b : Basis (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
    (FreeDegreeRankLieAlgebra X s r w hw)} {p q : ℝ}

def mono (F : FreeCoordinateFrame b p) (hpq : p ≤ q) : FreeCoordinateFrame b q where
  tree_height x hx i := (F.tree_height x hx i).trans hpq
  sourceBasis := F.sourceBasis
  sourceBasis_trees := F.sourceBasis_trees
  sourceDimension := F.sourceDimension.trans hpq
  sectionMatrix := F.sectionMatrix
  section_right_inverse := F.section_right_inverse
  section_height i j := (F.section_height i j).trans hpq

end FreeCoordinateFrame
end Erdos3

end

section

namespace Erdos3

open Module

theorem FreeNilpotentLieAlgebra.of_mem_treeGenerators
    (X : Type*) [Fintype X] (s : ℕ) (hs : 1 ≤ s) (x : X) :
    FreeNilpotentLieAlgebra.of X s x ∈ FreeNilpotentLieAlgebra.treeGenerators X s := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨FreeMagma.of x, Finset.mem_filter.mpr ⟨?_, hs⟩, rfl⟩
  exact mem_finiteLieTrees_of_length_le X (FreeMagma.of x) hs

theorem FreeCoordinateFrame.generator_height
    {X : Type*} [Fintype X] {s r : ℕ} {w : X → ℕ} {hw : ∀ x, 0 < w x}
    {b : Basis (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
      (FreeDegreeRankLieAlgebra X s r w hw)} {p : ℝ}
    (F : FreeCoordinateFrame b p) (hs : 1 ≤ s) (x : X) (i) :
    rationalLogHeight (b.repr (FreeDegreeRankLieAlgebra.of X s r w hw x) i) ≤ p :=
  F.tree_height (FreeNilpotentLieAlgebra.of X s x)
    (FreeNilpotentLieAlgebra.of_mem_treeGenerators X s hs x) i

theorem exists_submodule_basis_of_spanning_logHeight
    {V ι κ : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι]
    (e : Basis ι ℚ V) (U : Submodule ℚ V) (v : κ → V)
    (hspan : Submodule.span ℚ (Set.range v) = U) {p : ℝ}
    (hv : ∀ a i, rationalLogHeight (e.repr (v a) i) ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ U)) ℚ U,
      ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ p := by
  classical
  let : FiniteDimensional ℚ V := e.finiteDimensional_of_finite
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range v)
  rw [hspan] at hex
  obtain ⟨z, hz, hzspan, hzli⟩ := hex
  refine ⟨(Basis.span hzli).map (LinearEquiv.ofEq _ _ hzspan), ?_⟩
  intro a i
  simp only [Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
  obtain ⟨k, hk⟩ := hz a
  rw [← hk]
  exact hv k i

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_petalComparisonSpace_basis_logHeight
    {V μ : Type*} [AddCommGroup V] [Module ℚ V] [Fintype μ]
    (e : Basis μ ℚ V) (C P K : Submodule ℚ V)
    (c : Basis (Fin (finrank ℚ C)) ℚ C) (p : Basis (Fin (finrank ℚ P)) ℚ P)
    (k : Basis (Fin (finrank ℚ K)) ℚ K) {q : ℝ} (hq : 0 ≤ q)
    (hc : ∀ a i, rationalLogHeight (e.repr (c a : V) i) ≤ q)
    (hp : ∀ a i, rationalLogHeight (e.repr (p a : V) i) ≤ q)
    (hk : ∀ a i, rationalLogHeight (e.repr (k a : V) i) ≤ q) :
    ∃ b : Basis (Fin (finrank ℚ (petalComparisonSpace C P K))) ℚ (petalComparisonSpace C P K),
      ∀ a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => e)).repr (b a : Fin 2 → V) i) ≤ q := by
  classical
  let Δ : V →ₗ[ℚ] (Fin 2 → V) := LinearMap.pi (fun _ => LinearMap.id)
  let S₀ : V →ₗ[ℚ] (Fin 2 → V) := LinearMap.single ℚ (fun _ : Fin 2 => V) 0
  let S₁ : V →ₗ[ℚ] (Fin 2 → V) := LinearMap.single ℚ (fun _ : Fin 2 => V) 1
  have hspace : petalComparisonSpace C P K =
      (C.map Δ ⊔ P.map S₀) ⊔ (K.map S₀ ⊔ K.map S₁) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, b, hb, u, hu, v, hv, h₀, h₁⟩ := petalComparisonSpace_decompose C P K x hx
      have hh : (Δ a + S₀ b) + (S₀ u + S₁ v) ∈
          (C.map Δ ⊔ P.map S₀) ⊔ (K.map S₀ ⊔ K.map S₁) :=
        Submodule.add_mem_sup (Submodule.add_mem_sup ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩)
          (Submodule.add_mem_sup ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩)
      convert hh using 1
      ext i
      fin_cases i <;> simp [Δ, S₀, S₁, LinearMap.single_apply, h₀, h₁]
    · apply sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
      · rintro x ⟨a, ha, rfl⟩
        apply (mem_petalComparisonSpace C P K _).mpr
        simpa [Δ] using And.intro (Submodule.mem_sup_left ha)
          ((P ⊔ K).zero_mem)
      · rintro x ⟨a, ha, rfl⟩
        apply (mem_petalComparisonSpace C P K _).mpr
        simpa [S₀, LinearMap.single_apply] using
          And.intro ((C ⊔ K).zero_mem) (Submodule.mem_sup_left ha)
      · rintro x ⟨a, ha, rfl⟩
        apply (mem_petalComparisonSpace C P K _).mpr
        simpa [S₀, LinearMap.single_apply] using
          And.intro ((C ⊔ K).zero_mem) (Submodule.mem_sup_right ha)
      · rintro x ⟨a, ha, rfl⟩
        apply (mem_petalComparisonSpace C P K _).mpr
        simpa [S₁, LinearMap.single_apply] using
          And.intro (Submodule.mem_sup_right ha) (Submodule.mem_sup_right (K.neg_mem ha))
  have hspan (U : Submodule ℚ V) (b : Basis (Fin (finrank ℚ U)) ℚ U) :
      Submodule.span ℚ (Set.range (fun j => (b j : V))) = U := by
    change Submodule.span ℚ (Set.range (U.subtype ∘ b)) = U
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hmap (U : Submodule ℚ V) (b : Basis (Fin (finrank ℚ U)) ℚ U)
      (φ : V →ₗ[ℚ] (Fin 2 → V)) :
      Submodule.span ℚ (Set.range (fun j => φ (b j : V))) = U.map φ := by
    change Submodule.span ℚ (Set.range (φ ∘ fun j => (b j : V))) = _
    rw [Set.range_comp, ← Submodule.map_span, hspan]
  let v := Sum.elim (Sum.elim (fun j => Δ (c j : V)) (fun j => S₀ (p j : V)))
    (Sum.elim (fun j => S₀ (k j : V)) (fun j => S₁ (k j : V)))
  have hv : Submodule.span ℚ (Set.range v) = petalComparisonSpace C P K := by
    dsimp only [v]
    rw [span_range_sumElim, span_range_sumElim, span_range_sumElim,
      hmap, hmap, hmap, hmap, hspace]
  have hsingle (j : Fin 2) (x : V) (hx : ∀ i, rationalLogHeight (e.repr x i) ≤ q)
      (i : Σ _ : Fin 2, μ) :
      rationalLogHeight ((Pi.basis (fun _ : Fin 2 => e)).repr
        (LinearMap.single ℚ (fun _ : Fin 2 => V) j x) i) ≤ q := by
    rcases i with ⟨i, a⟩
    by_cases hji : j = i
    · subst i
      simpa [Pi.basis_repr, LinearMap.single_apply] using hx a
    · simpa [Pi.basis_repr, LinearMap.single_apply, hji, Ne.symm hji, rationalLogHeight] using hq
  apply exists_submodule_basis_of_spanning_logHeight (Pi.basis (fun _ : Fin 2 => e)) _ v hv
  intro j i
  cases j with
  | inl j =>
    cases j with
    | inl j => simpa [v, Δ, Pi.basis_repr] using hc j i.2
    | inr j => exact hsingle 0 (p j) (hp j) i
  | inr j =>
    cases j with
    | inl j => exact hsingle 0 (k j) (hk j) i
    | inr j => exact hsingle 1 (k j) (hk j) i

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def coefficientFreeSpan (d : Fin s) : Submodule ℚ D.CoefficientFreeLieAlgebra :=
  D.commonFreeSpan d ⊔ D.dependentFreeSpan d

theorem commonFreeSpan_le_coefficientFreeSpan (d : Fin s) :
    D.commonFreeSpan d ≤ D.coefficientFreeSpan d := le_sup_left

theorem dependentFreeSpan_le_coefficientFreeSpan (d : Fin s) :
    D.dependentFreeSpan d ≤ D.coefficientFreeSpan d := le_sup_right

theorem coefficientFreeSpan_le_layer (d : Fin s) :
    D.coefficientFreeSpan d ≤ D.coefficientFreeFiltration.layer (d.val + 1) 1 :=
  sup_le (D.commonFreeSpan_le_layer d) (D.dependentFreeSpan_le_layer d)

variable {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.freeEvaluation_coefficientFreeSpan (d : Fin s) :
    (D.coefficientFreeSpan d).map (B.freeEvaluation D).toLinearMap =
      D.commonCoefficientSpace ⟨d.val + 1, by omega⟩ := by
  rw [coefficientFreeSpan, Submodule.map_sup, B.freeEvaluation_commonFreeSpan D,
    B.freeEvaluation_dependentFreeSpan D]
  exact sup_eq_left.mpr (D.dependentCoefficientSpace_le_common _)

theorem CoefficientBases.combined_free_sunflower (n : ℕ) (d : Fin n → Fin s)
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s)
    (hr : a.length = r) (v : Fin n → D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ D.coefficientFreeSpan (d i))
    (j k : Fin n) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : v j ∈ D.dependentFreeSpan (d j)) (hvk : v k ∈ D.dependentFreeSpan (d k)) :
    B.freeFrequency D (lieTreeEval v a) = 0 := by
  have h := D.coefficient_sunflower n (fun i => ⟨(d i).val + 1, by omega⟩) a hd hr
    (fun i => B.freeEvaluation D (v i))
    (fun i => (B.freeEvaluation_coefficientFreeSpan D (d i)).le ⟨v i, hv i, rfl⟩)
    j k hjk hj hk
    ((B.freeEvaluation_dependentFreeSpan D (d j)).le ⟨v j, hvj, rfl⟩)
    ((B.freeEvaluation_dependentFreeSpan D (d k)).le ⟨v k, hvk, rfl⟩)
  change W.vertical.frequency (B.freeEvaluation D (lieTreeEval v a)) = 0
  rw [map_lieTreeEval]
  exact h

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (e : Basis (Fin (finrank ℚ D.CoefficientFreeLieAlgebra)) ℚ D.CoefficientFreeLieAlgebra)
  {Q : ℝ} (F : FreeCoordinateFrame e Q)

include F

theorem exists_dependentFreeSpan_basis (hs : 1 ≤ s) (d : Fin s) :
    ∃ c : Basis (Fin (finrank ℚ (D.dependentFreeSpan d))) ℚ (D.dependentFreeSpan d),
      ∀ a i, rationalLogHeight (e.repr (c a : D.CoefficientFreeLieAlgebra) i) ≤ Q :=
  exists_submodule_basis_of_spanning_logHeight e _
    (fun a => D.coefficientFreeGenerator (Sum.inr ⟨d, a⟩)) rfl
    (fun a i => F.generator_height hs (Sum.inr ⟨d, a⟩) i)

theorem exists_coefficientFreeSpan_basis (hs : 1 ≤ s) (d : Fin s) :
    ∃ c : Basis (Fin (finrank ℚ (D.coefficientFreeSpan d))) ℚ (D.coefficientFreeSpan d),
      ∀ a i, rationalLogHeight (e.repr (c a : D.CoefficientFreeLieAlgebra) i) ≤ Q := by
  let v := Sum.elim (fun a => D.coefficientFreeGenerator (Sum.inl ⟨d, a⟩))
    (fun a => D.coefficientFreeGenerator (Sum.inr ⟨d, a⟩))
  have hspan : Submodule.span ℚ (Set.range v) = D.coefficientFreeSpan d := by
    dsimp only [v]
    rw [span_range_sumElim]
    rfl
  apply exists_submodule_basis_of_spanning_logHeight e _ v hspan
  intro a i
  cases a with
  | inl a => exact F.generator_height hs (Sum.inl ⟨d, a⟩) i
  | inr a => exact F.generator_height hs (Sum.inr ⟨d, a⟩) i

end Erdos3.NativeRankRelation.CommonData

end

end OAI

/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/UniformFrozenDescent.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Nilpotent.TopInvariantNiltestBudget
public import OAI.Combinatorics.Progressions.Nilpotent.FrozenComplexNiltest
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

noncomputable def topQuotientModel (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    RationalFilteredNilmanifold (L ⧸ F.layerIdeal (s + 1)) s
      (Fintype.card {i : Fin d // ¬ s + 1 ≤ w i}) :=
  F.coordinateQuotientModel b w hlayers (F.layerIdeal (s + 1)) le_rfl
    {i | s + 1 ≤ w i} (hlayers (s + 1)) Γ N hN hin hout

theorem topQuotientModel_geometry (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N)
    {p : ℝ} (hp : 0 ≤ p)
    (hgeom : (F.ofAdaptedBasis b w hlayers Γ N hN hin hout).GeometryComplexityLE p) :
    (F.topQuotientModel b w hlayers Γ N hN hin hout).GeometryComplexityLE p := by
  apply F.coordinateQuotientModel_geometry b w hlayers (F.layerIdeal (s + 1)) le_rfl
    {i | s + 1 ≤ w i} (hlayers (s + 1)) Γ N hN hin hout hp
  · simpa only [Fintype.card_fin] using hgeom.1
  · exact hgeom.2.1
  · exact hgeom.2.2.1

@[simp] theorem topQuotientModel_filtration (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    (F.topQuotientModel b w hlayers Γ N hN hin hout).filtration = F.quotientTop := rfl

@[simp] theorem topQuotientModel_lattice (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    (F.topQuotientModel b w hlayers Γ N hN hin hout).lattice =
      Γ.map (F.quotientStepHom (F.layerIdeal (s + 1)) le_rfl) := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem quotientFinBasis_repr_mk {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι]
    (b : Basis ι ℚ L) (I : LieIdeal ℚ L) (S : Set ι) [DecidablePred (· ∈ S)]
    (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))
    (x : L) (k : Fin (Fintype.card {i // i ∉ S})) :
    (quotientFinBasis b I S hspan).repr (lieQuotientMap I x) k =
      b.repr x ((Fintype.equivFin {i // i ∉ S}).symm k) := by
  rw [quotientFinBasis, Basis.repr_reindex_apply]
  exact supportedQuotientBasis_repr_mk b I.toSubmodule S hspan x _

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

theorem exists_controlled_top_quotient {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    ∃ n : ℕ, n ≤ d ∧
      ∃ Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n,
        Q.filtration = D.filtration.quotientTop ∧
        Q.lattice = D.lattice.map
          (D.filtration.quotientStepHom (D.filtration.layerIdeal (s + 1)) le_rfl) ∧
        Q.GeometryComplexityLE ((p + 3) ^ 11) ∧
        (∀ i k, rationalLogHeight (Q.basis.repr
          (lieQuotientMap (D.filtration.layerIdeal (s + 1)) (D.basis i)) k) ≤ (p + 3) ^ 5) ∧
        ∃ w : Fin n → ℕ, ∀ j, Q.filtration.layer j = Submodule.span ℚ (Q.basis '' {i | j ≤ w i}) := by
  classical
  obtain ⟨b, w, N, _, _, hF, _, hinverse, hbracket, hN, hNp, hin, hout⟩ :=
    D.exists_controlled_adapted_basis hp hD
  let Q := D.filtration.topQuotientModel b w hF D.lattice N hN hin hout
  have hdim : finrank ℚ L = d := by simpa only [Fintype.card_fin] using finrank_eq_card_basis D.basis
  have hn : Fintype.card {i : Fin (finrank ℚ L) // ¬ s + 1 ≤ w i} ≤ d := by
    simpa only [Fintype.card_fin, hdim] using
      Fintype.card_subtype_le (fun i : Fin (finrank ℚ L) => ¬ s + 1 ≤ w i)
  have hp1 : 0 ≤ p + 1 := by linarith
  have hpPow : p + 1 ≤ (p + 3) ^ 11 := by
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      (le_power_budget hp1 (by decide : 1 ≤ 11))
  have hpr : p ≤ (p + 3) ^ 11 := (by linarith : p ≤ p + 1).trans hpPow
  have hbase : 1 ≤ p + 3 := by linarith
  have h9 : (p + 3) ^ 9 ≤ (p + 3) ^ 11 := pow_le_pow_right₀ hbase (by decide)
  have hgeom : Q.GeometryComplexityLE ((p + 3) ^ 11) := by
    apply D.filtration.topQuotientModel_geometry b w hF D.lattice N hN hin hout (by positivity)
    apply D.filtration.ofAdaptedBasis_geometry b w hF D.lattice N hN hin hout (by positivity)
    · exact (by simpa only [hdim] using hD.1 : (finrank ℚ L : ℝ) ≤ p).trans hpr
    · exact hNp.trans (Real.exp_le_exp.mpr h9)
    · exact hbracket
  refine ⟨_, hn, Q, rfl, rfl, hgeom, ?_, quotientFinWeight w {i | s + 1 ≤ w i}, ?_⟩
  · intro i k
    have hspan : (D.filtration.layerIdeal (s + 1)).toSubmodule =
        Submodule.span ℚ (b '' {i | s + 1 ≤ w i}) := hF (s + 1)
    have hcoord := quotientFinBasis_repr_mk b (D.filtration.layerIdeal (s + 1))
      {i | s + 1 ≤ w i} hspan (D.basis i) k
    exact (congrArg rationalLogHeight hcoord).le.trans (hinverse i _)
  · intro j
    exact D.filtration.quotientFinBasis_layers b w hF (D.filtration.layerIdeal (s + 1)) le_rfl
      {i | s + 1 ≤ w i} (hF (s + 1)) j

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)

theorem exists_controlled_reduced_square_geometry {p : ℝ}
    (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ)
      (hlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis b w (hlayers 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b w (hlayers 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.ofAdaptedBasis
        (D.filtration.squareFinBasis b w (hlayers 2)) (squareFinWeight w)
        (D.filtration.squareFinBasis_layers b w hlayers)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE
          (squareGeometryBudget p) ∧
      (D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis b w (hlayers 2)) (squareFinWeight w)
        (D.filtration.squareFinBasis_layers b w hlayers)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE
          (squareGeometryBudget p) := by
  obtain ⟨b, w, hlayers, N, hN, hin, hout, hb, hgeom⟩ :=
    D.exists_controlled_square_geometry hp hD
  exact ⟨b, w, hlayers, N, hN, hin, hout, hb, hgeom,
    D.filtration.squareFiltration.topQuotientModel_geometry _ _ _ _ _ _ _ _
      (squareGeometryBudget_nonneg hp) hgeom⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_frozen_descent (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      (E : RationalFilteredNilmanifold M (s + 1) e) (φ : L →ₗ⁅ℚ⁆ M)
      {w : σ → ℕ} (T : E.Niltest w)
      (g : D.filtration.realification.PolynomialOrbit w) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → T.ComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧
        (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ n : ℕ, n ≤ d ∧
          ∃ Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n,
            ∃ hQF : Q.filtration = D.filtration.quotientTop,
              Q.lattice = Λ.map
                (D.filtration.quotientStepHom (D.filtration.layerIdeal (s + 1)) le_rfl) ∧
              Q.GeometryComplexityLE ((p + C) ^ C) ∧
              (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))
               letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
                 IsModuleTopology.isTopologicalAddGroup ℝ _
               letI := realification_moduleTopology_t2 Q.basis
               ∀ a r : E.RealGroup,
                 (∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
                 (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
                 (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x : D.RealGroup,
                   T.observable (QuotientGroup.mk
                     (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                       (hM := E.filtration.lowerCentralSeries_eq_bot) φ (z * x) * r)) =
                   T.observable (QuotientGroup.mk
                     (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                       (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r))) →
                 ∃ S : Q.Niltest w, S.orbit = D.topQuotientOrbit Q hQF g ∧
                   S.normBound = T.normBound ∧ S.ComplexityLE ((p + C) ^ C) ∧
                   ∀ x : σ → ℤ, S.eval x = T.observable (QuotientGroup.mk
                     (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                       (hM := E.filtration.lowerCentralSeries_eq_bot) φ
                       (D.filtration.realification.polynomialOrbitEval w x g) * r))) := by
  obtain ⟨A, _, hmaps⟩ := exists_uniform_frozen_map (s + 1) k
  obtain ⟨B, _, hdesc⟩ := exists_topInvariant_niltest_budget s
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let P := X + U + 4
  let R := P + (P + 3) ^ 11 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro L M σ _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ w T g p hp hD hT hφ q hq hqp
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hF, hmap⟩ :=
    hmaps D E φ p hp hD hT.1 hφ q hq hqp
  let F := D.withLattice Λ N hN hin hout
  let u := (p + A) ^ A
  let t := p + u + 4
  let r := t + (t + 3) ^ 11 + 4
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hut : u ≤ t := by dsimp [t]; linarith
  have htr : t ≤ r := by dsimp [r]; linarith [pow_nonneg (by linarith : 0 ≤ t + 3) 11]
  have hr : 0 ≤ r := ht.trans htr
  have hQr : (t + 3) ^ 11 ≤ r := by dsimp [r]; linarith
  have hsum : r + (r + B) ^ B ≤ (p + C) ^ C := by
    simpa [R, P, U, X, r, t, u, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hcost : (r + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hr).trans hsum
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hproj, _⟩ :=
    F.exists_controlled_top_quotient ht (hF.mono F hut)
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr ((hut.trans htr).trans hrC)),
    n, hn, Q, hQF, hQL, hQ.mono Q (hQr.trans hrC), ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let : TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ F.filtration.layerIdeal (s + 1))) :=
    moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ F.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  intro a b ha hb hinvariant
  obtain ⟨hconj, K, hK, hKlip⟩ := hmap a b ha hb
  let T' := F.frozenComplexNiltest E φ a b hconj T g K hKlip
  have hT' : T'.ComplexityLE t :=
    F.frozenComplexNiltest_complexity E φ a b hconj T g K hKlip hp hu hF hT hK
  have h5 : (t + 3) ^ 5 ≤ (t + 3) ^ 11 := pow_le_pow_right₀ (by linarith) (by decide)
  obtain ⟨S, hSo, hSn, hSc, hSe⟩ := hdesc F Q hQF hQL T' r hr (hT'.mono htr)
    (hQ.mono Q hQr) (fun i j => (hproj j i).trans (h5.trans hQr))
    (F.frozenComplexNiltest_top_invariant E φ a b hconj T g K hKlip hinvariant)
  refine ⟨S, hSo, hSn, hSc.mono hcost, ?_⟩
  intro x
  exact (hSe x).trans (F.frozenComplexNiltest_eval E φ a b hconj T g K hKlip x)

end Erdos3.RationalFilteredNilmanifold

end

end OAI

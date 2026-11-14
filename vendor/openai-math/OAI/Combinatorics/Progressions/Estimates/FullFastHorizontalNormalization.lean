/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/FullFastHorizontalNormalization.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Geometry.HorizontalSeparationTransport
public import OAI.Combinatorics.Progressions.Linear.FullFastHorizontalSpanning
@[expose] public section

namespace OAI

section

namespace Erdos3

theorem exists_controlled_derivative_absorption {H E V ι κ ν τ σ : Type*}
    [AddCommGroup H] [Module ℝ H] [AddCommGroup E] [Module ℝ E]
    [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype ι] [Fintype κ] [Fintype ν]
    (e : H ≃ₗ[ℝ] (ι → ℝ)) (U K : Submodule ℝ H)
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ)
    (hAspan : Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) = U.map e.toLinearMap)
    (hBspan : Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) = K.map e.toLinearMap)
    (b : ν → K) (hb : ∀ j, e (b j).val = (B.map (Rat.castHom ℝ)).col j)
    (P : E →ₗ[ℝ] H) (f : E →ₗ[ℝ] E) (hf : P.comp f = P)
    (S R : K →ₗ[ℝ] E) (hSR : S = f.comp R)
    (hS : P.comp S = K.subtype) (hR : P.comp R = K.subtype)
    (c : E →ₗ[ℝ] (τ → ℝ)) (N : E →ₗ[ℝ] V)
    (n rden : ℕ) (hRgrid : ∀ j, c (R (b j)) ∈ realDenominatorGrid n)
    {J l : ℕ} (hJ : 1 ≤ J) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) J) (hB : ∀ i j, RationalHeightLE (B i j) J)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hJp : (J : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (M C : ℝ) (hC : 0 ≤ C) (hSbound : ∀ x, ‖N (S x)‖ ≤ C * ‖e x.val‖)
    (y small rational : σ → E) (k : σ → K)
    (hsystem : ∀ i, y i = small i + f (rational i) + S (k i))
    (hy : ∀ i, P (y i) ∈ U)
    (hsmall : ∀ i, ‖e (P (small i))‖ ≤ Real.exp p / T i)
    (hNsmall : ∀ i, ‖N (small i)‖ ≤ M / T i)
    (hrational : ∀ i, e (P (rational i)) ∈ realDenominatorGrid l)
    (hrgrid : ∀ i, c (rational i) ∈ realDenominatorGrid rden) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∃ ks kr : σ → K, ∀ i,
        P (small i - S (ks i)) ∈ U ∧
        P (rational i - R (kr i)) ∈ U ∧
        (k i + ks i + kr i).val ∈ U ∧
        y i = (small i - S (ks i)) + f (rational i - R (kr i)) + S (k i + ks i + kr i) ∧
        ‖e (ks i).val‖ ≤ Real.exp ((p + 2) ^ 19) * Real.exp p / T i ∧
        ‖N (small i - S (ks i))‖ ≤ (M + C * Real.exp ((p + 2) ^ 19) * Real.exp p) / T i ∧
        ‖e (P (small i - S (ks i)))‖ ≤ (1 + Real.exp ((p + 2) ^ 19)) * Real.exp p / T i ∧
        c (rational i - R (kr i)) ∈ realDenominatorGrid (rden * (n * m)) := by
  obtain ⟨m, hm, hmp, split, hsplit, hnorm, hgrid⟩ :=
    exists_controlled_kernel_split_equiv e U K A B hAspan hBspan b hb (c.comp R) n hRgrid
      hJ hl hA hB hp hι hcols hJp hlp
  let ks : σ → K := fun i => split (P (small i))
  let kr : σ → K := fun i => split (P (rational i))
  have hks (i : σ) : ‖e (ks i).val‖ ≤ Real.exp ((p + 2) ^ 19) * Real.exp p / T i := by
    calc
      _ ≤ Real.exp ((p + 2) ^ 19) * ‖e (P (small i))‖ := hnorm _
      _ ≤ Real.exp ((p + 2) ^ 19) * (Real.exp p / T i) :=
        mul_le_mul_of_nonneg_left (hsmall i) (Real.exp_nonneg _)
      _ = _ := by ring
  refine ⟨m, hm, hmp, ks, kr, fun i => ?_⟩
  have hproj : P (y i) = P (small i) + P (rational i) + (k i).val := by
    rw [hsystem i, map_add, map_add,
      show P (f (rational i)) = P (rational i) from DFunLike.congr_fun hf _,
      show P (S (k i)) = (k i).val from DFunLike.congr_fun hS _]
  have hparts := horizontal_parts_separation_equiv e U K A B hAspan hBspan
    hJ hl hA hB hp hι hcols hJp hlp T hT i
    (P (y i)) (P (small i)) (P (rational i)) (k i) hproj (hy i) (hsmall i) (hrational i)
  have habsorb := horizontal_absorption_with_split U K P f hf S R hSR hS hR split hsplit
    (y i) (small i) (rational i) (k i) (hsystem i) (hy i) hparts.1 hparts.2
  refine ⟨habsorb.1, habsorb.2.1, habsorb.2.2.1, habsorb.2.2.2, hks i, ?_, ?_, ?_⟩
  · calc
      _ ≤ ‖N (small i)‖ + ‖N (S (ks i))‖ := by rw [map_sub]; exact norm_sub_le _ _
      _ ≤ M / T i + C * (Real.exp ((p + 2) ^ 19) * Real.exp p / T i) :=
        add_le_add (hNsmall i) ((hSbound _).trans (mul_le_mul_of_nonneg_left (hks i) hC))
      _ = _ := by ring
  · rw [map_sub, map_sub, show P (S (ks i)) = (ks i).val from DFunLike.congr_fun hS _]
    calc
      _ ≤ ‖e (P (small i))‖ + ‖e (ks i).val‖ := norm_sub_le _ _
      _ ≤ Real.exp p / T i + Real.exp ((p + 2) ^ 19) * Real.exp p / T i :=
        add_le_add (hsmall i) (hks i)
      _ = _ := by ring
  · rw [map_sub]
    exact realDenominatorGrid_sub_product rden (n * m) _ _ (hrgrid i) (hgrid _ (hrational i))

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ ν τ L V : Type*} [Fintype σ] [DecidableEq σ]
  [Fintype ι] [Fintype κ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L]
  [SeminormedAddCommGroup V] [NormedSpace ℝ V] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "𝓗" => ℝ ⊗[ℚ] (L ⧸ F.layer 2)
local notation "𝓔" => F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "𝓖" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf
local notation "𝓟" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) Wf)
local notation "𝓤" => Submodule.baseChange ℝ (F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W))
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "Y" => (fun (g : 𝓖) i => F.realFastCoefficientDirectionMap Wf (Subtype.val g) (Pi.single i 1))

theorem exists_fullFast_derivative_absorption
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (g : 𝓖) (hzero : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g.val.coord) 0 = 0)
    (K : Submodule ℝ 𝓗) (Q : Matrix (LayerOneBasisIndex ω) ν ℚ)
    (hQspan : Submodule.span ℝ (Set.range (Q.map (Rat.castHom ℝ)).col) = K.map (cH).toLinearMap)
    (b : ν → K) (hb : ∀ j, cH (b j).val = (Q.map (Rat.castHom ℝ)).col j)
    (S R : K →ₗ[ℝ] 𝓔) (hSR : S = (ρ g).toLinearMap.comp R)
    (hS : (𝓟).comp S = K.subtype) (hR : (𝓟).comp R = K.subtype)
    (c : 𝓔 →ₗ[ℝ] (τ → ℝ)) (N : 𝓔 →ₗ[ℝ] V)
    (n rden : ℕ) (hRgrid : ∀ j, c (R (b j)) ∈ realDenominatorGrid n)
    {J l : ℕ} (hJ : 1 ≤ J) (hl : 0 < l)
    (hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) J)
    (hQ : ∀ i j, RationalHeightLE (Q i j) J)
    {p : ℝ} (hp : 0 ≤ p)
    (hsize : ((Fintype.card κ + Fintype.card ι + Fintype.card ν : ℕ) : ℝ) ≤ p)
    (hJp : (J : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (M C : ℝ) (hC : 0 ≤ C) (hSbound : ∀ x, ‖N (S x)‖ ≤ C * ‖cH x.val‖)
    (small rational : σ → 𝓔) (k : σ → K)
    (hsystem : ∀ i, Y g i = small i + ρ g (rational i) + S (k i))
    (hsmall : ∀ i, ‖cH (𝓟 (small i))‖ ≤ Real.exp p / T i)
    (hNsmall : ∀ i, ‖N (small i)‖ ≤ M / T i)
    (hrational : ∀ i, cH (𝓟 (rational i)) ∈ realDenominatorGrid l)
    (hrgrid : ∀ i, c (rational i) ∈ realDenominatorGrid rden) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∃ ks kr : σ → K, ∀ i,
        𝓟 (small i - S (ks i)) ∈ 𝓤 ∧
        𝓟 (rational i - R (kr i)) ∈ 𝓤 ∧
        (k i + ks i + kr i).val ∈ 𝓤 ∧
        Y g i = (small i - S (ks i)) + ρ g (rational i - R (kr i)) + S (k i + ks i + kr i) ∧
        ‖cH (ks i).val‖ ≤ Real.exp ((p + 2) ^ 19) * Real.exp p / T i ∧
        ‖N (small i - S (ks i))‖ ≤ (M + C * Real.exp ((p + 2) ^ 19) * Real.exp p) / T i ∧
        ‖cH (𝓟 (small i - S (ks i)))‖ ≤ (1 + Real.exp ((p + 2) ^ 19)) * Real.exp p / T i ∧
        c (rational i - R (kr i)) ∈ realDenominatorGrid (rden * (n * m)) := by
  have hrow : Fintype.card (LayerOneBasisIndex ω) ≤ Fintype.card ι :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hrows : (Fintype.card (LayerOneBasisIndex ω) : ℝ) ≤ p := by
    have hle : Fintype.card (LayerOneBasisIndex ω) ≤
        Fintype.card κ + Fintype.card ι + Fintype.card ν := by omega
    exact (Nat.cast_le.mpr hle).trans hsize
  have hcol : Fintype.card ((κ ⊕ TopGradedBasisIndex s ω) ⊕ ν) ≤
      Fintype.card κ + Fintype.card ι + Fintype.card ν := by
    rw [Fintype.card_sum]
    exact Nat.add_le_add_right (fullFastDiagonalGenerators_card (κ := κ) (s := s) (ω := ω)) _
  have hf : (𝓟).comp (ρ g).toLinearMap = 𝓟 := by
    apply LinearMap.ext
    intro x
    exact F.realFastCoefficientAction_horizontal (fun _ => 1) (fun _ => Nat.zero_lt_one)
      Wf e ω hF g x
  exact exists_controlled_derivative_absorption cH 𝓤 K (F.fullFastHorizontalMatrix e ω hF v) Q
    (F.fullFastHorizontalMatrix_span e ω hF W hW v hv) hQspan b hb 𝓟 (ρ g).toLinearMap hf
    S R hSR hS hR c N n rden hRgrid hJ hl (F.fullFastHorizontalMatrix_height e ω hF v hJ hheight)
    hQ hp hrows ((Nat.cast_le.mpr hcol).trans hsize) hJp hlp T hT M C hC hSbound
    (Y g) small rational k hsystem
    (fun i => F.fullFast_horizontal_derivative_mem e ω hF W hW g.val g.property hzero i)
    hsmall hNsmall hrational hrgrid

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ ν τ L V : Type*} [Fintype σ] [DecidableEq σ]
  [Fintype ι] [Fintype κ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L]
  [SeminormedAddCommGroup V] [NormedSpace ℝ V] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "𝓗" => ℝ ⊗[ℚ] (L ⧸ F.layer 2)
local notation "𝓔" => F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "𝓖" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf
local notation "𝓟" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) Wf)
local notation "𝓤" => Submodule.baseChange ℝ (F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W))
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "Y" => (fun (g : 𝓖) i => F.realFastCoefficientDirectionMap Wf (Subtype.val g) (Pi.single i 1))

end Erdos3.NilpotentLieFiltration

end

end OAI

/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/WeightedOrbitNormalization.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Polynomial.ShiftedPolynomialBasis
@[expose] public section

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem eval_zero_eq_coefficient (p : VectorPolynomial σ R V) :
    eval (fun _ => 0) p = coefficients p 0 := by
  induction p using TensorProduct.inductionOn with
  | tmul q v => simp [MvPolynomial.aeval_zero', MvPolynomial.constantCoeff_eq]
  | add p q hp hq => simp [hp, hq]

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem horizontal_bch (a b : L) :
    lieQuotientMap (F.layerIdeal 2) (lieBCH s a b) =
      lieQuotientMap (F.layerIdeal 2) a + lieQuotientMap (F.layerIdeal 2) b := by
  rw [map_lieBCH]
  apply lieBCH_eq_add_of_lie_eq_zero
    (lie_quotient_lowerCentralSeries_eq_bot F.lowerCentralSeries_eq_bot (F.layerIdeal 2))
  rw [← LieHom.map_lie]
  apply (lieQuotientMap_eq_zero _ _).mpr
  exact F.lie_mem (show a ∈ F.layer 1 by rw [F.one_eq_top]; trivial)
    (show b ∈ F.layer 1 by rw [F.one_eq_top]; trivial)

def horizontalLog (g : F.Group) : L ⧸ F.layerIdeal 2 := lieQuotientMap (F.layerIdeal 2) g.coord

@[simp] theorem horizontalLog_mul (g h : F.Group) :
    F.horizontalLog (g * h) = F.horizontalLog g + F.horizontalLog h := F.horizontal_bch _ _

@[simp] theorem horizontalLog_inv (g : F.Group) : F.horizontalLog g⁻¹ = -F.horizontalLog g :=
  map_neg (lieQuotientMap (F.layerIdeal 2)) g.coord

theorem normalizedShift_horizontal_zero (h : σ → ℚ) (p : VectorPolynomial σ ℚ L)
    (ε γ : F.Group)
    (heq : (⟨eval h p⟩ : F.Group) * (⟨eval (fun _ => 0) p⟩ : F.Group)⁻¹ = ε * γ) :
    coefficients (normalizedShiftLog s h (-ε.coord) (-γ.coord) p - p) 0 ∈ F.layer 2 := by
  have hh := congrArg F.horizontalLog heq
  simp only [horizontalLog_mul, horizontalLog_inv] at hh
  rw [← sub_eq_add_neg] at hh
  change lieQuotientMap (F.layerIdeal 2) (eval h p) -
    lieQuotientMap (F.layerIdeal 2) (eval (fun _ => 0) p) =
    lieQuotientMap (F.layerIdeal 2) ε.coord + lieQuotientMap (F.layerIdeal 2) γ.coord at hh
  have hsolve := (sub_eq_iff_eq_add).mp hh
  apply (lieQuotientMap_eq_zero (F.layerIdeal 2) _).mp
  rw [← eval_zero_eq_coefficient]
  simp only [map_sub, eval_normalizedShiftLog, F.horizontal_bch, map_neg, zero_add]
  rw [hsolve]
  abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {τ L : Type*} [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

theorem dilationPair_coefficients_mem (r : ℚ) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L))
    (hq : ∀ a, coefficients q a ∈ F.dilationPairLayer r (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) (a : τ →₀ ℕ) :
    coefficients q a ∈ F.dilationPairSubalgebra r := by
  by_cases ha : a = 0
  · rw [ha, hq0]
    exact (F.dilationPairSubalgebra r).zero_mem
  · have hpos : 0 < Finsupp.weight w a :=
      NilpotentLieFiltration.positive_weight_of_ne_zero w hw ha
    exact F.dilationPairLayer_antitone r (Nat.succ_le_of_lt hpos) (hq a)

noncomputable def restrictDilationPairPolynomial (r : ℚ) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L))
    (hq : ∀ a, coefficients q a ∈ F.dilationPairLayer r (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) :
    VectorPolynomial τ ℚ (F.dilationPairSubalgebra r) :=
  restrictCoefficients (F.dilationPairSubalgebra r).toSubmodule q
    (F.dilationPair_coefficients_mem r w hw q hq hq0)

theorem restrictDilationPairPolynomial_eval (r : ℚ) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L))
    (hq : ∀ a, coefficients q a ∈ F.dilationPairLayer r (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) (x : τ → ℚ) :
    (eval (V := F.dilationPairSubalgebra r) x
      (F.restrictDilationPairPolynomial r w hw q hq hq0) : L × L) = eval x q :=
  eval_restrictCoefficients (F.dilationPairSubalgebra r).toSubmodule q
    (F.dilationPair_coefficients_mem r w hw q hq hq0) x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def weightedGroupInclusion (c : σ → ℕ) :
    (F.weightedFiltration c).Group →* F.Group :=
  NilpotentLieBCHGroup.mapOfSteps (F.weightedSubalgebra c).incl

theorem weightedGroupInclusion_injective (c : σ → ℕ) :
    Function.Injective (F.weightedGroupInclusion c) :=
  NilpotentLieBCHGroup.mapOfSteps_injective _ (fun _ _ h => Subtype.ext h)

noncomputable def weightedNormalizationLog (p : VectorPolynomial τ ℚ L) (a b : F.Group) :
    VectorPolynomial τ ℚ L :=
  lieBCH s (lieBCH s (monomial 0 (-a.coord)) p) (monomial 0 (-b.coord))

theorem weightedNormalizationLog_adapted (c : σ → ℕ) (v : τ → ℕ)
    {p : VectorPolynomial τ ℚ L} (hp : F.WeightedAdapted c v p) (a b : F.Group) :
    F.WeightedAdapted c v (F.weightedNormalizationLog p a b) :=
  F.weightedAdapted_bch c v s
    (F.weightedAdapted_bch c v s (F.weightedAdapted_constant c v _) hp)
    (F.weightedAdapted_constant c v _)

theorem weightedNormalizationLog_eval (p : VectorPolynomial τ ℚ L) (a b : F.Group)
    (x : τ → ℚ) :
    eval x (F.weightedNormalizationLog p a b) =
      (a⁻¹ * (⟨eval x p⟩ : F.Group) * b⁻¹).coord := by
  simp only [weightedNormalizationLog, eval_lieBCH, eval_monomial,
    Finsupp.prod_zero_index, one_smul, NilpotentLieBCHGroup.coord_mul,
    NilpotentLieBCHGroup.coord_inv]

theorem weightedNormalizationLog_zero (p : VectorPolynomial τ ℚ L) (a b : F.Group)
    (hzero : (⟨eval (fun _ => 0) p⟩ : F.Group) = a * b) :
    coefficients (F.weightedNormalizationLog p a b) 0 = 0 := by
  rw [← eval_zero_eq_coefficient, F.weightedNormalizationLog_eval, hzero]
  simp

noncomputable def normalizedWeightedOrbit (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (a b : F.Group)
    (hzero : (⟨eval (fun _ => 0) p⟩ : F.Group) = a * b) :
    (F.weightedFiltration c).PolynomialOrbit v :=
  F.restrictWeightedOrbit c v hv (F.weightedNormalizationLog p a b)
    (F.weightedNormalizationLog_adapted c v hp a b) (F.weightedNormalizationLog_zero p a b hzero)

theorem normalizedWeightedOrbit_eval (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (a b : F.Group)
    (hzero : (⟨eval (fun _ => 0) p⟩ : F.Group) = a * b) (x : τ → ℤ) :
    F.weightedGroupInclusion c ((F.weightedFiltration c).polynomialOrbitEval v x
      (F.normalizedWeightedOrbit c v hv p hp a b hzero)) =
      a⁻¹ * (⟨eval (fun i => (x i : ℚ)) p⟩ : F.Group) * b⁻¹ := by
  apply NilpotentLieBCHGroup.ext
  change (((F.weightedFiltration c).polynomialOrbitEval v x
    (F.restrictWeightedOrbit c v hv _ _ _)).coord : L) = _
  rw [F.restrictWeightedOrbit_eval, F.weightedNormalizationLog_eval]

theorem normalizedWeightedOrbit_zero (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (a b : F.Group)
    (hzero : (⟨eval (fun _ => 0) p⟩ : F.Group) = a * b) :
    (F.weightedFiltration c).polynomialOrbitEval v 0
      (F.normalizedWeightedOrbit c v hv p hp a b hzero) = 1 := by
  apply F.weightedGroupInclusion_injective c
  rw [F.normalizedWeightedOrbit_eval, map_one]
  simp only [Pi.zero_apply, Int.cast_zero, hzero, inv_mul_cancel_left, mul_inv_cancel]

end Erdos3.MultidegreeLieFiltration

end

end OAI

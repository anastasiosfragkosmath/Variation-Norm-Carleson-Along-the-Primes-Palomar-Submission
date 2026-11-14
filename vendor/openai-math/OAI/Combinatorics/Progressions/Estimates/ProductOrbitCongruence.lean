/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/ProductOrbitCongruence.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.PolarizedCoefficientPermutation
public import OAI.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization
@[expose] public section

namespace OAI

section

open scoped TensorProduct BigOperators

namespace Erdos3

theorem baseChange_mem_of_mapsTo {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (P : Submodule ℚ V) (Q : Submodule ℚ W)
    (f : V →ₗ[ℚ] W) (hf : ∀ x ∈ P, f x ∈ Q) {x : ℝ ⊗[ℚ] V}
    (hx : x ∈ P.baseChange ℝ) : f.baseChange ℝ x ∈ Q.baseChange ℝ := by
  have hm : P.baseChange ℝ ≤ (Q.baseChange ℝ).comap (f.baseChange ℝ) := by
    rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    exact Submodule.tmul_mem_baseChange_of_mem 1 (hf a ha)
  exact hm hx

variable {ι : Type*} {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

noncomputable def realProductSingle (i : ι) :
    (ℝ ⊗[ℚ] L i) →ₗ[ℝ] (ℝ ⊗[ℚ] (∀ j, L j)) := by
  classical
  exact (LinearMap.single ℚ L i).baseChange ℝ

theorem realProductSingle_projection (i : ι) (x : ℝ ⊗[ℚ] L i) :
    realificationLieHom (liePiEval i) (realProductSingle i x) = x := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    change r ⊗ₜ[ℚ] (Pi.single i x i) = r ⊗ₜ[ℚ] x
    rw [Pi.single_eq_same]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realProductSingle_projection_ne {i j : ι} (hij : j ≠ i) (x : ℝ ⊗[ℚ] L i) :
    realificationLieHom (liePiEval j) (realProductSingle i x) = 0 := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    change r ⊗ₜ[ℚ] (Pi.single i x j) = 0
    rw [Pi.single_eq_of_ne hij, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

theorem realProductSingle_mem_layer {s : ℕ} (F : ∀ i, NilpotentLieFiltration (L i) s)
    (i : ι) (n : ℕ) {x : ℝ ⊗[ℚ] L i} (hx : x ∈ (F i).realification.layer n) :
    realProductSingle i x ∈ (NilpotentLieFiltration.pi F).realification.layer n := by
  classical
  apply baseChange_mem_of_mapsTo ((F i).layer n) ((NilpotentLieFiltration.pi F).layer n)
    (LinearMap.single ℚ L i) _ hx
  intro a ha
  apply (NilpotentLieFiltration.mem_pi_layer F n _).mpr
  intro j
  change Pi.single i a j ∈ (F j).layer n
  by_cases hji : j = i
  · subst j
    simpa only [Pi.single_eq_same] using ha
  · rw [Pi.single_eq_of_ne hji]
    exact Submodule.zero_mem _

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {bound : σ → ℕ}
  (F : ∀ i, MultidegreeLieFiltration σ (L i) s bound)

theorem realProductSingle_mem_layer (i : ι) (a : σ → ℕ) {x : ℝ ⊗[ℚ] L i}
    (hx : x ∈ (F i).realification.layer a) :
    realProductSingle i x ∈ (pi F).realification.layer a := by
  classical
  apply baseChange_mem_of_mapsTo ((F i).layer a) ((pi F).layer a)
    (LinearMap.single ℚ L i) _ hx
  intro y hy
  apply (mem_pi_layer F a _).mpr
  intro j
  change Pi.single i y j ∈ (F j).layer a
  by_cases hji : j = i
  · subst j
    simpa only [Pi.single_eq_same] using hy
  · rw [Pi.single_eq_of_ne hji]
    exact Submodule.zero_mem _

noncomputable def piRealOrbit (g : ∀ i, (F i).realification.PolynomialOrbit) :
    (pi F).realification.PolynomialOrbit :=
  (pi F).realification.polynomialOrbitOfLog
    (∑ i, VectorPolynomial.map ((realProductSingle i).restrictScalars ℚ)
      ((g i).log (F i).realification)) (by
      intro a
      simp only [map_sum, Finsupp.finsetSum_apply, VectorPolynomial.coefficients_map]
      apply Submodule.sum_mem
      intro i _
      exact realProductSingle_mem_layer F i _ ((g i).adapted (F i).realification a))

theorem piRealOrbit_eval (g : ∀ i, (F i).realification.PolynomialOrbit) (x : σ → ℤ) (i : ι) :
    NilpotentLieBCHGroup.realificationMap
      (hnil := (pi F).ordinary.lowerCentralSeries_eq_bot)
      (hM := (F i).ordinary.lowerCentralSeries_eq_bot) (liePiEval i)
      ((pi F).realification.polynomialOrbitEval x (piRealOrbit F g)) =
        (F i).realification.polynomialOrbitEval x (g i) := by
  classical
  apply NilpotentLieBCHGroup.ext
  simp only [NilpotentLieBCHGroup.realificationMap_coord, polynomialOrbitEval_coord,
    piRealOrbit, polynomialOrbitOfLog, PolynomialOrbit.log, map_sum, VectorPolynomial.eval_map]
  rw [Finset.sum_eq_single i]
  · exact realProductSingle_projection i _
  · intro j _ hji
    exact realProductSingle_projection_ne (Ne.symm hji) _
  · simp

end Erdos3.MultidegreeLieFiltration

end

section

open scoped TensorProduct BigOperators

namespace Erdos3.NilpotentLieFiltration

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
  (F : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ}

noncomputable def piRealOrbit (p : ∀ i, (F i).realification.PolynomialOrbit w) :
    (pi F).realification.PolynomialOrbit w :=
  polynomialOrbitOfLog
    (∑ i, VectorPolynomial.map ((realProductSingle i).restrictScalars ℚ) (p i).log) (by
      apply ((pi F).realification.adapted_iff_coefficients w _).mpr
      intro α
      simp only [map_sum, Finsupp.finsetSum_apply, VectorPolynomial.coefficients_map]
      apply Submodule.sum_mem
      intro i _
      exact realProductSingle_mem_layer F i _
        (((F i).realification.adapted_iff_coefficients w _).mp (p i).adapted α))

theorem piRealOrbit_eval (p : ∀ i, (F i).realification.PolynomialOrbit w)
    (x : σ → ℤ) (i : ι) :
    NilpotentLieBCHGroup.realificationMap
      (hnil := (pi F).lowerCentralSeries_eq_bot) (hM := (F i).lowerCentralSeries_eq_bot) (liePiEval i)
      ((pi F).realification.polynomialOrbitEval w x (piRealOrbit F p)) =
        (F i).realification.polynomialOrbitEval w x (p i) := by
  classical
  apply NilpotentLieBCHGroup.ext
  simp only [NilpotentLieBCHGroup.realificationMap_coord, polynomialOrbitEval_coord,
    piRealOrbit, polynomialOrbitOfLog_log, map_sum, VectorPolynomial.eval_map]
  rw [Finset.sum_eq_single i]
  · exact realProductSingle_projection i _
  · intro j _ hji
    exact realProductSingle_projection_ne (Ne.symm hji) _
  · simp

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
  (F : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ}

theorem piRealOrbit_coefficient (p : ∀ i, (F i).realification.PolynomialOrbit w)
    (α : σ →₀ ℕ) (i : ι) :
    realificationLieHom (liePiEval i) (coefficients (piRealOrbit F p).log α) =
      coefficients (p i).log α := by
  classical
  simp only [piRealOrbit, polynomialOrbitOfLog_log, map_sum,
    Finsupp.finsetSum_apply, coefficients_map]
  rw [Finset.sum_eq_single i]
  · exact realProductSingle_projection i _
  · intro j _ hji
    exact realProductSingle_projection_ne (Ne.symm hji) _
  · simp

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open scoped TensorProduct

end Erdos3

end

section

open scoped TensorProduct BigOperators

namespace Erdos3.NilpotentLieFiltration

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

end Erdos3.RationalFilteredNilmanifold

end

end OAI

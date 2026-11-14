/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/NiltestAffineProjection.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.PositiveCyclicCorrelation
public import OAI.Combinatorics.Progressions.Fourier.VerticalFrequencyIdentification
public import OAI.Combinatorics.Progressions.Lattices.CommonIntegerIntervalCorrelation
public import OAI.Combinatorics.Progressions.Lattices.IntegerAffineSubstitution
public import OAI.Combinatorics.Progressions.Lattices.RealSymbolAffine
public import OAI.Combinatorics.Progressions.Polynomial.PolynomialSymbolBounds
@[expose] public section

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

noncomputable def substitute (T : D.Niltest w) (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ i, f i ∈ weightedSupportLE v (w i)) : D.Niltest v :=
  { T with orbit := D.filtration.realification.polynomialOrbitSubstitute f hf T.orbit }

theorem eval_substitute (T : D.Niltest w) (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ i, f i ∈ weightedSupportLE v (w i)) (x : τ → ℤ) (y : σ → ℤ)
    (hxy : ∀ i, MvPolynomial.aeval (R := ℚ) (fun j => (x j : ℚ)) (f i) = (y i : ℚ)) :
    (T.substitute f hf).eval x = T.eval y := by
  exact congrArg (fun z : D.RealGroup => T.observable (QuotientGroup.mk z))
    (D.filtration.realification.polynomialOrbitSubstitute_eval f hf T.orbit x y hxy)

@[simp] theorem substitute_complexityLE (T : D.Niltest w) (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ i, f i ∈ weightedSupportLE v (w i)) (p : ℝ) :
    (T.substitute f hf).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

noncomputable def affinePullback [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (A : σ → τ → ℤ) (b : σ → ℤ) : D.Niltest (fun _ : τ => 1) :=
  T.substitute (integerAffinePolynomial A b) (integerAffinePolynomial_support A b)

theorem eval_affinePullback [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (A : σ → τ → ℤ) (b : σ → ℤ) (x : τ → ℤ) :
    (T.affinePullback A b).eval x = T.eval (integerAffineMap A b x) :=
  T.eval_substitute (integerAffinePolynomial A b) (integerAffinePolynomial_support A b)
    x (integerAffineMap A b x) (integerAffinePolynomial_eval A b x)

@[simp] theorem affinePullback_complexityLE [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (A : σ → τ → ℤ) (b : σ → ℤ) (p : ℝ) :
    (T.affinePullback A b).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

noncomputable def linearPullbackHom [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (f : σ → ((τ → ℤ) →+ ℤ)) : D.Niltest (fun _ : τ => 1) := by
  classical
  exact T.affinePullback (fun i j => f i (Pi.single j 1)) 0

theorem eval_linearPullbackHom [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (f : σ → ((τ → ℤ) →+ ℤ)) (x : τ → ℤ) :
    (T.linearPullbackHom f).eval x = T.eval (fun i => f i x) := by
  classical
  change (T.affinePullback (fun i j => f i (Pi.single j 1)) 0).eval x = _
  rw [eval_affinePullback]
  congr 1
  funext i
  simpa only [integerAffineMap, Pi.zero_apply, zero_add] using (integerLinearForm_eq_sum (f i) x).symm

@[simp] theorem linearPullbackHom_complexityLE [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (f : σ → ((τ → ℤ) →+ ℤ)) (p : ℝ) :
    (T.linearPullbackHom f).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def translate (T : D.Niltest w) (hw : ∀ i, 0 < w i) (h : σ → ℤ) : D.Niltest w :=
  { T with
    orbit := NilpotentLieFiltration.polynomialOrbitOfLog
      (VectorPolynomial.translate (fun i => (h i : ℚ)) T.orbit.log)
      (D.filtration.realification.adapted_translate w hw (fun i => (h i : ℚ)) T.orbit.adapted) }

@[simp] theorem eval_translate (T : D.Niltest w) (hw : ∀ i, 0 < w i) (h x : σ → ℤ) :
    (T.translate hw h).eval x = T.eval (x + h) := by
  apply congrArg T.observable
  apply congrArg QuotientGroup.mk
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.eval (fun i => (x i : ℚ))
      (VectorPolynomial.translate (fun i => (h i : ℚ)) T.orbit.log) =
    VectorPolynomial.eval (fun i => ((x + h) i : ℚ)) T.orbit.log
  rw [VectorPolynomial.eval_translate]
  simp only [Pi.add_apply, Int.cast_add]

@[simp] theorem translate_complexityLE (T : D.Niltest w) (hw : ∀ i, 0 < w i)
    (h : σ → ℤ) (p : ℝ) : (T.translate hw h).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {I L : Type*} [Fintype I] [DecidableEq I] [LieRing L] [LieAlgebra ℚ L] {s dim : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s dim}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {K K' L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

open scoped TensorProduct BigOperators

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial
open scoped TensorProduct BigOperators

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def symbol (T : D.Niltest w) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) :
    D.filtration.RealPolynomialSymbolGroup w :=
  D.filtration.realPolynomialSymbolHom b ω hF w ⟨⟨T.orbit.log, T.orbit.property⟩⟩

theorem symbol_translate (T : D.Niltest w) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (hw : ∀ i, 0 < w i) (h : σ → ℤ) :
    (T.translate hw h).symbol b ω hF = T.symbol b ω hF := by
  apply D.filtration.realPolynomialSymbolHom_eq_of_quotient_eq b ω hF w
  apply NilpotentLieBCHGroup.ext
  exact D.filtration.realification.polynomialSymbolMap_translate w hw
    (fun i => (h i : ℚ)) ⟨T.orbit.log, T.orbit.property⟩

theorem mean_translate_box [Fintype σ] [DecidableEq σ]
    (T : D.Niltest w) (hw : ∀ i, 0 < w i) (a : σ → ℤ) (N : σ → ℕ) :
    (𝔼 x ∈ integerBox N, (T.translate hw a).eval x) =
      𝔼 x ∈ translatedIntegerBox a N, T.eval x := by
  rw [translatedIntegerBox, translateSupport,
    Finset.expect_image (add_right_injective a).injOn]
  apply Finset.expect_congr rfl
  intro x _
  rw [T.eval_translate, add_comm]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

noncomputable def scalarAffinePolynomial {σ : Type*} (r : ℚ) (shift : σ → ℚ) (i : σ) :
    MvPolynomial σ ℚ := MvPolynomial.C (shift i) + MvPolynomial.C r * MvPolynomial.X i

theorem scalarAffinePolynomial_support {σ : Type*} (r : ℚ) (shift : σ → ℚ) (i : σ) :
    scalarAffinePolynomial r shift i ∈ weightedSupportLE (fun _ : σ => 1) 1 := by
  apply Submodule.add_mem
  · exact weightedSupportLE_C _ 1 (shift i)
  · simpa only [zero_add] using
      weightedSupportLE_mul (weightedSupportLE_C (fun _ : σ => 1) 0 r)
        (weightedSupportLE_X (fun _ : σ => 1) i)

namespace VectorPolynomial

theorem substitute_scalarAffinePolynomial {σ V : Type*} [AddCommGroup V] [Module ℚ V]
    (r : ℚ) (shift : σ → ℚ) (p : VectorPolynomial σ ℚ V) :
    substitute (scalarAffinePolynomial r shift) p =
      weightedDilation (fun _ => 1) r (translate shift p) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval_zero
  intro x
  rw [map_sub, eval_substitute, eval_weightedDilation, eval_translate]
  simp [scalarAffinePolynomial, add_comm]

end VectorPolynomial

namespace RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

noncomputable def scalarAffinePullback (T : D.Niltest (fun _ : σ => 1))
    (r : ℚ) (shift : σ → ℚ) : D.Niltest (fun _ : σ => 1) :=
  T.substitute (scalarAffinePolynomial r shift) (scalarAffinePolynomial_support r shift)

@[simp] theorem scalarAffinePullback_complexityLE (T : D.Niltest (fun _ : σ => 1))
    (r : ℚ) (shift : σ → ℚ) (p : ℝ) :
    (T.scalarAffinePullback r shift).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

theorem scalarAffinePullback_log (T : D.Niltest (fun _ : σ => 1)) (r : ℚ) (shift : σ → ℚ) :
    (T.scalarAffinePullback r shift).orbit.log =
      weightedDilation (fun _ => 1) r (VectorPolynomial.translate shift T.orbit.log) :=
  substitute_scalarAffinePolynomial r shift T.orbit.log

theorem scalarAffinePullback_symbol (T : D.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (r : ℚ) (shift : σ → ℚ) :
    (T.scalarAffinePullback r shift).symbol b ω hF =
      D.filtration.realPolynomialSymbolDilationHom (fun _ => 1) r (T.symbol b ω hF) := by
  apply NilpotentLieBCHGroup.ext
  change D.filtration.realSymbolOfPolynomial b ω hF (fun _ => 1)
      (T.scalarAffinePullback r shift).orbit.log =
    D.filtration.realPolynomialSymbolDilation (fun _ => 1) r
      (D.filtration.realSymbolOfPolynomial b ω hF (fun _ => 1) T.orbit.log)
  rw [T.scalarAffinePullback_log]
  apply NilpotentLieFiltration.realSymbolOfPolynomial_affine
  · exact fun _ => Nat.zero_lt_one
  · exact T.orbit.adapted

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem symbol_eq_of_orbit_eq (T U : D.Niltest w) (h : T.orbit = U.orbit)
    (b : Module.Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) :
    T.symbol b ω hF = U.symbol b ω hF := by
  unfold symbol
  apply congrArg (D.filtration.realPolynomialSymbolHom b ω hF w)
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact congrArg (fun o : D.filtration.realification.PolynomialOrbit w => o.log) h

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

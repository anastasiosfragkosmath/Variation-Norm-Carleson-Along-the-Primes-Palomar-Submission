/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/NativeCrossFactorization.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.FixedObservableCorrelation
public import OAI.Combinatorics.Progressions.Estimates.NativeEquivalenceTransitivity
public import OAI.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest
@[expose] public section

namespace OAI

section

namespace Erdos3

variable {G : Type*} [Add G]

noncomputable def fourPointProduct (f₁ f₂ f₃ f₄ : G → ℂ) (a x : G) : ℂ :=
  star (f₁ x) * f₂ (x + a) * f₃ x * star (f₄ (x + a))

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeVectorCorrelation {I : Type*} (degree N : ℕ) [NeZero N] (p : ℝ)
    (f : I → ZMod N → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest (fun _ : Unit => 1)
  complexity : test.ComplexityLE p
  coordinate : I
  correlation : Real.exp (-p) ≤
    ‖𝔼 x, f coordinate x * star (test.evalCyclic N (fun _ => x))‖

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

namespace NativeVectorCorrelation

noncomputable def mono {I : Type*} {degree N : ℕ} [NeZero N] {p q : ℝ}
    {f : I → ZMod N → ℂ} (W : NativeVectorCorrelation degree N p f) (hpq : p ≤ q) :
    NativeVectorCorrelation degree N q f :=
  { W with
    complexity := W.complexity.mono hpq
    correlation := (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans W.correlation }

theorem exists_of_mean {I : Type*} (degree N : ℕ) [NeZero N] {p : ℝ}
    (f : I → ZMod N → ℂ) (hp : 2 ≤ p) (h : ∃ i, Real.exp (-p) ≤ ‖𝔼 x, f i x‖) :
    Nonempty (NativeVectorCorrelation degree N p f) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨{
    L := RationalTorus.Algebra 0
    dim := 0
    model := RationalTorus.trivialNilmanifold degree
    test := RationalFilteredNilmanifold.Niltest.const _ (fun _ : Unit => 1) 1
    complexity := RationalTorus.trivialNilmanifold_const_one_complexity degree _ hp
    coordinate := i
    correlation := ?_
  }⟩
  simpa only [RationalFilteredNilmanifold.Niltest.evalCyclic,
    RationalFilteredNilmanifold.Niltest.eval, RationalFilteredNilmanifold.Niltest.const,
    star_one, mul_one] using hi

end NativeVectorCorrelation

end Erdos3

end

section

namespace Erdos3.NativeVectorCorrelation

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_of_mean_approx {I : Type*} {degree N : ℕ} [NeZero N] {p : ℝ}
    {f : I → ZMod N → ℂ} (W : NativeVectorCorrelation degree N p f)
    (g : I → ZMod N → ℂ)
    (herr : (𝔼 x, ‖f W.coordinate x - g W.coordinate x‖) ≤ Real.exp (-(2 * p)) / 2) :
    Nonempty (NativeVectorCorrelation degree N (p + 1) g) := by
  let b (x : ZMod N) := star (W.test.evalCyclic N (fun _ => x))
  have hb (x : ZMod N) : ‖b x‖ ≤ Real.exp p := by
    simpa only [b, norm_star, RationalFilteredNilmanifold.Niltest.evalCyclic] using W.test.eval_budget W.complexity
      (fun _ : Unit => (x.val : ℤ))
  have he := mean_error_mul_bounded (f W.coordinate) (g W.coordinate) b
    (Real.exp_pos p).le hb herr
  have hexp : Real.exp p * (Real.exp (-(2 * p)) / 2) = Real.exp (-p) / 2 := by
    rw [← mul_div_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hexp] at he
  have hdiff : ‖(𝔼 x, f W.coordinate x * b x) -
      (𝔼 x, g W.coordinate x * b x)‖ ≤ Real.exp (-p) / 2 := by
    rw [← Finset.expect_sub_distrib]
    exact (RCLike.norm_expect_le (K := ℂ)).trans he
  have hretain : Real.exp (-p) / 2 ≤ ‖𝔼 x, g W.coordinate x * b x‖ := by
    have htri := norm_le_norm_add_norm_sub
      (𝔼 x, g W.coordinate x * b x) (𝔼 x, f W.coordinate x * b x)
    rw [norm_sub_rev] at htri
    have hc : Real.exp (-p) ≤ ‖𝔼 x, f W.coordinate x * b x‖ := W.correlation
    linarith
  refine ⟨{ W with complexity := W.complexity.mono (by linarith), correlation := ?_ }⟩
  have ht : Real.exp (-(p + 1)) ≤ Real.exp (-p) / 2 := by
    simpa only [neg_add, sub_eq_add_neg] using exp_sub_one_le_half_exp (-p)
  exact ht.trans hretain

theorem exists_of_uniform_approx {I : Type*} {degree N : ℕ} [NeZero N] {p : ℝ}
    {f : I → ZMod N → ℂ} (W : NativeVectorCorrelation degree N p f)
    (g : I → ZMod N → ℂ)
    (herr : ∀ i x, ‖f i x - g i x‖ ≤ Real.exp (-(2 * p)) / 2) :
    Nonempty (NativeVectorCorrelation degree N (p + 1) g) := by
  apply W.exists_of_mean_approx g
  calc
    _ ≤ 𝔼 _x : ZMod N, Real.exp (-(2 * p)) / 2 :=
      Finset.expect_le_expect (fun x _ => herr W.coordinate x)
    _ = _ := by simp

end Erdos3.NativeVectorCorrelation

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

noncomputable def nativeCrossResidual {N : ℕ} (f₀ f₁ : ZMod N → ℂ)
    (m : ZMod N → ZMod N → ℂ) (h : ZMod N) (_ : Unit) (x : ZMod N) : ℂ :=
  f₀ x * star (f₁ (x + h)) * star (m h x)

abbrev NativeCrossWitnesses (s N : ℕ) [NeZero N] (p : ℝ)
    (f₀ f₁ : ZMod N → ℂ) (m : ZMod N → ZMod N → ℂ) (H : Finset (ZMod N)) :=
  ∀ h : H, NativeVectorCorrelation s N p (nativeCrossResidual f₀ f₁ m h.val)

namespace NativeCrossWitnesses

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p q : ℝ} {f₀ f₁ : ZMod N → ℂ}
  {m : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)}
  (U : NativeCrossWitnesses s N p f₀ f₁ m H)

noncomputable def product (h : H) (x : ZMod N) : ℂ :=
  m h.val x * (U h).test.evalCyclic N (fun _ => x)

noncomputable def extension (h x : ZMod N) : ℂ :=
  if hh : h ∈ H then U.product ⟨h, hh⟩ x else 0

theorem extension_of_mem (h : ZMod N) (hh : h ∈ H) (x : ZMod N) :
    U.extension h x = U.product ⟨h, hh⟩ x := by
  simp only [extension, dite_eq_left hh]

theorem extension_of_not_mem (h : ZMod N) (hh : h ∉ H) (x : ZMod N) :
    U.extension h x = 0 := by
  simp only [extension, dite_eq_right hh]

theorem product_norm (hm : ∀ h x, ‖m h x‖ ≤ 1) (h : H) (x : ZMod N) :
    ‖U.product h x‖ ≤ Real.exp p := by
  have hT := (U h).test.eval_budget (U h).complexity (fun _ : Unit => (x.val : ℤ))
  change ‖(U h).test.evalCyclic N (fun _ => x)‖ ≤ Real.exp p at hT
  rw [product, norm_mul]
  simpa only [one_mul] using mul_le_mul (hm h.val x) hT (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem extension_norm (hm : ∀ h x, ‖m h x‖ ≤ 1) (h x : ZMod N) :
    ‖U.extension h x‖ ≤ Real.exp p := by
  by_cases hh : h ∈ H
  · rw [U.extension_of_mem h hh]
    exact U.product_norm hm ⟨h, hh⟩ x
  · rw [U.extension_of_not_mem h hh, norm_zero]
    exact Real.exp_nonneg _

theorem product_correlation (h : H) :
    Real.exp (-p) ≤
      ‖𝔼 x, (f₀ x * star (f₁ (x + h.val))) * star (U.product h x)‖ := by
  simpa only [product, nativeCrossResidual, star_mul, mul_assoc, mul_left_comm, mul_comm]
    using (U h).correlation

noncomputable def mono (hpq : p ≤ q) : NativeCrossWitnesses s N q f₀ f₁ m H :=
  fun h => (U h).mono hpq

end NativeCrossWitnesses

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_native_two_unit_comparison {A I J : Type*} [Fintype I] [Fintype J]
    {degree N : ℕ} [NeZero N] {p q r : ℝ}
    (f : A → ZMod N → ℂ) (v a : I → ZMod N → ℂ) (b : J → ZMod N → ℂ)
    (ha : ∀ x, ∑ i, ‖a i x‖ ^ 2 = 1) (hb : ∀ x, ∑ j, ‖b j x‖ ^ 2 = 1)
    (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hI : (Fintype.card I : ℝ) ≤ Real.exp q) (hJ : (Fintype.card J : ℝ) ≤ Real.exp r)
    (W : NativeVectorCorrelation degree N p (fun ai : A × I => fun x => f ai.1 x * star (v ai.2 x))) :
    Nonempty (NativeVectorCorrelation degree N (p + q + r)
      (fun aij : A × ((I × I) × (I × J)) => fun x =>
        f aij.1 x * star (b aij.2.2.2 x) *
          star (v aij.2.1.1 x * star (a aij.2.1.2 x)) *
          star (a aij.2.2.1 x * star (b aij.2.2.2 x)))) := by
  classical
  let F (x : ZMod N) := f W.coordinate.1 x * star (W.test.evalCyclic N (fun _ => x))
  let P (j : I) (x : ZMod N) := star (a j x)
  let ψ (j : I) (_ : Unit) (x : ZMod N) := star (v W.coordinate.2 x * star (a j x))
  have hcorr : Real.exp (-p) ≤ ‖𝔼 x ∈ (Finset.univ : Finset (ZMod N)), F x * star (v W.coordinate.2 x)‖ := by
    simpa only [F, mul_assoc, mul_left_comm, mul_comm] using W.correlation
  obtain ⟨j, _, hj⟩ := exists_unit_expansion_correlation Finset.univ F
    (fun x => star (v W.coordinate.2 x)) P (fun (_ : I) (_ : Unit) => (1 : ℂ)) ψ
    (fun x _ => by simpa only [P, norm_star] using ha x)
    (fun j x _ => by simp only [P, ψ, star_star, star_mul, Fintype.sum_unique, one_mul, mul_comm])
    (Real.exp_pos (-p)) (Real.exp_pos q) (by norm_num : (0 : ℝ) < 1) hI (fun _ => by simp) hcorr
  have hfrac : Real.exp (-p) / (Real.exp q * 1) = Real.exp (-(p + q)) := by
    rw [mul_one, ← Real.exp_sub]
    congr 1
    ring
  rw [hfrac] at hj
  let F' (x : ZMod N) := F x * ψ j () x
  let P' (k : J) (x : ZMod N) := star (b k x)
  let ψ' (k : J) (_ : Unit) (x : ZMod N) := star (a j x * star (b k x))
  have hj' : Real.exp (-(p + q)) ≤
      ‖𝔼 x ∈ (Finset.univ : Finset (ZMod N)), F' x * star (a j x)‖ := by
    simpa only [F', P, mul_assoc, mul_left_comm, mul_comm] using hj
  obtain ⟨k, _, hk⟩ := exists_unit_expansion_correlation Finset.univ F'
    (fun x => star (a j x)) P' (fun (_ : J) (_ : Unit) => (1 : ℂ)) ψ'
    (fun x _ => by simpa only [P', norm_star] using hb x)
    (fun k x _ => by simp only [P', ψ', star_star, star_mul, Fintype.sum_unique, one_mul, mul_comm])
    (Real.exp_pos (-(p + q))) (Real.exp_pos r) (by norm_num : (0 : ℝ) < 1) hJ (fun _ => by simp) hj'
  have hfrac' : Real.exp (-(p + q)) / (Real.exp r * 1) = Real.exp (-(p + q + r)) := by
    rw [mul_one, ← Real.exp_sub]
    congr 1
    ring
  rw [hfrac'] at hk
  exact ⟨{
    L := W.L
    dim := W.dim
    model := W.model
    test := W.test
    complexity := W.complexity.mono (by linarith)
    coordinate := (W.coordinate.1, (W.coordinate.2, j), (j, k))
    correlation := by simpa only [F, F', P', ψ, ψ', mul_assoc, mul_left_comm, mul_comm] using hk
  }⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem le_productNiltestBudget {p : ℝ} (hp : 0 ≤ p) : p ≤ productNiltestBudget p := by
  apply le_trans _ (productNiltestBudget_geometry hp)
  nlinarith [sq_nonneg p]

namespace NativeVectorCorrelation

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_absorb {I J : Type*} {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d N : ℕ} [NeZero N] {p : ℝ} (D : RationalFilteredNilmanifold L s d)
    (T : J → D.Niltest (fun _ : Unit => 1)) (f : I → ZMod N → ℂ) (hp : 2 ≤ p)
    (hT : ∀ j, (T j).ComplexityLE p)
    (W : NativeVectorCorrelation s N p
      (fun ij : I × J => fun x => f ij.1 x * star ((T ij.2).evalCyclic N (fun _ => x)))) :
    Nonempty (NativeVectorCorrelation s N (productNiltestBudget p) f) := by
  have hp0 : 0 ≤ p := by linarith
  let K : Bool → Type := BoolLieFamily L W.L
  let dims : Bool → ℕ := fun b => Bool.rec W.dim d b
  let models : ∀ b, RationalFilteredNilmanifold (K b) s (dims b) := fun b => by
    cases b
    · exact W.model
    · exact D
  let tests : ∀ b, (models b).Niltest (fun _ : Unit => 1) := fun b => by
    cases b
    · exact W.test
    · exact T W.coordinate.2
  have htests : ∀ b, (tests b).ComplexityLE p := by
    intro b
    cases b
    · exact W.complexity
    · exact hT _
  have hcard : (Fintype.card Bool : ℝ) ≤ p := by
    simpa only [Fintype.card_bool, Nat.cast_ofNat] using hp
  let : FiniteDimensional ℚ (∀ b, K b) :=
    (RationalFilteredNilmanifold.productFinBasis models).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ b, K b))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ b, K b)) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ b, K b)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis models)
  let S := RationalFilteredNilmanifold.piNiltest models tests hp0 hcard htests
  have heval (x : ZMod N) : S.evalCyclic N (fun _ => x) =
      (T W.coordinate.2).evalCyclic N (fun _ => x) * W.test.evalCyclic N (fun _ => x) := by
    change (RationalFilteredNilmanifold.piNiltest models tests hp0 hcard htests).eval
      (fun _ : Unit => (x.val : ℤ)) = _
    rw [RationalFilteredNilmanifold.piNiltest_eval, Fintype.prod_bool]
    rfl
  refine ⟨{
    L := ∀ b, K b
    dim := _
    model := RationalFilteredNilmanifold.pi models
    test := S
    complexity := RationalFilteredNilmanifold.piNiltest_complexity models tests hp0 hcard htests
    coordinate := W.coordinate.1
    correlation := ?_
  }⟩
  have hcorr := (Real.exp_le_exp.mpr (neg_le_neg (le_productNiltestBudget hp0))).trans W.correlation
  simpa only [heval, star_mul, mul_assoc, mul_left_comm, mul_comm] using hcorr

end NativeVectorCorrelation

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace NativeVectorCorrelation

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

end NativeVectorCorrelation

end Erdos3

end

section

namespace Erdos3.NativeCrossWitnesses

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f₀ f₁ : ZMod N → ℂ}
  {m : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)}
  (U : NativeCrossWitnesses s N p f₀ f₁ m H)

noncomputable def lower (h : H) (x : ZMod N) : ℂ := (U h).test.evalCyclic N (fun _ => x)

end Erdos3.NativeCrossWitnesses

end

end OAI

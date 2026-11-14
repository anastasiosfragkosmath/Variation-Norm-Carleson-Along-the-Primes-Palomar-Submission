module

public import OAI.Combinatorics.Progressions.Estimates.AxisCompression
public import OAI.Combinatorics.Progressions.Estimates.ControlledAdaptedRebase
public import OAI.Combinatorics.Progressions.Estimates.SampledNativeModel
public import OAI.Combinatorics.Progressions.Estimates.WeightedSummandCorrelation
public import OAI.Combinatorics.Progressions.Dynamics.VerticalDecompositionBudget
public import OAI.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity
public import OAI.Combinatorics.Progressions.Geometry.BoxDetectionExponents
public import OAI.Combinatorics.Progressions.Nilpotent.NiltestVerticalBounds

/-!
# The start of the type I / II iteration

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). Input: a
one-variable niltest `T` on a rational filtered nilmanifold of an arbitrary degree `deg`,
correlating with a function `f` on a finite set `Q ⊆ ℤ`. Output (the zero-frequency branch
included): either a `LengStart`, the data the engine `exists_translated_step_drop` needs (adapted
basis with weights `omega`, a vertical character `η` of the top layer, `η ≠ 0` on the top layer), or
a top-layer invariant niltest, in which case the iteration descends to degree `deg - 1` without
calling the engine (the engine is vacuous when `η` kills the top layer).

* `LengStart`: the packaged state (the field `omega` is the basis weight; it is not called `w`,
  which would clash with the niltest weight `fun _ : Unit => 1`), with `LengStart.mono` (raise the
  complexity) and `LengStart.nonneg`;
* `realifyFunctional_eq_zero_of_mem_subgroup`: a frequency killing `layer deg` has zero character
  on the top real layer;
* `exists_leng_start_or_top_invariant`: vertical decomposition
  (`Niltest.exists_vertical_decomposition_preserving_bounds`), pigeonhole of the correlation to one
  frequency (`exists_correlating_summand`), then either the top-invariant branch or the adapted
  rebase (`exists_controlled_adapted_rebase`: decompose first, then rebase) producing the
  `LengStart`;
* `exists_leng_start`: the same from the quantitative `U³` inverse theorem
  `exists_native_inverse_on_cyclic_encoding 2` (`σ = Unit`);
* `intervalPoints`, `reflectsPairSums_intervalPoints`, `exists_leng_start_interval`: the
  encoding of `{1, …, N}` (modulus `2 N`, density `1 / 2`, `q = 1`) and the resulting statement
  for the interval.

Used as the entry of the type I / II iteration of [F+] Prop 3.1 via Leng's `t:mobiusuniformity`
(arXiv:2312.10772v5 TeX L1183-L1262).
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3 OAI.Erdos3.CircleFourier
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- The state of the iteration at a model of degree `deg`: a one-variable niltest `T` of
complexity `p` on a rational filtered nilmanifold, with an adapted basis (weights `omega`,
`hF`), a rational vertical character `η` of height `≤ p` on the top layer, nonzero on the top
layer, and correlating with `f` on `Q`. -/
structure LengStart (deg : ℕ) (Q : Finset (Unit → ℤ)) (f : (Unit → ℤ) → ℂ) (p : ℝ) where
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
  /-- The rational filtered nilmanifold. -/
  D : RationalFilteredNilmanifold L deg dim
  /-- The weights of the adapted basis `D.basis`. -/
  omega : Fin dim → ℕ
  /-- The basis is adapted to the filtration. -/
  hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ omega i})
  /-- The niltest. -/
  T : D.Niltest (fun _ : Unit => 1)
  /-- The vertical frequency. -/
  η : L →ₗ[ℚ] ℚ
  complexity : T.ComplexityLE p
  norm_le : T.normBound ≤ 1
  eta_height : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p
  vertical : ∀ z ∈ D.filtration.realification.subgroup deg, ∀ x,
    T.observable (z • x) =
      character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x
  /-- A nonzero top frequency (the engine is vacuous otherwise). -/
  eta_ne : ∃ z ∈ D.filtration.layer deg, η z ≠ 0
  corr : Real.exp (-p) ≤ ‖𝔼 x ∈ Q, f x * star (T.eval x)‖

-- The instance fields of `LengStart` are instances (globally, so that consumers of a
-- `LengStart` need no local attribute).
attribute [instance] LengStart.lie LengStart.algebra LengStart.topology
  LengStart.topologicalAdd LengStart.continuousSMul LengStart.hausdorff

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace LengStart

variable {deg : ℕ} {Q : Finset (Unit → ℤ)} {f : (Unit → ℤ) → ℂ} {p q : ℝ}

/-- The complexity of a `LengStart` is nonnegative. -/
theorem nonneg (S : LengStart deg Q f p) : 0 ≤ p :=
  (Nat.cast_nonneg S.dim).trans S.complexity.1.1

/-- A `LengStart` at complexity `p` is one at every larger complexity `q`. -/
def mono (S : LengStart deg Q f p) (hpq : p ≤ q) : LengStart deg Q f q where
  L := S.L
  dim := S.dim
  D := S.D
  omega := S.omega
  hF := S.hF
  T := S.T
  η := S.η
  complexity := S.complexity.mono hpq
  norm_le := S.norm_le
  eta_height := fun i => (S.eta_height i).trans hpq
  vertical := S.vertical
  eta_ne := S.eta_ne
  corr := (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans S.corr

end LengStart

section Zero

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {deg d : ℕ}

/-- A frequency `η` killing the top layer `layer deg` has zero real functional on the top real
layer, so the vertical character of the top layer is trivial. -/
theorem realifyFunctional_eq_zero_of_mem_subgroup (D : RationalFilteredNilmanifold L deg d)
    (η : L →ₗ[ℚ] ℚ) (hη : ∀ z ∈ D.filtration.layer deg, η z = 0) (z : D.RealGroup)
    (hz : z ∈ D.filtration.realification.subgroup deg) :
    realifyFunctional η z.coord = 0 := by
  have hle : D.filtration.layer deg ≤ LinearMap.ker η := fun v hv => hη v hv
  exact (mem_realified_frequency_kernel_iff η z.coord).mp (Submodule.baseChange_mono ℝ hle hz)

end Zero

section B0

open Module

/-- **The start step, with the zero-frequency branch.** A one-variable niltest `T` of complexity
`p`, norm at most one, on a model of arbitrary degree `deg`, correlating with a 1-bounded `f` on
`Q`, gives either a `LengStart` at complexity `(p + C) ^ C`, or a niltest `T'` of complexity
`(p + C) ^ C` on the same model that is invariant under the top layer (frequency zero) and still
correlates with `f`. Proof: vertical decomposition with error `e^{-p}/2`, pigeonhole of the
correlation to one summand, then the dichotomy "`η` kills the top layer" against the adapted
rebase. -/
theorem exists_leng_start_or_top_invariant :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L] {deg d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L deg d) (Q : Finset (Unit → ℤ))
      (f : (Unit → ℤ) → ℂ), (∀ x ∈ Q, ‖f x‖ ≤ 1) →
      ∀ (T : D.Niltest (fun _ : Unit => 1)) {p : ℝ}, T.ComplexityLE p → T.normBound ≤ 1 →
      Real.exp (-p) ≤ ‖𝔼 x ∈ Q, f x * star (T.eval x)‖ →
      Nonempty (LengStart deg Q f ((p + C) ^ C)) ∨
      ∃ T' : D.Niltest (fun _ : Unit => 1),
        T'.ComplexityLE ((p + C) ^ C) ∧ T'.normBound ≤ 1 ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 x ∈ Q, f x * star (T'.eval x)‖ ∧
        ∀ z ∈ D.filtration.realification.subgroup deg, ∀ x,
          T'.observable (z • x) = T'.observable x := by
  obtain ⟨Cv, hCv, hvdb⟩ := exists_verticalDecompositionBudget_bound
  obtain ⟨Cr, hCr, hrebase⟩ := RationalFilteredNilmanifold.exists_controlled_adapted_rebase
  obtain ⟨C, hC, hbud⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + 1 + (Polynomial.X + 1 + Polynomial.C Cv) ^ Cv + Polynomial.C Cr) ^ Cr)
  refine ⟨C, hC, ?_⟩
  intro L _ _ deg d _ _ _ _ D Q f hf T p hT hnorm hcorr
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hT.1.1
  have hp1 : 0 ≤ p + 1 := by linarith
  have hQ : Q.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hcorr
    simp only [Finset.expect_empty, norm_zero] at hcorr
    exact absurd hcorr (not_le.mpr (Real.exp_pos _))
  -- the budget `P₁` after the vertical decomposition
  set v := verticalDecompositionBudget (p + 1) with hv
  have hv0 : 0 ≤ v := verticalDecompositionBudget_nonneg hp1
  set P₁ := p + 1 + v with hP₁
  have hP₁0 : 0 ≤ P₁ := by linarith
  have hP₁C : P₁ + Cr ≤ p + 1 + (p + 1 + Cv) ^ Cv + Cr := by
    have := hvdb (p + 1) hp1
    linarith
  have hfinal : (P₁ + Cr) ^ Cr ≤ (p + C) ^ C := by
    have h := hbud p hp
    have h' : (p + 1 + (p + 1 + (Cv : ℝ)) ^ Cv + Cr) ^ Cr ≤ (p + C) ^ C := by
      simpa [Polynomial.eval₂_pow] using h
    exact (pow_le_pow_left₀ (by positivity) hP₁C Cr).trans h'
  have hP₁fin : P₁ ≤ (p + C) ^ C :=
    ((le_add_of_nonneg_right (Nat.cast_nonneg Cr)).trans (le_self_pow₀ (by
      have : (0 : ℝ) ≤ Cr := Nat.cast_nonneg Cr
      have h2 : (1 : ℝ) ≤ 2 := by norm_num
      have hCr' : (2 : ℝ) ≤ Cr := by exact_mod_cast hCr
      linarith) (by omega))).trans hfinal
  -- vertical decomposition
  have hrho : (Real.exp (-p) / 2)⁻¹ ≤ Real.exp (p + 1) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * Real.exp p := by rw [inv_div]; simp [Real.exp_neg]
      _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg p)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨J, inst, hdecomp⟩ := T.exists_vertical_decomposition_preserving_bounds hp1
    (hT.mono (by linarith)) (half_pos (Real.exp_pos (-p))) hrho
  let _ := inst
  obtain ⟨η, U, hcard, hheight, hU, hvert, -, -, herr⟩ := hdecomp
  -- pigeonhole
  obtain ⟨j, hj⟩ := exists_correlating_summand hQ f T.eval (fun j => (U j).eval)
    (ρ := Real.exp (-p)) (M := Real.exp v) (Real.exp_pos _) (Real.exp_pos _) hcard hf
    (fun x _ => herr x) hcorr
  have hcorrj : Real.exp (-P₁) ≤ ‖𝔼 x ∈ Q, f x * star ((U j).eval x)‖ := by
    refine le_trans ?_ hj
    have h1 : Real.exp (-P₁) = Real.exp ((-p - v) - 1) := by rw [hP₁]; congr 1; ring
    have h2 : Real.exp (-p - v) / 2 = Real.exp (-p) / (2 * Real.exp v) := by
      rw [Real.exp_sub]; field_simp
    rw [h1, ← h2]
    exact exp_sub_one_le_half_exp _
  have hcorrj' : Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 x ∈ Q, f x * star ((U j).eval x)‖ :=
    le_trans (Real.exp_le_exp.mpr (neg_le_neg hP₁fin)) hcorrj
  have hUc : (U j).ComplexityLE P₁ := (hU j).1.mono (by linarith)
  have hnormj : (U j).normBound ≤ 1 := by rw [(hU j).2.2.1]; exact hnorm
  by_cases hη : ∀ z ∈ D.filtration.layer deg, η j z = 0
  · -- zero frequency: the niltest is invariant under the top layer
    right
    refine ⟨U j, hUc.mono hP₁fin, hnormj, hcorrj', ?_⟩
    intro z hz x
    rw [hvert j z hz x, realifyFunctional_eq_zero_of_mem_subgroup D (η j) hη z hz]
    simp
  · -- nonzero frequency: rebase to an adapted basis
    left
    push Not at hη
    obtain ⟨F, H, hH, -, -, hcomp, hfreq⟩ := hrebase D hP₁0
      (RationalFilteredNilmanifold.GeometryComplexityLE.mono D hT.1 (by linarith))
    refine ⟨{
      L := L
      dim := finrank ℚ L
      D := F.model
      omega := F.weight
      hF := F.model_layers
      T := F.rebaseNiltest H hH (U j)
      η := η j
      complexity := (hcomp (U j) hUc).mono hfinal
      norm_le := hnormj
      eta_height := fun i =>
        (hfreq (η j) (fun i => (hheight j i).trans (by linarith)) i).trans hfinal
      vertical := F.rebaseNiltest_vertical H hH (U j) (η j) (hvert j)
      eta_ne := hη
      corr := hcorrj' }⟩

end B0

section Initial

/-- **The initial `LengStart` from the `U³` inverse theorem** (`σ = Unit`, degree `2`). The
hypotheses are those of `exists_native_inverse_on_cyclic_encoding 2` (an encoding `φ` of `Q` into
`ℤ / N` reflecting pair sums, density `e^{-q}`); the glue to `Q = {1, …, N}` with the cyclic
encoding of modulus `2 N` is the transport of `Glue/Transport.lean`. Conclusion: a `LengStart` or
the top-invariant (zero frequency) branch, packaged as a `NativeSampleCorrelation` of degree `2`. -/
theorem exists_leng_start :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] (Q : Finset (Unit → ℤ)), Q.Nonempty →
      ∀ (φ : (Unit → ℤ) →+ ℤ),
      ReflectsPairSums ((Int.castAddHom (ZMod N)).comp φ) (Q : Set (Unit → ℤ)) →
      (∀ x ∈ Q, 0 ≤ φ x ∧ φ x < (N : ℤ)) →
      ∀ {p q : ℝ}, 2 ≤ p → 0 ≤ q → Real.exp (-q) ≤ (Q.card : ℝ) / (N : ℝ) →
      ∀ f : (Unit → ℤ) → ℂ, (∀ x ∈ Q, ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ finiteSupportGowersNorm 3 Q f →
      Nonempty (LengStart 2 Q f ((p + q + C) ^ C)) ∨
      ∃ V : NativeSampleCorrelation (fun _ : Unit => 1) 2 ((p + q + C) ^ C) Q id f,
        V.test.normBound ≤ 1 ∧
        ∀ z ∈ V.model.filtration.realification.subgroup 2, ∀ x,
          V.test.observable (z • x) = V.test.observable x := by
  obtain ⟨C₀, hC₀, hinv⟩ := exists_native_inverse_on_cyclic_encoding 2 (by norm_num)
  obtain ⟨C₁, hC₁, hB0⟩ := exists_leng_start_or_top_invariant
  obtain ⟨C, hC, hbud⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + Polynomial.C C₀) ^ C₀ + Polynomial.C C₁) ^ C₁)
  refine ⟨C, hC, ?_⟩
  intro N _ Q hQ φ hφ hφN p q hp hq hden f hf hG
  obtain ⟨V, hVn⟩ := hinv Q hQ φ hφ hφN hp hq hden f hf hG
  have hfinal : (((p + q + C₀) ^ C₀ + C₁) ^ C₁ : ℝ) ≤ (p + q + C) ^ C := by
    have h := hbud (p + q) (by linarith)
    simpa [Polynomial.eval₂_pow] using h
  rcases hB0 V.model Q f hf V.test V.complexity hVn V.correlation with
    hS | ⟨T', hc, hn, hcorr, hinvar⟩
  · obtain ⟨S⟩ := hS
    exact Or.inl ⟨S.mono hfinal⟩
  · exact Or.inr ⟨{
      L := V.L
      dim := V.dim
      model := V.model
      test := T'
      complexity := hc.mono hfinal
      correlation := (Real.exp_le_exp.mpr (neg_le_neg hfinal)).trans hcorr }, hn, hinvar⟩

end Initial

section Interval

/-- The interval `{1, …, N}` as a finite set of one-variable integer points. -/
def intervalPoints (N : ℕ) : Finset (Unit → ℤ) :=
  (Finset.Icc (1 : ℤ) N).image (fun n _ => n)

/-- Membership in `intervalPoints N`. -/
theorem mem_intervalPoints {N : ℕ} {x : Unit → ℤ} :
    x ∈ intervalPoints N ↔ 1 ≤ x () ∧ x () ≤ N := by
  simp only [intervalPoints, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact hn
  · intro h
    exact ⟨x (), h, funext fun _ => rfl⟩

/-- The cardinality of `intervalPoints N`. -/
theorem card_intervalPoints (N : ℕ) : (intervalPoints N).card = N := by
  rw [intervalPoints, Finset.card_image_of_injective _ (fun a b h => congrFun h ())]
  simp

/-- The evaluation at the unique point of `Unit`, reduced modulo `2 N`, reflects pair sums on
`{1, …, N}` (the sums lie in `[2, 2 N]`, a window of length `2 N - 1`). -/
theorem reflectsPairSums_intervalPoints (N : ℕ) :
    ReflectsPairSums ((Int.castAddHom (ZMod (2 * N))).comp
      (Pi.evalAddMonoidHom (fun _ : Unit => ℤ) ())) (intervalPoints N : Set (Unit → ℤ)) := by
  intro a ha b hb c hc d hd h
  simp only [Finset.mem_coe, mem_intervalPoints] at ha hb hc hd
  simp only [AddMonoidHom.comp_apply, Int.coe_castAddHom, Pi.evalAddMonoidHom_apply] at h
  have h' : ((a () + b () : ℤ) : ZMod (2 * N)) = ((c () + d () : ℤ) : ZMod (2 * N)) := by
    push_cast
    exact h
  have hmod := (ZMod.intCast_eq_intCast_iff _ _ (2 * N)).mp h'
  have hN : ((2 * N : ℕ) : ℤ) = 2 * N := by push_cast; ring
  rw [hN] at hmod
  have heq : a () + b () = c () + d () := by
    obtain ⟨k, hk⟩ := Int.ModEq.dvd hmod
    have hk' : c () + d () - (a () + b ()) = 2 * N * k := by
      simpa using hk
    have hk1 : k = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · nlinarith
      · nlinarith
    rw [hk1] at hk'
    linarith
  funext i
  cases i
  have := heq
  simp only [Pi.add_apply]
  exact this

/-- **`exists_leng_start` on the interval `{1, …, N}`** (modulus `2 N`, density `1 / 2 ≥ e^{-1}`,
`q = 1`): a `LengStart` of degree `2` at complexity `(p + 1 + C) ^ C`, or the zero-frequency branch.
The remaining glue to the statement is the transport of
`finiteSupportGowersNorm 3 (intervalPoints N)` to the interval Gowers norm
(`Glue/Transport.lean`). -/
theorem exists_leng_start_interval :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ}, 1 ≤ N → ∀ {p : ℝ}, 2 ≤ p → ∀ f : (Unit → ℤ) → ℂ,
      (∀ x ∈ intervalPoints N, ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ finiteSupportGowersNorm 3 (intervalPoints N) f →
      Nonempty (LengStart 2 (intervalPoints N) f ((p + 1 + C) ^ C)) ∨
      ∃ V : NativeSampleCorrelation (fun _ : Unit => 1) 2 ((p + 1 + C) ^ C)
          (intervalPoints N) id f,
        V.test.normBound ≤ 1 ∧
        ∀ z ∈ V.model.filtration.realification.subgroup 2, ∀ x,
          V.test.observable (z • x) = V.test.observable x := by
  obtain ⟨C, hC, h⟩ := exists_leng_start
  refine ⟨C, hC, ?_⟩
  intro N hN p hp f hf hG
  have : NeZero (2 * N) := ⟨by omega⟩
  have hne : (intervalPoints N).Nonempty := by
    refine ⟨fun _ => 1, mem_intervalPoints.mpr ⟨le_rfl, by exact_mod_cast hN⟩⟩
  have hbound : ∀ x ∈ intervalPoints N,
      0 ≤ (Pi.evalAddMonoidHom (fun _ : Unit => ℤ) ()) x ∧
        (Pi.evalAddMonoidHom (fun _ : Unit => ℤ) ()) x < ((2 * N : ℕ) : ℤ) := by
    intro x hx
    obtain ⟨h1, h2⟩ := mem_intervalPoints.mp hx
    simp only [Pi.evalAddMonoidHom_apply]
    push_cast
    constructor <;> omega
  have hden : Real.exp (-1) ≤ ((intervalPoints N).card : ℝ) / ((2 * N : ℕ) : ℝ) := by
    rw [card_intervalPoints]
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have h2 : ((N : ℝ)) / ((2 * N : ℕ) : ℝ) = 1 / 2 := by
      push_cast
      field_simp
    rw [h2, Real.exp_neg]
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc (Real.exp 1)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) he
      _ = 1 / 2 := by norm_num
  exact h (N := 2 * N) (intervalPoints N) hne _ (reflectsPairSums_intervalPoints N) hbound
    (q := 1) hp (by norm_num) hden f hf hG

end Interval

end PrimeCarleson.Proof.Fplus31

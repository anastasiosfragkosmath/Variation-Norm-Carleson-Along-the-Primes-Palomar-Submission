/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/CommonIntegralModelEquivalences.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.LinearMapIntegralCover
public import OAI.Combinatorics.Progressions.Geometry.CommonRationalModelCoordinates
public import OAI.Combinatorics.Progressions.Linear.BoundedSpanningPadding
public import OAI.Combinatorics.Progressions.Linear.ReducedSquareFastKernel
public import OAI.Combinatorics.Progressions.Linear.SynchronizeSplittingProjection
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module

variable {α ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  (e : Basis ι ℚ L) (S : Finset α) (hS : S.Nonempty) (K : α → LieSubalgebra ℚ L)

include hS in
theorem exists_common_height_bounded_subalgebra (m : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hK : ∀ a ∈ S, K a ∈ heightBoundedLieSubalgebras e m ⌈Real.exp A⌉₊) :
    ∃ a₀ ∈ S, ∃ T : Finset α, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, K a = K a₀) ∧
      Real.exp (-(3 * (m : ℝ) * Fintype.card ι * (A + 2))) * S.card ≤ (T.card : ℝ) := by
  obtain ⟨U, _, T, hTS, hT, hU, hlarge⟩ := exists_exponential_constant_fiber S hS K
    (heightBoundedLieSubalgebras e m ⌈Real.exp A⌉₊)
    (finite_card_heightBoundedLieSubalgebras e m ⌈Real.exp A⌉₊).1 hK
    (heightBoundedLieSubalgebras_ncard_exp_bound e m hA)
  obtain ⟨a₀, ha₀⟩ := hT
  exact ⟨a₀, hTS ha₀, T, hTS, ha₀, fun a ha => (hU a ha).trans (hU a₀ ha₀).symm, hlarge⟩

include hS in
theorem exists_common_log_height_subalgebra (m : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hK : ∀ a ∈ S, ∃ v : Fin m → L,
      Submodule.span ℚ (Set.range v) = (K a).toSubmodule ∧
        ∀ i j, rationalLogHeight (e.repr (v i) j) ≤ A) :
    ∃ a₀ ∈ S, ∃ T : Finset α, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, K a = K a₀) ∧
      Real.exp (-(3 * (m : ℝ) * Fintype.card ι * (A + 2))) * S.card ≤ (T.card : ℝ) := by
  apply exists_common_height_bounded_subalgebra e S hS K m hA
  intro a ha
  obtain ⟨v, hv, hh⟩ := hK a ha
  exact (mem_heightBoundedSubspaces e m ⌈Real.exp A⌉₊ (K a).toSubmodule).mpr
    ⟨v, hv, fun i j => rationalHeightLE_ceil_exp (hh i j)⟩

theorem common_subalgebra_cost_le_budget (m d : ℕ) {A p : ℝ} (hp : 0 ≤ p)
    (hm : (m : ℝ) ≤ p) (hd : (d : ℝ) ≤ p) (hA : 0 ≤ A) (hAp : A ≤ p) :
    3 * (m : ℝ) * d * (A + 2) ≤ (p + 2) ^ 5 := by
  have hm' : (m : ℝ) ≤ p + 2 := by linarith
  have hd' : (d : ℝ) ≤ p + 2 := by linarith
  calc
    _ ≤ 3 * (p + 2) * (p + 2) * (p + 2) := by gcongr
    _ = 3 * (p + 2) ^ 3 := by ring
    _ ≤ (p + 2) ^ 2 * (p + 2) ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    _ = (p + 2) ^ 5 := by ring

include hS in
theorem exists_common_fast_subalgebra (m : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hm : (m : ℝ) ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hK : ∀ a ∈ S, ∃ v : Fin m → L,
      Submodule.span ℚ (Set.range v) = (K a).toSubmodule ∧
        ∀ i j, rationalLogHeight (e.repr (v i) j) ≤ p) :
    ∃ a₀ ∈ S, ∃ T : Finset α, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, K a = K a₀) ∧
      Real.exp (-((p + 2) ^ 5)) * S.card ≤ (T.card : ℝ) := by
  obtain ⟨a₀, ha₀, T, hTS, haT, hcommon, hlarge⟩ :=
    exists_common_log_height_subalgebra e S hS K m hp hK
  refine ⟨a₀, ha₀, T, hTS, haT, hcommon, ?_⟩
  apply le_trans _ hlarge
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (common_subalgebra_cost_le_budget m (Fintype.card ι) hp hm hd hp le_rfl)

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {α σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (e : Basis ι ℚ (F.squareFiltration.PolynomialSymbol w))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

theorem exists_common_bounded_moduli {G κ : Type*} [Fintype κ]
    (S : Finset G) (hS : S.Nonempty) (moduli : G → κ → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hmoduli : ∀ a ∈ S, ∀ i, (moduli a i : ℝ) ≤ Real.exp p) :
    ∃ a₀ ∈ S, ∃ T : Finset G, T ⊆ S ∧ a₀ ∈ T ∧
      (∀ a ∈ T, moduli a = moduli a₀) ∧
      Real.exp (-((p + 1) * Fintype.card κ)) * S.card ≤ (T.card : ℝ) := by
  classical
  let N := ⌊Real.exp p⌋₊
  let tag : G → κ → Fin (N + 1) := fun a i =>
    ⟨min (moduli a i) N, (min_le_right _ _).trans_lt (Nat.lt_succ_self _)⟩
  have htag : ∀ a ∈ S, ∀ i, (tag a i).val = moduli a i := by
    intro a ha i
    exact min_eq_left (Nat.le_floor (hmoduli a ha i))
  have hbase : ((N + 1 : ℕ) : ℝ) ≤ Real.exp (p + 1) := by
    have h1 : 1 ≤ Real.exp p := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hp
    have h2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    rw [Nat.cast_add, Nat.cast_one]
    calc
      (N : ℝ) + 1 ≤ Real.exp p + Real.exp p :=
        add_le_add (Nat.floor_le (Real.exp_pos p).le) h1
      _ = Real.exp p * 2 := by ring
      _ ≤ Real.exp p * Real.exp 1 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos p).le
      _ = _ := (Real.exp_add p 1).symm
  have hcount : ((Set.univ : Set (κ → Fin (N + 1))).ncard : ℝ) ≤
      Real.exp ((p + 1) * Fintype.card κ) := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp (p + 1) ^ Fintype.card κ := pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  obtain ⟨q, _, T, hTS, hT, hconstant, hlarge⟩ := exists_exponential_constant_fiber
    S hS tag Set.univ Set.finite_univ (fun _ _ => Set.mem_univ _) hcount
  obtain ⟨a₀, ha₀⟩ := hT
  refine ⟨a₀, hTS ha₀, T, hTS, ha₀, ?_, hlarge⟩
  intro a ha
  funext i
  have h := congrArg (fun f : κ → Fin (N + 1) => (f i).val)
    ((hconstant a ha).trans (hconstant a₀ ha₀).symm)
  simpa only [htag a (hTS ha) i, htag a₀ (hTS ha₀) i] using h

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {α σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (e : Basis ι ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

theorem exists_common_positive_nat {α : Type*} (S : Finset α) (hS : S.Nonempty)
    (n : α → ℕ) {p : ℝ} (hn : ∀ a ∈ S, 0 < n a ∧ (n a : ℝ) ≤ Real.exp p) :
    ∃ a₀ ∈ S, ∃ T : Finset α, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, n a = n a₀) ∧
      Real.exp (-p) * S.card ≤ (T.card : ℝ) := by
  let A := Finset.Icc 1 ⌊Real.exp p⌋₊
  have hA : ((A : Set ℕ).ncard : ℝ) ≤ Real.exp p := by
    simpa only [A, Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel] using
      (Nat.floor_le (Real.exp_nonneg p))
  obtain ⟨k, _, T, hTS, hT, hk, hlarge⟩ := exists_exponential_constant_fiber S hS n
    (A : Set ℕ) A.finite_toSet
    (fun a ha => Finset.mem_Icc.mpr ⟨(hn a ha).1, Nat.le_floor (hn a ha).2⟩) hA
  obtain ⟨a₀, ha₀⟩ := hT
  exact ⟨a₀, hTS ha₀, T, hTS, ha₀, fun a ha => (hk a ha).trans (hk a₀ ha₀).symm, hlarge⟩

theorem exists_common_fast_subalgebra_and_denominator
    {α ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (e : Basis ι ℚ L) (S : Finset α) (hS : S.Nonempty)
    (K : α → LieSubalgebra ℚ L) (n : α → ℕ) (m : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hK : ∀ a ∈ S, ∃ v : Fin m → L,
      Submodule.span ℚ (Set.range v) = (K a).toSubmodule ∧
        ∀ i j, rationalLogHeight (e.repr (v i) j) ≤ p)
    (hn : ∀ a ∈ S, 0 < n a ∧ (n a : ℝ) ≤ Real.exp p) :
    ∃ a₀ ∈ S, ∃ T : Finset α, T ⊆ S ∧ a₀ ∈ T ∧
      (∀ a ∈ T, K a = K a₀ ∧ n a = n a₀) ∧
      Real.exp (-((p + 2) ^ 5 + p)) * S.card ≤ (T.card : ℝ) := by
  obtain ⟨b, _, U, hUS, hbU, hKsame, hUlarge⟩ :=
    exists_common_fast_subalgebra e S hS K m hp hm hd hK
  obtain ⟨a₀, haU, T, hTU, haT, hnsame, hTlarge⟩ :=
    exists_common_positive_nat U ⟨b, hbU⟩ n (fun a ha => hn a (hUS ha))
  refine ⟨a₀, hUS haU, T, hTU.trans hUS, haT, ?_, ?_⟩
  · intro a ha
    exact ⟨(hKsame a (hTU ha)).trans (hKsame a₀ haU).symm, hnsame a ha⟩
  · calc
      Real.exp (-((p + 2) ^ 5 + p)) * S.card =
          Real.exp (-p) * (Real.exp (-((p + 2) ^ 5)) * S.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-p) * U.card := mul_le_mul_of_nonneg_left hUlarge (Real.exp_pos _).le
      _ ≤ T.card := hTlarge

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

theorem exists_common_integral_models (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G : Type*} {L : G → Type*}
      [∀ h, LieRing (L h)] [∀ h, LieAlgebra ℚ (L h)] {d : ℕ}
      (D : ∀ h, RationalFilteredNilmanifold (L h) s d) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h, (D h).GeometryComplexityLE p) →
      ∃ (B : G → ℕ) (Λ : ∀ h, Subgroup (D h).filtration.Group)
        (hB : ∀ h, 0 < B h)
        (hin : ∀ h, scaledIntegerGrid (B h) ⊆ bchSubgroupCoordinates (D h).basis (Λ h))
        (hout : ∀ h, bchSubgroupCoordinates (D h).basis (Λ h) ⊆ denominatorGrid (B h)),
        (∀ h, (B h : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ Λ h ≤ (D h).lattice ∧
          bchSubgroupCoordinates (D h).basis (Λ h) = scaledIntegerGrid (B h) ∧
          ((D h).withLattice (Λ h) (B h) (hB h) (hin h) (hout h)).GeometryComplexityLE ((p + C) ^ C)) ∧
        ∃ h₀ ∈ H, ∃ H' : Finset G, H' ⊆ H ∧ h₀ ∈ H' ∧
          (∀ h ∈ H', B h = B h₀ ∧ (D h).rationalModelCoordinates = (D h₀).rationalModelCoordinates) ∧
          Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) := by
  classical
  obtain ⟨c, _, hcover⟩ := exists_native_integral_model_cover s
  obtain ⟨k, _, hmodel⟩ := exists_common_rational_model_power s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C c) ^ c + (X + Polynomial.C k) ^ k + X)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ d D H hH p hp hD
  let q := (p + c) ^ c
  let r := (p + k) ^ k
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hbud : q + r + p ≤ (p + C) ^ C := by
    simpa [q, r, X, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hqrC : q + r ≤ (p + C) ^ C := by linarith
  choose B Λ hB hin hout hBb hΛ hcoords hgeom using fun h => hcover (D h) hp (hD h)
  obtain ⟨h₁, _, H₁, hsub₁, hh₁, hcodes, hlarge₁⟩ :=
    hmodel D H hH hp (fun h _ => hD h)
  obtain ⟨h₀, hh₀, H', hsub₂, hh₀', hmoduli, hlarge₂⟩ :=
    exists_common_positive_nat H₁ ⟨h₁, hh₁⟩ B (p := q)
      (fun h _ => ⟨hB h, hBb h⟩)
  refine ⟨B, Λ, hB, hin, hout, ?_, h₀, hsub₁ hh₀, H', hsub₂.trans hsub₁, hh₀', ?_, ?_⟩
  · intro h
    exact ⟨(hBb h).trans (Real.exp_le_exp.mpr hqC), hΛ h, hcoords h,
      (hgeom h).mono _ hqC⟩
  · intro h hh
    exact ⟨hmoduli h hh, (hcodes h (hsub₂ hh)).trans (hcodes h₀ hh₀).symm⟩
  · calc
      Real.exp (-((p + C) ^ C)) * H.card ≤ Real.exp (-(q + r)) * H.card :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqrC)) (Nat.cast_nonneg _)
      _ = Real.exp (-q) * (Real.exp (-r) * H.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-q) * H₁.card := mul_le_mul_of_nonneg_left hlarge₁ (Real.exp_pos _).le
      _ ≤ H'.card := hlarge₂

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

end Erdos3.RationalFilteredNilmanifold

end

end OAI

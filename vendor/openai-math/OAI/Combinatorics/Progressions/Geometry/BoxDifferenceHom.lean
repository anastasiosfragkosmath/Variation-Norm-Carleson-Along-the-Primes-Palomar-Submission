/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Geometry/BoxDifferenceHom.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.DenseProductApproximation
public import OAI.Combinatorics.Progressions.Polynomial.PhasePreservingCauchySchwarz
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem expect_prod_split {X Y M : Type*} [Fintype X] [Fintype Y]
    [AddCommMonoid M] [Module ℚ≥0 M] (F : X × Y → M) :
    (𝔼 p, F p) = 𝔼 x, 𝔼 y, F (x,y) := by
  simpa using (Finset.expect_product' (Finset.univ : Finset X)
    (Finset.univ : Finset Y) (fun x y => F (x,y)))

theorem expect_empty_tuple {X : Fin 0 → Type*} [∀ i, Fintype (X i)]
    {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M] (F : (∀ i, X i) → M) :
    (𝔼 x, F x) = F (fun i => Fin.elim0 i) := by
  calc
    (𝔼 x, F x) = 𝔼 _x : ∀ i, X i, F (fun i => Fin.elim0 i) := by
      apply Finset.expect_congr rfl
      intro x _
      congr 1
      exact Subsingleton.elim _ _
    _ = _ := Fintype.expect_const _

theorem expect_two_dependent_fin_cons {n : ℕ} {X : Fin (n+1) → Type*}
    [∀ i, Fintype (X i)] {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (F : (∀ i, X i) → (∀ i, X i) → M) :
    (𝔼 x, 𝔼 y, F x y) =
      𝔼 a : X 0, 𝔼 b : X 0, 𝔼 u : ∀ i : Fin n, X i.succ,
        𝔼 v : ∀ i : Fin n, X i.succ, F (Fin.cons a u) (Fin.cons b v) := by
  rw [expect_dependent_fin_cons]
  apply Finset.expect_congr rfl
  intro a _
  simp_rw [expect_dependent_fin_cons]
  exact Finset.expect_comm _ _ _

theorem expect_pow_two_pow_le {X : Type*} [Fintype X] [Nonempty X]
    (n : ℕ) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x, f x)^(2^n) ≤ 𝔼 x, (f x)^(2^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, pow_mul]
    calc
      ((𝔼 x, f x)^(2^n))^2 ≤ (𝔼 x, (f x)^(2^n))^2 :=
        pow_le_pow_left₀ (pow_nonneg (Finset.expect_nonneg (fun x _ => hf x)) _) ih 2
      _ ≤ 𝔼 x, ((f x)^(2^n))^2 := expect_square_le _

theorem expect_double_pow_two_pow_le {X Y : Type*}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (n : ℕ) (f : X → Y → ℝ) (hf : ∀ x y, 0 ≤ f x y) :
    (𝔼 x, 𝔼 y, f x y)^(2^n) ≤ 𝔼 x, 𝔼 y, (f x y)^(2^n) := by
  apply (expect_pow_two_pow_le n (fun x => 𝔼 y, f x y)
    (fun x => Finset.expect_nonneg (fun y _ => hf x y))).trans
  exact Finset.expect_le_expect (fun x _ => expect_pow_two_pow_le n (f x) (hf x))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteBoxCorrelation {X Y : Type*} [Fintype X] [Fintype Y]
    (F : X → Y → ℂ) : ℂ :=
  𝔼 x, 𝔼 x', 𝔼 y, 𝔼 y',
    F x y * star (F x' y) * star (F x y') * F x' y'

theorem finiteBoxCorrelation_re_eq_mean_square {X Y : Type*} [Fintype X] [Fintype Y]
    (F : X → Y → ℂ) :
    (finiteBoxCorrelation F).re = 𝔼 x, 𝔼 x', ‖𝔼 y, F x y * star (F x' y)‖ ^ 2 := by
  unfold finiteBoxCorrelation
  simp_rw [square_norm_mean_eq_cross_re, ← expect_re]
  congr 1
  apply Finset.expect_congr rfl
  intro x _
  apply Finset.expect_congr rfl
  intro x' _
  apply Finset.expect_congr rfl
  intro y _
  apply Finset.expect_congr rfl
  intro y' _
  simp only [star_mul, star_star]
  ring

theorem norm_weighted_expect_sq_le {X : Type*} [Fintype X] [Nonempty X]
    (a f : X → ℂ) (ha : ∀ x, ‖a x‖ ≤ 1) :
    ‖𝔼 x, a x * f x‖ ^ 2 ≤ 𝔼 x, ‖f x‖ ^ 2 := by
  have hcs := norm_expect_mul_star_sq_le a (fun x => star (f x))
  simp only [star_star, norm_star] at hcs
  have ha2 : (𝔼 x, ‖a x‖ ^ 2) ≤ 1 := by
    exact (Finset.expect_le_expect (fun x _ =>
      pow_le_pow_left₀ (norm_nonneg _) (ha x) 2)).trans_eq (by simp)
  exact hcs.trans ((mul_le_mul_of_nonneg_right ha2
    (Finset.expect_nonneg (fun _ _ => sq_nonneg _))).trans_eq (one_mul _))

theorem norm_weighted_pair_mean_pow_four_le_box {X Y : Type*}
    [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (F : X → Y → ℂ) (a : X → ℂ) (b : Y → ℂ)
    (ha : ∀ x, ‖a x‖ ≤ 1) (hb : ∀ y, ‖b y‖ ≤ 1) :
    ‖𝔼 x, 𝔼 y, F x y * a x * b y‖ ^ 4 ≤ (finiteBoxCorrelation F).re := by
  let m : ℂ := 𝔼 x, 𝔼 x', a x * star (a x') * (𝔼 y, F x y * star (F x' y))
  have hleft : (𝔼 y, b y * (𝔼 x, F x y * a x)) = 𝔼 x, 𝔼 y, F x y * a x * b y := by
    simp_rw [Finset.mul_expect]
    rw [Finset.expect_comm]
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro y _
    ring
  have hright : (𝔼 x, 𝔼 x', 𝔼 y, (F x y * a x) * star (F x' y * a x')) = m := by
    dsimp [m]
    simp_rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro x' _
    apply Finset.expect_congr rfl
    intro y _
    rw [map_mul]
    ring
  have hfirst : ‖𝔼 x, 𝔼 y, F x y * a x * b y‖ ^ 2 ≤ m.re := by
    simpa only [hleft, hright, one_pow, one_mul] using
      finite_family_cauchy_schwarz_re b (fun x y => F x y * a x) hb
  have hsecond : ‖m‖ ^ 2 ≤ 𝔼 x, 𝔼 x', ‖𝔼 y, F x y * star (F x' y)‖ ^ 2 := by
    have hh := norm_weighted_expect_sq_le
      (fun u : X × X => a u.1 * star (a u.2))
      (fun u : X × X => 𝔼 y, F u.1 y * star (F u.2 y)) (fun u => by
        rw [norm_mul, norm_star]
        exact (mul_le_of_le_one_left (norm_nonneg _) (ha _)).trans (ha _))
    simpa only [← Finset.univ_product_univ, Finset.expect_product, m] using hh
  have hm : 0 ≤ m.re := (sq_nonneg _).trans hfirst
  calc
    _ = (‖𝔼 x, 𝔼 y, F x y * a x * b y‖ ^ 2) ^ 2 := by ring
    _ ≤ m.re ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
    _ ≤ ‖m‖ ^ 2 := pow_le_pow_left₀ hm (Complex.re_le_norm m) 2
    _ ≤ _ := hsecond.trans_eq (finiteBoxCorrelation_re_eq_mean_square F).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def iteratedBoxDifference {Z : Type*} :
    (n : ℕ) → {X : Fin n → Type*} → ((∀ i, X i) → Z → ℂ) →
      (∀ i, X i) → (∀ i, X i) → Z → ℂ
  | 0, _, F, _, _, z => F (fun i => Fin.elim0 i) z
  | n+1, _, F, u, v, z => iteratedBoxDifference n
      (fun x z => F (Fin.cons (u 0) x) z * star (F (Fin.cons (v 0) x) z))
      (Fin.tail u) (Fin.tail v) z

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def boxSlice {X : Type*} (a z : Fin 2 → X) : Fin 4 → X := ![z 0, a 0, z 1, a 1]

def boxSliceEquiv (X : Type*) : ((Fin 2 → X) × (Fin 2 → X)) ≃ (Fin 4 → X) where
  toFun p := boxSlice p.1 p.2
  invFun x := (![x 1, x 3], ![x 0, x 2])
  left_inv p := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

theorem expect_boxSlice {X M : Type*} [Fintype X] [AddCommMonoid M] [Module ℚ≥0 M]
    (F : (Fin 4 → X) → M) :
    (𝔼 x, F x) = 𝔼 a : Fin 2 → X, 𝔼 z : Fin 2 → X, F (boxSlice a z) := by
  calc
    _ = 𝔼 p : (Fin 2 → X) × (Fin 2 → X), F (boxSlice p.1 p.2) :=
      (Fintype.expect_equiv (boxSliceEquiv X) _ F (fun _ => rfl)).symm
    _ = _ := by
      simpa using (Finset.expect_product' Finset.univ Finset.univ
        (fun a z => F (boxSlice a z)))

noncomputable def boxKernel {X : Type*} (K : X → X → ℂ) (x : Fin 4 → X) : ℂ :=
  K (x 0) (x 2) * star (K (x 1) (x 2)) * star (K (x 0) (x 3)) * K (x 1) (x 3)

noncomputable def boxAnchorFactor {X : Type*} (K : X → X → ℂ)
    (a z : Fin 2 → X) : ℂ :=
  star (K (a 0) (z 1)) * star (K (z 0) (a 1)) * K (a 0) (a 1)

theorem boxKernel_slice {X : Type*} (K : X → X → ℂ) (a z : Fin 2 → X) :
    boxKernel K (boxSlice a z) = K (z 0) (z 1) * boxAnchorFactor K a z := by
  simp [boxKernel, boxSlice, boxAnchorFactor, mul_assoc]

theorem boxKernel_mean {X : Type*} [Fintype X] (K : X → X → ℂ) :
    (𝔼 x : Fin 4 → X, boxKernel K x) = finiteBoxCorrelation K := by
  simp_rw [expect_fin_cons]
  unfold finiteBoxCorrelation
  apply Finset.expect_congr rfl
  intro x _
  apply Finset.expect_congr rfl
  intro a _
  apply Finset.expect_congr rfl
  intro y _
  apply Finset.expect_congr rfl
  intro b _
  change (𝔼 _ : Fin 0 → X, K x y * star (K a y) * star (K x b) * K a b) = _
  rw [Fintype.expect_const]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_box_anchor_correlation {X : Type*} [Fintype X] [Nonempty X]
    (K : X → X → ℂ) :
    ∃ a : Fin 2 → X, (finiteBoxCorrelation K).re ≤
      ‖𝔼 z : Fin 2 → X, K (z 0) (z 1) * boxAnchorFactor K a z‖ := by
  have hmean : (finiteBoxCorrelation K).re =
      𝔼 a : Fin 2 → X, (𝔼 z : Fin 2 → X,
        K (z 0) (z 1) * boxAnchorFactor K a z).re := by
    rw [← boxKernel_mean, expect_boxSlice, expect_re]
    simp_rw [boxKernel_slice]
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean.le
  exact ⟨a, ha.trans (Complex.re_le_norm _)⟩

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

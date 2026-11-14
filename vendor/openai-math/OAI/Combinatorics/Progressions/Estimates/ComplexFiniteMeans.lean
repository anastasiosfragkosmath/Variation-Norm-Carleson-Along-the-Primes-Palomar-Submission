/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/ComplexFiniteMeans.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib
@[expose] public section

namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem expect_fin_cons {G M : Type*} [Fintype G] [AddCommMonoid M] [Module ℚ≥0 M]
    {n : ℕ} (F : (Fin (n + 1) → G) → M) :
    (𝔼 x, F x) = 𝔼 a : G, 𝔼 y : Fin n → G, F (Fin.cons a y) := by
  calc
    (𝔼 x, F x) = 𝔼 p : G × (Fin n → G), F (Fin.cons p.1 p.2) := by
      apply Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n + 1) ↦ G)).symm
      intro x
      congr 1
      simp
    _ = _ := by
      simpa using (Finset.expect_product' (Finset.univ : Finset G)
        (Finset.univ : Finset (Fin n → G)) (fun a y ↦ F (Fin.cons a y)))

theorem norm_expect_mul_star_sq_le {Ω : Type*} [Fintype Ω] (f g : Ω → ℂ) :
    ‖𝔼 x, f x * star (g x)‖ ^ 2 ≤
      (𝔼 x, ‖f x‖ ^ 2) * (𝔼 x, ‖g x‖ ^ 2) := by
  have hnorm : ‖𝔼 x, f x * star (g x)‖ ≤ 𝔼 x, ‖f x‖ * ‖g x‖ := by
    simpa only [norm_mul, norm_star] using
      (RCLike.norm_expect_le (K := ℂ) (f := fun x ↦ f x * star (g x)))
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (Finset.expect_mul_sq_le_sq_mul_sq Finset.univ (fun x ↦ ‖f x‖) (fun x ↦ ‖g x‖))

theorem expect_square_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    (𝔼 x, f x) ^ 2 ≤ 𝔼 x, f x ^ 2 := by
  have h := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f (fun _ : Ω ↦ (1 : ℝ))
  simpa using h

theorem prod_bool_tuple_succ {M : Type*} [CommMonoid M] {n : ℕ}
    (F : (Fin (n + 1) → Bool) → M) :
    (∏ ω, F ω) =
      (∏ ω : Fin n → Bool, F (Fin.cons false ω)) *
        (∏ ω : Fin n → Bool, F (Fin.cons true ω)) := by
  calc
    (∏ ω, F ω) = ∏ q : Bool × (Fin n → Bool), F (Fin.cons q.1 q.2) := by
      apply Fintype.prod_equiv (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Bool)).symm
      intro ω
      simp
    _ = _ := by rw [Fintype.prod_prod_type]; simp [mul_comm]

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

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

theorem expect_prod_boolean_pow_le {Ω : Type*} [Fintype Ω]
    (n : ℕ) (F : (Fin n → Bool) → Ω → ℝ) (hF : ∀ ω x, 0 ≤ F ω x) :
    (𝔼 x, ∏ ω, F ω x) ^ (2 ^ n) ≤ ∏ ω, 𝔼 x, F ω x ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    let A (b : Bool) (x : Ω) := ∏ ω : Fin n → Bool, F (Fin.cons b ω) x
    have hprod (x : Ω) : (∏ ω, F ω x) = A false x * A true x :=
      prod_bool_tuple_succ _
    have hcs := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ (A false) (A true)
    have hpart (b : Bool) : (𝔼 x, A b x ^ 2) ^ (2 ^ n) ≤
        ∏ ω : Fin n → Bool, 𝔼 x, F (Fin.cons b ω) x ^ (2 ^ (n + 1)) := by
      have h := ih (fun ω x ↦ F (Fin.cons b ω) x ^ 2) (fun _ _ ↦ sq_nonneg _)
      simpa only [A, ← Finset.prod_pow, ← pow_mul, ← pow_succ'] using h
    calc
      (𝔼 x, ∏ ω, F ω x) ^ (2 ^ (n + 1)) =
          ((𝔼 x, A false x * A true x) ^ 2) ^ (2 ^ n) := by
        simp_rw [hprod]
        rw [← pow_mul, pow_succ']
      _ ≤ ((𝔼 x, A false x ^ 2) * (𝔼 x, A true x ^ 2)) ^ (2 ^ n) :=
        pow_le_pow_left₀ (sq_nonneg _) hcs _
      _ = (𝔼 x, A false x ^ 2) ^ (2 ^ n) * (𝔼 x, A true x ^ 2) ^ (2 ^ n) :=
        mul_pow _ _ _
      _ ≤ (∏ ω : Fin n → Bool, 𝔼 x, F (Fin.cons false ω) x ^ (2 ^ (n + 1))) *
          (∏ ω : Fin n → Bool, 𝔼 x, F (Fin.cons true ω) x ^ (2 ^ (n + 1))) := by
        apply mul_le_mul (hpart false) (hpart true)
        · exact pow_nonneg (Finset.expect_nonneg (fun _ _ ↦ sq_nonneg _)) _
        · exact Finset.prod_nonneg (fun ω _ ↦ Finset.expect_nonneg
            (fun x _ ↦ pow_nonneg (hF _ x) _))
      _ = ∏ ω, 𝔼 x, F ω x ^ (2 ^ (n + 1)) :=
        (prod_bool_tuple_succ (fun ω ↦ 𝔼 x, F ω x ^ (2 ^ (n + 1)))).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*}

variable [Fintype G] [DecidableEq G]

variable [AddCommGroup G]

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

theorem exists_common_slice_of_equal_marginals {A B H : Type*}
    [Fintype A] [Fintype B] [Fintype H] [Nonempty A] [Nonempty B] [Nonempty H]
    (f : A → H → ℝ) (g : B → H → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hmarginal : ∀ h, (𝔼 a, f a h) = 𝔼 b, g b h)
    (hmean : δ ≤ 𝔼 h, 𝔼 a, f a h) :
    ∃ (a : A) (b : B), δ ^ 2 ≤ 𝔼 h, f a h * g b h := by
  have henergy := (pow_le_pow_left₀ hδ hmean 2).trans
    (expect_square_le (fun h => 𝔼 a, f a h))
  have hproduct : (𝔼 h, (𝔼 a, f a h) ^ 2) = 𝔼 a, 𝔼 b, 𝔼 h, f a h * g b h := by
    calc
      _ = 𝔼 h, (𝔼 a, f a h) * (𝔼 b, g b h) := by
        apply Finset.expect_congr rfl
        intro h _
        rw [← hmarginal h, pow_two]
      _ = 𝔼 h, 𝔼 a, 𝔼 b, f a h * g b h := by simp_rw [Fintype.expect_mul_expect]
      _ = 𝔼 a, 𝔼 h, 𝔼 b, f a h * g b h := Finset.expect_comm _ _ _
      _ = _ := by
        apply Finset.expect_congr rfl
        intro a _
        exact Finset.expect_comm _ _ _
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty (henergy.trans_eq hproduct)
  obtain ⟨b, _, hb⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty ha
  exact ⟨a, b, hb⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

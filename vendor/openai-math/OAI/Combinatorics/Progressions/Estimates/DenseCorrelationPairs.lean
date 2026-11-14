/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/DenseCorrelationPairs.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Combinatorics.Pigeonhole
public import OAI.Combinatorics.Progressions.Estimates.ShiftTestingGowers
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_dense_level_set {H : Type*} [Fintype H] [Nonempty H]
    (f : H → ℝ) {a : ℝ} (ha : 0 ≤ a) (hf : ∀ h, f h ≤ 1) (hmean : a ≤ 𝔼 h, f h) :
    ∃ S : Finset H, a / 2 * Fintype.card H ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, a / 2 ≤ f h := by
  classical
  let S := Finset.univ.filter (fun h => a / 2 ≤ f h)
  have hpoint (h : H) : f h ≤ a / 2 + (if h ∈ S then (1 : ℝ) else 0) := by
    by_cases hs : h ∈ S
    · simp only [hs, ite_true]
      linarith [hf h]
    · simp only [hs, ite_false]
      have hsmall : f h < a / 2 := by simpa only [S, Finset.mem_filter,
        Finset.mem_univ, true_and, not_le] using hs
      linarith
  have hindicator : (𝔼 h, if h ∈ S then (1 : ℝ) else 0) =
      (S.card : ℝ) / Fintype.card H := by
    rw [Fintype.expect_eq_sum_div_card]
    simp
  have h := hmean.trans (Finset.expect_le_expect (fun h _ => hpoint h))
  rw [Finset.expect_add_distrib, Fintype.expect_const, hindicator] at h
  have hcard : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  refine ⟨S, ?_, fun h hh => (Finset.mem_filter.mp hh).2⟩
  apply (le_div_iff₀ hcard).mp
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_anchor_branch {I G : Type*} [Fintype I] [Fintype G] [Nonempty G]
    (anchor : I → G) (branch : I → Bool) {α : ℝ} (hα : 0 < α)
    (hsize : α * (Fintype.card G : ℝ) ^ 3 ≤ Fintype.card I) :
    ∃ (k : G) (b : Bool) (T : Finset I), T.Nonempty ∧
      α / 2 * (Fintype.card G : ℝ) ^ 2 ≤ (T.card : ℝ) ∧
      ∀ t ∈ T, anchor t = k ∧ branch t = b := by
  classical
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hb : Fintype.card (G × Bool) • (α / 2 * (Fintype.card G : ℝ) ^ 2) ≤
      (Fintype.card I : ℝ) := by
    calc
      _ = α * (Fintype.card G : ℝ) ^ 3 := by
        simp only [nsmul_eq_mul, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
        ring
      _ ≤ _ := hsize
  obtain ⟨⟨k, b⟩, hkb⟩ := Fintype.exists_le_card_fiber_of_nsmul_le_card
    (fun i => (anchor i, branch i)) hb
  let T := Finset.univ.filter (fun i => (anchor i, branch i) = (k, b))
  have hTsize : α / 2 * (Fintype.card G : ℝ) ^ 2 ≤ (T.card : ℝ) := hkb
  have hTpos : (0 : ℝ) < T.card := lt_of_lt_of_le (by positivity) hTsize
  refine ⟨k, b, T, Finset.card_pos.mp (by exact_mod_cast hTpos), hTsize, ?_⟩
  intro t ht
  exact Prod.mk.inj (Finset.mem_filter.mp ht).2

theorem exists_dense_first_fibers {I G : Type*} [Fintype G] [Nonempty G] [DecidableEq G]
    (T : Finset I) (a h : I → G) (hinj : Set.InjOn (fun i => (a i, h i)) (T : Set I))
    {ρ : ℝ} (hρ : 0 < ρ) (hsize : ρ * (Fintype.card G : ℝ) ^ 2 ≤ T.card) :
    ∃ A : Finset G, A.Nonempty ∧ ρ / 2 * (Fintype.card G : ℝ) ≤ (A.card : ℝ) ∧
      ∀ x ∈ A, ρ / 2 * (Fintype.card G : ℝ) ≤ ((T.filter (fun i => a i = x)).card : ℝ) := by
  classical
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  let F (x : G) := T.filter (fun i => a i = x)
  have hcard (x : G) : (F x).card ≤ Fintype.card G := by
    have hmap : Function.Injective (fun t : F x => h t.val) := by
      intro u v huv
      apply Subtype.ext
      apply hinj (Finset.mem_filter.mp u.property).1 (Finset.mem_filter.mp v.property).1
      exact Prod.ext ((Finset.mem_filter.mp u.property).2.trans (Finset.mem_filter.mp v.property).2.symm) huv
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective _ hmap
  have hsum : ∑ x : G, (F x).card = T.card := by
    symm
    exact Finset.card_eq_sum_card_fiberwise (f := a) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  let density (x : G) := ((F x).card : ℝ) / Fintype.card G
  have hmean : ρ ≤ 𝔼 x, density x := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [density, ← Finset.sum_div, ← Nat.cast_sum, hsum]
    apply (le_div_iff₀ hN).mpr
    apply (le_div_iff₀ hN).mpr
    nlinarith only [hsize]
  have hunit (x : G) : density x ≤ 1 := by
    apply (div_le_iff₀ hN).mpr
    simpa only [one_mul] using (Nat.cast_le.mpr (hcard x) : ((F x).card : ℝ) ≤ Fintype.card G)
  obtain ⟨A, hAsize, hA⟩ := exists_dense_level_set density hρ.le hunit hmean
  have hApos : (0 : ℝ) < A.card := lt_of_lt_of_le (by positivity) hAsize
  refine ⟨A, Finset.card_pos.mp (by exact_mod_cast hApos), hAsize, ?_⟩
  intro x hx
  exact (le_div_iff₀ hN).mp (hA x hx)

theorem exists_dense_anchored_fibers {I G : Type*} [Fintype I] [Fintype G]
    [Nonempty G] [DecidableEq G] (a h k : I → G) (branch : I → Bool)
    (hinj : Function.Injective (fun i => (a i, h i, k i)))
    {α : ℝ} (hα : 0 < α) (hsize : α * (Fintype.card G : ℝ) ^ 3 ≤ Fintype.card I) :
    ∃ (anchor : G) (b : Bool) (T : Finset I) (A : Finset G), A.Nonempty ∧
      α / 4 * (Fintype.card G : ℝ) ≤ (A.card : ℝ) ∧
      (∀ t ∈ T, k t = anchor ∧ branch t = b) ∧
      Set.InjOn (fun i => (a i, h i)) (T : Set I) ∧
      ∀ x ∈ A, α / 4 * (Fintype.card G : ℝ) ≤ ((T.filter (fun i => a i = x)).card : ℝ) := by
  classical
  obtain ⟨anchor, b, T, _, hTsize, hT⟩ := exists_large_anchor_branch k branch hα hsize
  have hpair : Set.InjOn (fun i => (a i, h i)) (T : Set I) := by
    intro u hu v hv huv
    have hau : a u = a v := congrArg (fun z : G × G => z.1) huv
    have hhu : h u = h v := congrArg (fun z : G × G => z.2) huv
    apply hinj
    exact Prod.ext hau (Prod.ext hhu ((hT u hu).1.trans (hT v hv).1.symm))
  obtain ⟨A, hA, hAsize, hAfiber⟩ := exists_dense_first_fibers T a h hpair (by positivity) hTsize
  refine ⟨anchor, b, T, A, hA, ?_, hT, hpair, ?_⟩
  · convert hAsize using 1; ring
  · intro x hx
    convert hAfiber x hx using 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {H Ω : Type*} [Fintype H] [Fintype Ω]

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

theorem exists_dense_correlation_pairs {I X : Type*} [Fintype I] [Nonempty I]
    [Fintype X] [Nonempty X] (B : X → ℂ) (v : I → X → ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hB : ∀ x, ‖B x‖ ≤ 1) (hv : ∀ i x, ‖v i x‖ ≤ 1)
    (hcorr : ∀ i, δ ≤ ‖𝔼 x, B x * v i x‖) :
    ∃ P : Finset (I × I), P.Nonempty ∧
      δ ^ 2 / 2 * (Fintype.card I : ℝ) ^ 2 ≤ (P.card : ℝ) ∧
      ∀ t ∈ P, δ ^ 2 / 2 ≤ ‖𝔼 x, v t.1 x * star (v t.2 x)‖ := by
  have hmean : δ ≤ 𝔼 i, ‖𝔼 x, B x * v i x‖ := by
    simpa only [Fintype.expect_const] using
      Finset.expect_le_expect (s := Finset.univ) (fun i _ => hcorr i)
  have hcs := finite_absolute_cauchy_schwarz B v hB
  have hcross : δ ^ 2 ≤ 𝔼 t : I × I, ‖𝔼 x, v t.1 x * star (v t.2 x)‖ := by
    have h := (pow_le_pow_left₀ hδ.le hmean 2).trans hcs
    simpa only [one_pow, one_mul, ← Finset.univ_product_univ, Finset.expect_product] using h
  have hunit (t : I × I) : ‖𝔼 x, v t.1 x * star (v t.2 x)‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply (Finset.expect_le_expect _).trans_eq (Fintype.expect_const _)
    intro x _
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hv t.1 x)).trans (hv t.2 x)
  obtain ⟨P, hsize, hP⟩ := exists_dense_level_set
    (fun t : I × I => ‖𝔼 x, v t.1 x * star (v t.2 x)‖) (sq_nonneg δ) hunit hcross
  have hsize' : δ ^ 2 / 2 * (Fintype.card I : ℝ) ^ 2 ≤ (P.card : ℝ) := by
    simpa only [Fintype.card_prod, Nat.cast_mul, pow_two] using hsize
  have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hpos : 0 < (P.card : ℝ) := lt_of_lt_of_le (by positivity) hsize'
  exact ⟨P, Finset.card_pos.mp (by exact_mod_cast hpos), hsize', hP⟩

end Erdos3

end

end OAI

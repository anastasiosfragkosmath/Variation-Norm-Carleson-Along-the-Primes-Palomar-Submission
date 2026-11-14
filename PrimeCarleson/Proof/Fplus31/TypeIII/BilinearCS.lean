module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Complex.Norm

/-!
# The bilinear Cauchy–Schwarz step (Leng23 Proposition 5.1, type II)

Part of the Vaughan decomposition in the proof of [F+] Proposition 3.1 (Leng23 Proposition
`p:type1type2correlation`, third bullet, `Final_Version.tex` L1096-L1110). For a bounded function
`f` on the integers (in the application `f = 1_P · star (T.eval)`) and coefficients `a`, `b`, a
bilinear correlation `∑_ℓ ∑_m a_ℓ b_m f(ℓ m)` is bounded by the four-fold sum
`∑_{ℓ,ℓ'} ∑_{m,m'} f(ℓ m) conj(f(ℓ' m) f(ℓ m')) f(ℓ' m')`, which equals both
`∑_{m,m'} ‖∑_ℓ f(ℓ m) conj f(ℓ m')‖²` and `∑_{ℓ,ℓ'} ‖∑_m f(ℓ m) conj f(ℓ' m)‖²`.

* `fourFold f Ls Ms`: the four-fold sum (a real number);
* `fourFold_eq_sum_m`, `fourFold_eq_sum_l`: the two square-norm forms; `fourFold_nonneg`,
  `fourFold_mono_left`, `fourFold_mono_right`, `fourFold_le`;
* `bilinear_cs`: `‖∑_ℓ ∑_m a_ℓ b_m f(ℓ m)‖⁴ ≤ (∑‖a_ℓ‖²)² (∑‖b_m‖²)² fourFold f`;
* `exists_pairs_of_fourFold` (the pigeonhole of the type II step): if `X ≤ fourFold f Ls Ms` there
  is a set `P` of pairs `(ℓ, ℓ')` with `X - |Ls|² θ² ≤ |P| |Ms|²` and
  `‖∑_m f(ℓ m) conj f(ℓ' m)‖ ≥ θ` on `P`.
-/

@[expose] public noncomputable section

open Finset
open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- The four-fold sum `∑_{ℓ,ℓ' ∈ Ls} ∑_{m,m' ∈ Ms} f(ℓ m) conj(f(ℓ' m)) conj(f(ℓ m')) f(ℓ' m')`
(Leng23 L1105), as a real number (it is the real part of a nonnegative complex number). -/
def fourFold (f : ℕ → ℂ) (Ls Ms : Finset ℕ) : ℝ :=
  (∑ l ∈ Ls, ∑ l' ∈ Ls, ∑ m ∈ Ms, ∑ m' ∈ Ms,
    f (l * m) * conj (f (l' * m)) * conj (f (l * m')) * f (l' * m')).re

/-- `‖∑_{m ∈ s} g m‖² = ∑_m ∑_{m'} g m conj (g m')`, as complex numbers. -/
theorem ofReal_norm_sum_sq (g : ℕ → ℂ) (s : Finset ℕ) :
    ((‖∑ m ∈ s, g m‖ : ℝ) : ℂ) ^ 2 = ∑ m ∈ s, ∑ m' ∈ s, g m * conj (g m') := by
  rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]

/-- `fourFold = ∑_{ℓ,ℓ'} ‖∑_m f(ℓ m) conj f(ℓ' m)‖²`. -/
theorem fourFold_eq_sum_l (f : ℕ → ℂ) (Ls Ms : Finset ℕ) :
    fourFold f Ls Ms = ∑ l ∈ Ls, ∑ l' ∈ Ls, ‖∑ m ∈ Ms, f (l * m) * conj (f (l' * m))‖ ^ 2 := by
  have key : ∀ l l' : ℕ, ((‖∑ m ∈ Ms, f (l * m) * conj (f (l' * m))‖ : ℝ) : ℂ) ^ 2 =
      ∑ m ∈ Ms, ∑ m' ∈ Ms, f (l * m) * conj (f (l' * m)) * conj (f (l * m')) * f (l' * m') := by
    intro l l'
    rw [ofReal_norm_sum_sq]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
    simp only [map_mul, Complex.conj_conj]
    ring
  have h : (∑ l ∈ Ls, ∑ l' ∈ Ls, ∑ m ∈ Ms, ∑ m' ∈ Ms,
      f (l * m) * conj (f (l' * m)) * conj (f (l * m')) * f (l' * m')) =
      ((∑ l ∈ Ls, ∑ l' ∈ Ls, ‖∑ m ∈ Ms, f (l * m) * conj (f (l' * m))‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => (key l l').symm
  unfold fourFold
  rw [h, Complex.ofReal_re]

/-- Reordering of a fourfold finite sum: the order `(ℓ, ℓ', m, m')` becomes `(m, m', ℓ, ℓ')`. -/
theorem sum_comm_four {M : Type*} [AddCommMonoid M] (Ls Ms : Finset ℕ) (F : ℕ → ℕ → ℕ → ℕ → M) :
    ∑ l ∈ Ls, ∑ l' ∈ Ls, ∑ m ∈ Ms, ∑ m' ∈ Ms, F l l' m m' =
      ∑ m ∈ Ms, ∑ m' ∈ Ms, ∑ l ∈ Ls, ∑ l' ∈ Ls, F l l' m m' := by
  calc ∑ l ∈ Ls, ∑ l' ∈ Ls, ∑ m ∈ Ms, ∑ m' ∈ Ms, F l l' m m'
      = ∑ l ∈ Ls, ∑ m ∈ Ms, ∑ m' ∈ Ms, ∑ l' ∈ Ls, F l l' m m' := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ m ∈ Ms, ∑ l ∈ Ls, ∑ m' ∈ Ms, ∑ l' ∈ Ls, F l l' m m' := Finset.sum_comm
    _ = ∑ m ∈ Ms, ∑ m' ∈ Ms, ∑ l ∈ Ls, ∑ l' ∈ Ls, F l l' m m' := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_comm]

/-- `fourFold = ∑_{m,m'} ‖∑_ℓ f(ℓ m) conj f(ℓ m')‖²`. -/
theorem fourFold_eq_sum_m (f : ℕ → ℂ) (Ls Ms : Finset ℕ) :
    fourFold f Ls Ms = ∑ m ∈ Ms, ∑ m' ∈ Ms, ‖∑ l ∈ Ls, f (l * m) * conj (f (l * m'))‖ ^ 2 := by
  have key : ∀ m m' : ℕ, ((‖∑ l ∈ Ls, f (l * m) * conj (f (l * m'))‖ : ℝ) : ℂ) ^ 2 =
      ∑ l ∈ Ls, ∑ l' ∈ Ls, f (l * m) * conj (f (l' * m)) * conj (f (l * m')) * f (l' * m') := by
    intro m m'
    rw [ofReal_norm_sum_sq]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
    simp only [map_mul, Complex.conj_conj]
    ring
  have h : (∑ l ∈ Ls, ∑ l' ∈ Ls, ∑ m ∈ Ms, ∑ m' ∈ Ms,
      f (l * m) * conj (f (l' * m)) * conj (f (l * m')) * f (l' * m')) =
      ((∑ m ∈ Ms, ∑ m' ∈ Ms, ‖∑ l ∈ Ls, f (l * m) * conj (f (l * m'))‖ ^ 2 : ℝ) : ℂ) := by
    rw [sum_comm_four]
    push_cast
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => (key m m').symm
  unfold fourFold
  rw [h, Complex.ofReal_re]

/-- The four-fold sum is nonnegative. -/
theorem fourFold_nonneg (f : ℕ → ℂ) (Ls Ms : Finset ℕ) : 0 ≤ fourFold f Ls Ms := by
  rw [fourFold_eq_sum_l]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- A double sum of nonnegative terms over `s × s` is monotone in `s`. -/
theorem sum_sum_mono (x : ℕ → ℕ → ℝ) (hx : ∀ a b, 0 ≤ x a b) {s t : Finset ℕ} (h : s ⊆ t) :
    ∑ a ∈ s, ∑ b ∈ s, x a b ≤ ∑ a ∈ t, ∑ b ∈ t, x a b := by
  calc ∑ a ∈ s, ∑ b ∈ s, x a b ≤ ∑ a ∈ s, ∑ b ∈ t, x a b :=
        Finset.sum_le_sum fun a _ =>
          Finset.sum_le_sum_of_subset_of_nonneg h fun b _ _ => hx a b
    _ ≤ ∑ a ∈ t, ∑ b ∈ t, x a b :=
        Finset.sum_le_sum_of_subset_of_nonneg h fun a _ _ => Finset.sum_nonneg fun b _ => hx a b

/-- The four-fold sum is monotone in the `ℓ`-set. -/
theorem fourFold_mono_left (f : ℕ → ℂ) {Ls Ls' : Finset ℕ} (h : Ls ⊆ Ls') (Ms : Finset ℕ) :
    fourFold f Ls Ms ≤ fourFold f Ls' Ms := by
  rw [fourFold_eq_sum_l, fourFold_eq_sum_l]
  exact sum_sum_mono (fun l l' => ‖∑ m ∈ Ms, f (l * m) * conj (f (l' * m))‖ ^ 2)
    (fun _ _ => sq_nonneg _) h

/-- The four-fold sum is monotone in the `m`-set. -/
theorem fourFold_mono_right (f : ℕ → ℂ) (Ls : Finset ℕ) {Ms Ms' : Finset ℕ} (h : Ms ⊆ Ms') :
    fourFold f Ls Ms ≤ fourFold f Ls Ms' := by
  rw [fourFold_eq_sum_m, fourFold_eq_sum_m]
  exact sum_sum_mono (fun m m' => ‖∑ l ∈ Ls, f (l * m) * conj (f (l * m'))‖ ^ 2)
    (fun _ _ => sq_nonneg _) h

/-- For a function bounded by `1`, `‖∑_m f(ℓ m) conj f(ℓ' m)‖ ≤ |Ms|`. -/
theorem norm_sum_mul_conj_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (Ms : Finset ℕ) (a b : ℕ → ℕ) :
    ‖∑ m ∈ Ms, f (a m) * conj (f (b m))‖ ≤ Ms.card := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ m ∈ Ms, ‖f (a m) * conj (f (b m))‖ ≤ ∑ _m ∈ Ms, (1 : ℝ) := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [norm_mul, Complex.norm_conj]
        exact (mul_le_mul (hf _) (hf _) (norm_nonneg _) zero_le_one).trans (by norm_num)
    _ = Ms.card := by simp

/-- Trivial upper bound `fourFold ≤ |Ls|² |Ms|²` for a function bounded by `1`. -/
theorem fourFold_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (Ls Ms : Finset ℕ) :
    fourFold f Ls Ms ≤ (Ls.card : ℝ) ^ 2 * (Ms.card : ℝ) ^ 2 := by
  rw [fourFold_eq_sum_l]
  calc ∑ l ∈ Ls, ∑ l' ∈ Ls, ‖∑ m ∈ Ms, f (l * m) * conj (f (l' * m))‖ ^ 2
      ≤ ∑ _l ∈ Ls, ∑ _l' ∈ Ls, (Ms.card : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun l' _ => ?_
        exact pow_le_pow_left₀ (norm_nonneg _)
          (norm_sum_mul_conj_le f hf Ms (fun m => l * m) (fun m => l' * m)) 2
    _ = (Ls.card : ℝ) ^ 2 * (Ms.card : ℝ) ^ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring

/-- **Bilinear Cauchy–Schwarz** (Leng23 Proposition 5.1, type II step):
`‖∑_ℓ ∑_m a_ℓ b_m f(ℓ m)‖⁴ ≤ (∑‖a_ℓ‖²)² (∑‖b_m‖²)² · fourFold f`. -/
theorem bilinear_cs (f : ℕ → ℂ) (Ls Ms : Finset ℕ) (a b : ℕ → ℂ) :
    ‖∑ l ∈ Ls, ∑ m ∈ Ms, a l * b m * f (l * m)‖ ^ 4 ≤
      (∑ l ∈ Ls, ‖a l‖ ^ 2) ^ 2 * (∑ m ∈ Ms, ‖b m‖ ^ 2) ^ 2 * fourFold f Ls Ms := by
  set S : ℕ → ℂ := fun l => ∑ m ∈ Ms, b m * f (l * m) with hS
  have hrw : ∑ l ∈ Ls, ∑ m ∈ Ms, a l * b m * f (l * m) = ∑ l ∈ Ls, a l * S l := by
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hS, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  -- Step A
  have hA : ‖∑ l ∈ Ls, a l * S l‖ ^ 2 ≤ (∑ l ∈ Ls, ‖a l‖ ^ 2) * ∑ l ∈ Ls, ‖S l‖ ^ 2 := by
    calc ‖∑ l ∈ Ls, a l * S l‖ ^ 2 ≤ (∑ l ∈ Ls, ‖a l‖ * ‖S l‖) ^ 2 := by
          refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans ?_) 2
          exact Finset.sum_le_sum fun l _ => (norm_mul _ _).le
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq Ls (fun l => ‖a l‖) (fun l => ‖S l‖)
  -- Step B
  have hB : (∑ l ∈ Ls, ‖S l‖ ^ 2) ^ 2 ≤ (∑ m ∈ Ms, ‖b m‖ ^ 2) ^ 2 * fourFold f Ls Ms := by
    have hc : (((∑ l ∈ Ls, ‖S l‖ ^ 2 : ℝ)) : ℂ) =
        ∑ m ∈ Ms, ∑ m' ∈ Ms, b m * conj (b m') * ∑ l ∈ Ls, f (l * m) * conj (f (l * m')) := by
      push_cast
      have : ∀ l ∈ Ls, ((‖S l‖ : ℝ) : ℂ) ^ 2 =
          ∑ m ∈ Ms, ∑ m' ∈ Ms, b m * conj (b m') * (f (l * m) * conj (f (l * m'))) := by
        intro l _
        rw [← Complex.mul_conj', hS]
        simp only [map_sum, map_mul, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
        ring
      rw [Finset.sum_congr rfl this, Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m' _ => ?_
      rw [Finset.mul_sum]
    have hnorm : ∑ l ∈ Ls, ‖S l‖ ^ 2 =
        ‖∑ m ∈ Ms, ∑ m' ∈ Ms, b m * conj (b m') * ∑ l ∈ Ls, f (l * m) * conj (f (l * m'))‖ := by
      rw [← hc, Complex.norm_real, Real.norm_of_nonneg
        (Finset.sum_nonneg fun l _ => sq_nonneg _)]
    have h1 : ∑ l ∈ Ls, ‖S l‖ ^ 2 ≤
        ∑ m ∈ Ms, ∑ m' ∈ Ms, ‖b m‖ * ‖b m'‖ *
          ‖∑ l ∈ Ls, f (l * m) * conj (f (l * m'))‖ := by
      rw [hnorm]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m' _ => ?_)
      rw [norm_mul, norm_mul, Complex.norm_conj]
    have h2 : (∑ m ∈ Ms, ∑ m' ∈ Ms, ‖b m‖ * ‖b m'‖ *
          ‖∑ l ∈ Ls, f (l * m) * conj (f (l * m'))‖) ^ 2 ≤
        (∑ m ∈ Ms, ‖b m‖ ^ 2) ^ 2 * fourFold f Ls Ms := by
      have e1 : ∑ p ∈ Ms ×ˢ Ms, (‖b p.1‖ * ‖b p.2‖) ^ 2 = (∑ m ∈ Ms, ‖b m‖ ^ 2) ^ 2 := by
        rw [Finset.sum_product, sq (∑ m ∈ Ms, ‖b m‖ ^ 2), Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => mul_pow _ _ _
      have e2 : ∑ p ∈ Ms ×ˢ Ms, ‖∑ l ∈ Ls, f (l * p.1) * conj (f (l * p.2))‖ ^ 2 =
          fourFold f Ls Ms := by
        rw [fourFold_eq_sum_m, Finset.sum_product]
      have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Ms ×ˢ Ms) (fun p => ‖b p.1‖ * ‖b p.2‖)
        (fun p => ‖∑ l ∈ Ls, f (l * p.1) * conj (f (l * p.2))‖)
      rw [e1, e2] at hCS
      have e3 : ∑ p ∈ Ms ×ˢ Ms, ‖b p.1‖ * ‖b p.2‖ *
          ‖∑ l ∈ Ls, f (l * p.1) * conj (f (l * p.2))‖ =
          ∑ m ∈ Ms, ∑ m' ∈ Ms, ‖b m‖ * ‖b m'‖ *
            ‖∑ l ∈ Ls, f (l * m) * conj (f (l * m'))‖ := Finset.sum_product _ _ _
      rw [e3] at hCS
      exact hCS
    calc (∑ l ∈ Ls, ‖S l‖ ^ 2) ^ 2 ≤
          (∑ m ∈ Ms, ∑ m' ∈ Ms, ‖b m‖ * ‖b m'‖ *
            ‖∑ l ∈ Ls, f (l * m) * conj (f (l * m'))‖) ^ 2 :=
          pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => sq_nonneg _) h1 2
      _ ≤ _ := h2
  rw [hrw]
  calc ‖∑ l ∈ Ls, a l * S l‖ ^ 4 = (‖∑ l ∈ Ls, a l * S l‖ ^ 2) ^ 2 := by ring
    _ ≤ ((∑ l ∈ Ls, ‖a l‖ ^ 2) * ∑ l ∈ Ls, ‖S l‖ ^ 2) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) hA 2
    _ = (∑ l ∈ Ls, ‖a l‖ ^ 2) ^ 2 * (∑ l ∈ Ls, ‖S l‖ ^ 2) ^ 2 := by ring
    _ ≤ (∑ l ∈ Ls, ‖a l‖ ^ 2) ^ 2 * ((∑ m ∈ Ms, ‖b m‖ ^ 2) ^ 2 * fourFold f Ls Ms) :=
        mul_le_mul_of_nonneg_left hB (sq_nonneg _)
    _ = _ := by ring

/-- **The pigeonhole of the type II step**: if `X ≤ fourFold f Ls Ms` for a function bounded by `1`,
there is a set `P` of pairs `(ℓ, ℓ')` of the `ℓ`-set with `X - |Ls|² θ² ≤ |P| |Ms|²` on which
`θ ≤ ‖∑_m f(ℓ m) conj f(ℓ' m)‖`. -/
theorem exists_pairs_of_fourFold (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (Ls Ms : Finset ℕ) {X θ : ℝ}
    (hX : X ≤ fourFold f Ls Ms) :
    ∃ P ⊆ Ls ×ˢ Ls, X - (Ls.card : ℝ) ^ 2 * θ ^ 2 ≤ (P.card : ℝ) * (Ms.card : ℝ) ^ 2 ∧
      ∀ p ∈ P, θ ≤ ‖∑ m ∈ Ms, f (p.1 * m) * conj (f (p.2 * m))‖ := by
  set g : ℕ × ℕ → ℝ := fun p => ‖∑ m ∈ Ms, f (p.1 * m) * conj (f (p.2 * m))‖ with hg
  refine ⟨(Ls ×ˢ Ls).filter fun p => θ ≤ g p, Finset.filter_subset _ _, ?_, fun p hp =>
    (Finset.mem_filter.mp hp).2⟩
  have hsum : fourFold f Ls Ms = ∑ p ∈ Ls ×ˢ Ls, g p ^ 2 := by
    rw [fourFold_eq_sum_l, Finset.sum_product]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Ls ×ˢ Ls) (fun p => θ ≤ g p)
    (fun p => g p ^ 2)
  have h1 : ∑ p ∈ (Ls ×ˢ Ls).filter (fun p => θ ≤ g p), g p ^ 2 ≤
      ((Ls ×ˢ Ls).filter (fun p => θ ≤ g p)).card * (Ms.card : ℝ) ^ 2 := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun p _ =>
      pow_le_pow_left₀ (norm_nonneg _)
        (norm_sum_mul_conj_le f hf Ms (fun m => p.1 * m) (fun m => p.2 * m)) 2
  have h2 : ∑ p ∈ (Ls ×ˢ Ls).filter (fun p => ¬ θ ≤ g p), g p ^ 2 ≤
      (Ls.card : ℝ) ^ 2 * θ ^ 2 := by
    calc ∑ p ∈ (Ls ×ˢ Ls).filter (fun p => ¬ θ ≤ g p), g p ^ 2
        ≤ ∑ p ∈ (Ls ×ˢ Ls).filter (fun p => ¬ θ ≤ g p), θ ^ 2 := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hlt : g p < θ := not_le.mp (Finset.mem_filter.mp hp).2
          exact pow_le_pow_left₀ (norm_nonneg _) hlt.le 2
      _ ≤ ∑ _p ∈ Ls ×ˢ Ls, θ ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => ?_
          positivity
      _ = (Ls.card : ℝ) ^ 2 * θ ^ 2 := by
          rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]
          push_cast
          ring
  rw [hsum] at hX
  linarith

end PrimeCarleson.Proof.Fplus31

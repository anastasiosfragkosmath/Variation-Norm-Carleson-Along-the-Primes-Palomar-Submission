module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Abstract energy decrement

An abstract form of the greedy decomposition of `sources/Variational_Carleson.tex`
(L2471–L2534), Source: main paper `p:greedy`, L2471–L2479.

Let `S : V → ℝ` be a seminorm-like functional on a complex inner product space (it is only
assumed subadditive and `ℂ`-homogeneous up to `≤`). Suppose `S f ≤ β ‖f‖` (the trivial bound) and
that every `f` with `S f > X ‖f‖` correlates with a unit vector `Φ` with `S Φ ≤ σ`, namely
`η ‖f‖ ≤ ‖⟪Φ, f⟫‖` (the inverse theorem). Removing the component of `f` along `Φ` multiplies the
squared norm by at most `1 - η²`, and `n` such removals leave a remainder of norm `≤ X ‖f‖`
whenever `β² (1 - η²)ⁿ ≤ X²`. This gives:

* `norm_sub_inner_smul_sq`: Pythagoras for removing the component along a unit vector;
* `energy_decrement`: `S f ≤ (X + σ √n) ‖f‖` as soon as `β² (1 - η²)ⁿ ≤ X²`;
* `one_sub_sq_pow_le_sq`: `(1 - η²)ⁿ ≤ η²` for `n ≥ 2 / η³`;
* `le_of_inverse_theorem`: the packaged form with `β = X / η` and `n = ⌈2 / η³⌉`, giving
  `S f ≤ (X + σ √(3 / η³)) ‖f‖`.

The proof of `energy_decrement` is an induction on `n` for the statement
`‖f‖ ≤ t → β² ‖f‖² (1 - η²)ⁿ ≤ X² t² → S f ≤ X t + σ √n ‖f‖`, the inductive step being the
Cauchy–Schwarz inequality `√n a + b ≤ √(n + 1) √(a² + b²)` applied to the norms of the remainder
`f - ⟪Φ, f⟫ Φ` and of the removed component.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace

set_option autoImplicit false

namespace PrimeCarleson.Proof.Goal0

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Removing the component along a unit vector (Pythagoras). -/
theorem norm_sub_inner_smul_sq {Φ : V} (hΦ : ‖Φ‖ = 1) (f : V) :
    ‖f - ⟪Φ, f⟫_ℂ • Φ‖ ^ 2 = ‖f‖ ^ 2 - ‖⟪Φ, f⟫_ℂ‖ ^ 2 := by
  have e : ⟪f, ⟪Φ, f⟫_ℂ • Φ⟫_ℂ = ((‖⟪Φ, f⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_smul_right, ← inner_conj_symm f Φ, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [norm_sub_sq (𝕜 := ℂ), e, norm_smul, hΦ]
  have hre : RCLike.re (((‖⟪Φ, f⟫_ℂ‖ ^ 2 : ℝ) : ℂ)) = ‖⟪Φ, f⟫_ℂ‖ ^ 2 := Complex.ofReal_re _
  rw [hre]
  ring

/-- Cauchy–Schwarz in `ℝ²`: `√n a + b ≤ √(n + 1) √(a² + b²)`. -/
theorem sqrt_mul_add_le_sqrt_succ_mul_sqrt (n : ℕ) (a b : ℝ) :
    Real.sqrt n * a + b ≤ Real.sqrt (n + 1) * Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  refine le_trans (le_abs_self _) ?_
  refine Real.abs_le_sqrt ?_
  have hn : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  nlinarith [sq_nonneg (Real.sqrt n * b - a)]

/-- Inductive step of `energy_decrement`: the statement for `n` implies the one for `n + 1`. -/
theorem energy_decrement_aux (S : V → ℝ) {β X σ η : ℝ} (hX : 0 ≤ X) (hσ : 0 ≤ σ)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hadd : ∀ f g, S (f + g) ≤ S f + S g) (hsmul : ∀ (c : ℂ) f, S (c • f) ≤ ‖c‖ * S f)
    (htriv : ∀ f, S f ≤ β * ‖f‖)
    (hinv : ∀ f, X * ‖f‖ < S f → ∃ Φ : V, ‖Φ‖ = 1 ∧ S Φ ≤ σ ∧ η * ‖f‖ ≤ ‖⟪Φ, f⟫_ℂ‖)
    (n : ℕ) : ∀ (f : V) (t : ℝ), 0 ≤ t → ‖f‖ ≤ t →
      β ^ 2 * ‖f‖ ^ 2 * (1 - η ^ 2) ^ n ≤ X ^ 2 * t ^ 2 →
        S f ≤ X * t + σ * Real.sqrt n * ‖f‖ := by
  have hη2 : 0 ≤ 1 - η ^ 2 := by nlinarith
  induction n with
  | zero =>
    intro f t ht hft hcond
    have h1 : (|β| * ‖f‖) ^ 2 ≤ (X * t) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]
      simpa [mul_comm, mul_assoc, mul_left_comm] using hcond
    have h2 : |β| * ‖f‖ ≤ X * t :=
      abs_le_of_sq_le_sq' h1 (mul_nonneg hX ht) |>.2
    calc S f ≤ β * ‖f‖ := htriv f
      _ ≤ |β| * ‖f‖ := mul_le_mul_of_nonneg_right (le_abs_self β) (norm_nonneg f)
      _ ≤ X * t := h2
      _ = X * t + σ * Real.sqrt (0 : ℕ) * ‖f‖ := by simp
  | succ n ih =>
    intro f t ht hft hcond
    have hnn : 0 ≤ σ * Real.sqrt (n + 1 : ℕ) * ‖f‖ := by positivity
    by_cases hS : S f ≤ X * t
    · linarith
    · replace hS := not_le.mp hS
      have hXf : X * ‖f‖ < S f :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left hft hX) hS
      obtain ⟨Φ, hΦ, hSΦ, hcorr⟩ := hinv f hXf
      set c : ℂ := ⟪Φ, f⟫_ℂ with hc
      set f' : V := f - c • Φ with hf'
      have hpyth : ‖f'‖ ^ 2 = ‖f‖ ^ 2 - ‖c‖ ^ 2 := norm_sub_inner_smul_sq hΦ f
      have hηf : (η * ‖f‖) ^ 2 ≤ ‖c‖ ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hη.le (norm_nonneg f)) hcorr 2
      have hf'sq : ‖f'‖ ^ 2 ≤ (1 - η ^ 2) * ‖f‖ ^ 2 := by nlinarith
      have hf'le : ‖f'‖ ≤ ‖f‖ := by
        refine abs_le_of_sq_le_sq' ?_ (norm_nonneg f) |>.2
        nlinarith [sq_nonneg η, sq_nonneg ‖f‖]
      have hcond' : β ^ 2 * ‖f'‖ ^ 2 * (1 - η ^ 2) ^ n ≤ X ^ 2 * t ^ 2 := by
        calc β ^ 2 * ‖f'‖ ^ 2 * (1 - η ^ 2) ^ n
            ≤ β ^ 2 * ((1 - η ^ 2) * ‖f‖ ^ 2) * (1 - η ^ 2) ^ n := by gcongr
          _ = β ^ 2 * ‖f‖ ^ 2 * (1 - η ^ 2) ^ (n + 1) := by ring
          _ ≤ X ^ 2 * t ^ 2 := hcond
      have hIH := ih f' t ht (hf'le.trans hft) hcond'
      have hSf : S f ≤ S f' + ‖c‖ * σ := by
        have hfeq : f = f' + c • Φ := by simp [hf']
        calc S f = S (f' + c • Φ) := by rw [← hfeq]
          _ ≤ S f' + S (c • Φ) := hadd _ _
          _ ≤ S f' + ‖c‖ * S Φ := by gcongr; exact hsmul c Φ
          _ ≤ S f' + ‖c‖ * σ := by gcongr
      have hCS := sqrt_mul_add_le_sqrt_succ_mul_sqrt n ‖f'‖ ‖c‖
      have hsum : ‖f'‖ ^ 2 + ‖c‖ ^ 2 = ‖f‖ ^ 2 := by linarith
      rw [hsum, Real.sqrt_sq (norm_nonneg f)] at hCS
      have : σ * (Real.sqrt n * ‖f'‖ + ‖c‖) ≤ σ * (Real.sqrt (n + 1) * ‖f‖) :=
        mul_le_mul_of_nonneg_left hCS hσ
      push_cast
      nlinarith [this]

/-- Greedy energy decrement: if `S f ≤ β ‖f‖` trivially, and every `f` with `S f > X ‖f‖`
correlates (at level `η`) with a unit vector `Φ` with `S Φ ≤ σ`, then `n` steps with
`β² (1 - η²)ⁿ ≤ X²` give `S f ≤ (X + σ √n) ‖f‖`. -/
theorem energy_decrement (S : V → ℝ) {β X σ η : ℝ} (hX : 0 ≤ X) (hσ : 0 ≤ σ)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hadd : ∀ f g, S (f + g) ≤ S f + S g) (hsmul : ∀ (c : ℂ) f, S (c • f) ≤ ‖c‖ * S f)
    (htriv : ∀ f, S f ≤ β * ‖f‖)
    (hinv : ∀ f, X * ‖f‖ < S f → ∃ Φ : V, ‖Φ‖ = 1 ∧ S Φ ≤ σ ∧ η * ‖f‖ ≤ ‖⟪Φ, f⟫_ℂ‖)
    {n : ℕ} (hn : β ^ 2 * (1 - η ^ 2) ^ n ≤ X ^ 2) (f : V) :
    S f ≤ (X + σ * Real.sqrt n) * ‖f‖ := by
  have h := energy_decrement_aux S hX hσ hη hη1 hadd hsmul htriv hinv n f ‖f‖ (norm_nonneg f)
    le_rfl (by
      have := mul_le_mul_of_nonneg_right hn (sq_nonneg ‖f‖)
      linarith)
  linarith

/-- `(1 - η²)ⁿ ≤ η²` as soon as `n ≥ 2 / η³`. -/
theorem one_sub_sq_pow_le_sq {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {n : ℕ} (hn : 2 / η ^ 3 ≤ n) :
    (1 - η ^ 2) ^ n ≤ η ^ 2 := by
  have h0 : 0 ≤ 1 - η ^ 2 := by nlinarith
  have h1 : (1 - η ^ 2) ^ n ≤ Real.exp (-(n * η ^ 2)) := by
    calc (1 - η ^ 2) ^ n ≤ Real.exp (-η ^ 2) ^ n :=
          pow_le_pow_left₀ h0 (by linarith [Real.add_one_le_exp (-η ^ 2)]) n
      _ = Real.exp (-(n * η ^ 2)) := by rw [← Real.exp_nat_mul]; ring_nf
  have h2 : 2 / η ≤ n * η ^ 2 := by
    have := mul_le_mul_of_nonneg_right hn (sq_nonneg η)
    have e : 2 / η ^ 3 * η ^ 2 = 2 / η := by field_simp
    linarith
  have h3 : Real.exp (-(n * η ^ 2)) ≤ Real.exp (-(2 / η)) := Real.exp_le_exp.2 (by linarith)
  have h4 : Real.exp (-(2 / η)) ≤ η ^ 2 := by
    have hexp : 1 / η ≤ Real.exp (1 / η) := by linarith [Real.add_one_le_exp (1 / η)]
    have hpos : 0 < 1 / η := by positivity
    have h5 : (1 / η) ^ 2 ≤ Real.exp (1 / η) ^ 2 := pow_le_pow_left₀ hpos.le hexp 2
    have e : Real.exp (-(2 / η)) = (Real.exp (1 / η) ^ 2)⁻¹ := by
      rw [← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1
      push_cast
      ring
    rw [e]
    calc (Real.exp (1 / η) ^ 2)⁻¹ ≤ ((1 / η) ^ 2)⁻¹ := inv_anti₀ (by positivity) h5
      _ = η ^ 2 := by field_simp
  exact h1.trans (h3.trans h4)

/-- Packaged form with `β = X / η` and `n = ⌈2 / η³⌉`. -/
theorem le_of_inverse_theorem (S : V → ℝ) {X σ η : ℝ} (hX : 0 ≤ X) (hσ : 0 ≤ σ)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hadd : ∀ f g, S (f + g) ≤ S f + S g) (hsmul : ∀ (c : ℂ) f, S (c • f) ≤ ‖c‖ * S f)
    (htriv : ∀ f, S f ≤ X / η * ‖f‖)
    (hinv : ∀ f, X * ‖f‖ < S f → ∃ Φ : V, ‖Φ‖ = 1 ∧ S Φ ≤ σ ∧ η * ‖f‖ ≤ ‖⟪Φ, f⟫_ℂ‖) (f : V) :
    S f ≤ (X + σ * Real.sqrt (3 / η ^ 3)) * ‖f‖ := by
  have hη3 : 0 < η ^ 3 := by positivity
  have hceil : 2 / η ^ 3 ≤ (⌈2 / η ^ 3⌉₊ : ℝ) := Nat.le_ceil _
  have hpow := one_sub_sq_pow_le_sq hη hη1 hceil
  have hn : (X / η) ^ 2 * (1 - η ^ 2) ^ ⌈2 / η ^ 3⌉₊ ≤ X ^ 2 := by
    calc (X / η) ^ 2 * (1 - η ^ 2) ^ ⌈2 / η ^ 3⌉₊ ≤ (X / η) ^ 2 * η ^ 2 := by gcongr
      _ = X ^ 2 := by field_simp
  have hle : (⌈2 / η ^ 3⌉₊ : ℝ) ≤ 3 / η ^ 3 := by
    have h1 : (⌈2 / η ^ 3⌉₊ : ℝ) < 2 / η ^ 3 + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : 1 ≤ 1 / η ^ 3 := by
      rw [le_div_iff₀ hη3]
      simpa using pow_le_one₀ hη.le hη1 (n := 3)
    have h3 : 3 / η ^ 3 = 2 / η ^ 3 + 1 / η ^ 3 := by ring
    linarith
  have h := energy_decrement S hX hσ hη hη1 hadd hsmul htriv hinv hn f
  have hsq : Real.sqrt (⌈2 / η ^ 3⌉₊ : ℝ) ≤ Real.sqrt (3 / η ^ 3) := Real.sqrt_le_sqrt hle
  calc S f ≤ (X + σ * Real.sqrt (⌈2 / η ^ 3⌉₊ : ℝ)) * ‖f‖ := h
    _ ≤ (X + σ * Real.sqrt (3 / η ^ 3)) * ‖f‖ := by gcongr

end PrimeCarleson.Proof.Goal0

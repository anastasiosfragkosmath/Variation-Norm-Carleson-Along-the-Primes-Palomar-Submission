module

public import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

/-!
# The iteration, the budget calculus

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). `PB f`
says that `0 ≤ f p ≤ (p + K)^K` for all `p ≥ 1` and some `K ≥ 2`; the class is closed under sums,
products and composition with functions `≥ 1`, by `exists_natPolynomial_eval_budget`. Every level of
a stage is then a `PB` function of the previous one, and so is the composite over the (bounded)
number of stages.
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- `f` is nonnegative and bounded by a polynomial budget: `0 ≤ f p ≤ (p + K)^K` for `p ≥ 1`. -/
def PB (f : ℝ → ℝ) : Prop := ∃ K : ℕ, 2 ≤ K ∧ ∀ p : ℝ, 1 ≤ p → 0 ≤ f p ∧ f p ≤ (p + K) ^ K

/-- A nonnegative smaller function is bounded if a larger one is. -/
theorem PB.mono {f g : ℝ → ℝ} (hf : PB f) (h : ∀ p, 1 ≤ p → 0 ≤ g p ∧ g p ≤ f p) : PB g := by
  obtain ⟨K, hK, hf⟩ := hf
  exact ⟨K, hK, fun p hp => ⟨(h p hp).1, (h p hp).2.trans (hf p hp).2⟩⟩

/-- The identity is bounded. -/
theorem PB.id : PB (fun p => p) := by
  refine ⟨2, le_rfl, fun p hp => ⟨by linarith, ?_⟩⟩
  push_cast
  nlinarith

/-- A nonnegative constant is bounded. -/
theorem PB.const (c : ℝ) (hc : 0 ≤ c) : PB (fun _ => c) := by
  refine ⟨⌈c⌉₊ + 2, by omega, fun p hp => ⟨hc, ?_⟩⟩
  have h1 : c ≤ ((⌈c⌉₊ + 2 : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.le_ceil c]
  have h2 : (1 : ℝ) ≤ p + ((⌈c⌉₊ + 2 : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ ((⌈c⌉₊ + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have h3 : p + ((⌈c⌉₊ + 2 : ℕ) : ℝ) ≤ (p + ((⌈c⌉₊ + 2 : ℕ) : ℝ)) ^ (⌈c⌉₊ + 2) :=
    le_self_pow₀ h2 (by omega)
  linarith

/-- The budget map `p ↦ (p + K)^K` of a lemma with constant `K` is bounded. -/
theorem PB.step (K : ℕ) : PB (fun p => (p + K) ^ K) := by
  refine ⟨max K 2, le_max_right _ _, fun p hp => ⟨?_, ?_⟩⟩
  · have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    positivity
  have hK : (K : ℝ) ≤ ((max K 2 : ℕ) : ℝ) := by exact_mod_cast le_max_left K 2
  have h1 : (1 : ℝ) ≤ p + K := by
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    linarith
  calc (p + K) ^ K ≤ (p + K) ^ (max K 2) := pow_le_pow_right₀ h1 (le_max_left _ _)
    _ ≤ (p + ((max K 2 : ℕ) : ℝ)) ^ (max K 2) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _

/-- Sums of bounded functions are bounded. -/
theorem PB.add {f g : ℝ → ℝ} (hf : PB f) (hg : PB g) : PB (fun p => f p + g p) := by
  obtain ⟨K₁, hK₁, hf⟩ := hf
  obtain ⟨K₂, hK₂, hg⟩ := hg
  obtain ⟨K, hK, hb⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + Polynomial.C K₁) ^ K₁ + (Polynomial.X + Polynomial.C K₂) ^ K₂)
  refine ⟨K, hK, fun p hp => ⟨add_nonneg (hf p hp).1 (hg p hp).1, ?_⟩⟩
  have h := hb p (by linarith)
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_natCast, eq_natCast] at h
  exact (add_le_add (hf p hp).2 (hg p hp).2).trans h

/-- Products of bounded functions are bounded. -/
theorem PB.mul {f g : ℝ → ℝ} (hf : PB f) (hg : PB g) : PB (fun p => f p * g p) := by
  obtain ⟨K₁, hK₁, hf⟩ := hf
  obtain ⟨K₂, hK₂, hg⟩ := hg
  obtain ⟨K, hK, hb⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + Polynomial.C K₁) ^ K₁ * (Polynomial.X + Polynomial.C K₂) ^ K₂)
  refine ⟨K, hK, fun p hp => ⟨mul_nonneg (hf p hp).1 (hg p hp).1, ?_⟩⟩
  have h := hb p (by linarith)
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_add,
    Polynomial.eval₂_X, Polynomial.eval₂_natCast, eq_natCast] at h
  exact (mul_le_mul (hf p hp).2 (hg p hp).2 (hg p hp).1 (by
    have : (0 : ℝ) ≤ (p + K₁) := by have := Nat.cast_nonneg (α := ℝ) K₁; linarith
    positivity)).trans h

/-- Composition of bounded functions, the inner one being `≥ 1`. -/
theorem PB.comp {f g : ℝ → ℝ} (hf : PB f) (hg : PB g) (hg1 : ∀ p, 1 ≤ p → 1 ≤ g p) :
    PB (fun p => f (g p)) := by
  obtain ⟨K₁, hK₁, hf⟩ := hf
  obtain ⟨K₂, hK₂, hg⟩ := hg
  obtain ⟨K, hK, hb⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + Polynomial.C K₂) ^ K₂ + Polynomial.C K₁) ^ K₁)
  refine ⟨K, hK, fun p hp => ⟨(hf (g p) (hg1 p hp)).1, ?_⟩⟩
  have h := hb p (by linarith)
  simp only [Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_X,
    Polynomial.eval₂_natCast, eq_natCast] at h
  refine ((hf (g p) (hg1 p hp)).2).trans (le_trans ?_ h)
  have h0 : (0 : ℝ) ≤ g p + K₁ := by have := hg1 p hp; have := Nat.cast_nonneg (α := ℝ) K₁; linarith
  exact pow_le_pow_left₀ h0 (by linarith [(hg p hp).2]) _

/-- A natural power of a bounded function. -/
theorem PB.npow {f : ℝ → ℝ} (hf : PB f) (n : ℕ) : PB (fun p => f p ^ n) := by
  induction n with
  | zero => exact (PB.const 1 zero_le_one).mono fun p _ => ⟨by simp, by simp⟩
  | succ n ih =>
    refine (ih.mul hf).mono fun p hp => ⟨?_, ?_⟩
    · obtain ⟨K, hK, h⟩ := hf
      exact pow_nonneg (h p hp).1 _
    · rw [pow_succ]

/-- `(p + K₁)^{K₁} ≤ (p + K₂)^{K₂}` for `2 ≤ K₁ ≤ K₂` and `p ≥ 0`. -/
theorem pow_K_mono {p : ℝ} (hp : 0 ≤ p) {K₁ K₂ : ℕ} (hK₁ : 2 ≤ K₁) (h12 : K₁ ≤ K₂) :
    (p + K₁) ^ K₁ ≤ (p + K₂) ^ K₂ := by
  have h2 : (2 : ℝ) ≤ K₁ := by exact_mod_cast hK₁
  have h1 : (1 : ℝ) ≤ p + K₁ := by linarith
  have h12' : (K₁ : ℝ) ≤ K₂ := by exact_mod_cast h12
  calc (p + K₁) ^ K₁ ≤ (p + K₁) ^ K₂ := pow_le_pow_right₀ h1 h12
    _ ≤ (p + K₂) ^ K₂ := pow_le_pow_left₀ (by linarith) (by linarith) _

/-- `p ≤ (p + K)^K` for `K ≥ 1`, `p ≥ 0`. -/
theorem le_pow_K {p : ℝ} (hp : 0 ≤ p) {K : ℕ} (hK : 2 ≤ K) : p ≤ (p + K) ^ K := by
  have h2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have h1 : (1 : ℝ) ≤ p + K := by linarith
  calc p ≤ p + K := by linarith
    _ ≤ (p + K) ^ K := le_self_pow₀ h1 (by omega)

end PrimeCarleson.Proof.Fplus31

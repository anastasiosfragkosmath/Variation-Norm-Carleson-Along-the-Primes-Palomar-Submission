module

public import PrimeCarleson.Proof.Fplus31.Vinogradov.Quadratic
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The many-dilates Vinogradov lemma, degree at most two, one variable

Vinogradov-type estimate used by the extrapolation step of the iteration of `C2/CMain.lean` (proof
of [F+] Proposition 3.1) (Leng's `l:vinogradov` = [GT14, Lemma 2.3],
arXiv:2312.10772v5 TeX L1471), in a form with the length large,
`L ≥ C δ^{-C}`, and `ε ≤ δ^C / C` (for small `L` the statement without these conditions is false:
`δ = 1/2`, `L = 2`, `Λ = {2}`, `P(ℓ) = (ℓ - 2)/√2`, `ε = 0`).

The distance to the nearest integer is `‖(x : UnitAddCircle)‖ = |x - round x|` (Mathlib's norm on
`AddCircle (1 : ℝ)`; see `Torus.lean`).

* `vinogradov_poly_deg_le_two_explicit`: explicit constants (`10¹²`, `δ⁻¹²`);
* `vinogradov_poly_deg_le_two`: the statement with one absolute `C` (`C = 4 · 10¹²` works).
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- The evaluation of a polynomial of degree at most two. -/
theorem eval_eq_of_natDegree_le_two (P : Polynomial ℝ) (hP : P.natDegree ≤ 2) (x : ℝ) :
    P.eval x = P.coeff 2 * x ^ 2 + P.coeff 1 * x + P.coeff 0 := by
  rw [Polynomial.eval_eq_sum_range' (n := 3) (by omega)]
  simp [Finset.sum_range_succ]
  ring

/-- **Many-dilates Vinogradov lemma, degree at most two, explicit constants.**  Let `P` be a real
polynomial of degree at most `2`, `L` a natural number with `δ⁶ L ≥ 2·10⁶`, and `Λ ⊆ (L/2, L]` a set
of integers with `|Λ| ≥ δ L`.  If `‖P(ℓ)‖_{ℝ/ℤ} ≤ ε` for `ℓ ∈ Λ`, where `10¹² ε ≤ δ¹²`, then there
is a positive integer `q ≤ 2·10⁵ δ⁻⁶` with
`‖q P₂‖ ≤ 4·10¹² ε δ⁻¹² / L²`, `‖q P₁‖ ≤ 2·10¹² ε δ⁻¹² / L` and `‖q P₀‖ ≤ 10¹² ε δ⁻¹²`. -/
theorem vinogradov_poly_deg_le_two_explicit {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 10 ^ 12 * ε ≤ δ ^ 12) (P : Polynomial ℝ) (hP : P.natDegree ≤ 2) (L : ℕ)
    (hL : 2 * 10 ^ 6 ≤ δ ^ 6 * L) (Λ : Finset ℕ)
    (hΛ : ∀ ℓ ∈ Λ, (L : ℝ) / 2 < ℓ ∧ (ℓ : ℝ) ≤ L) (hcard : δ * L ≤ Λ.card)
    (h : ∀ ℓ ∈ Λ, ‖((P.eval (ℓ : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ 2 * 10 ^ 5 / δ ^ 6 ∧
      ‖(((q : ℝ) * P.coeff 2 : ℝ) : UnitAddCircle)‖ ≤ 4 * 10 ^ 12 * ε / (δ ^ 12 * L ^ 2) ∧
      ‖(((q : ℝ) * P.coeff 1 : ℝ) : UnitAddCircle)‖ ≤ 2 * 10 ^ 12 * ε / (δ ^ 12 * L) ∧
      ‖(((q : ℝ) * P.coeff 0 : ℝ) : UnitAddCircle)‖ ≤ 10 ^ 12 * ε / δ ^ 12 := by
  have hL0 : (0 : ℝ) < L := by
    by_contra hcon
    have : (L : ℝ) = 0 := le_antisymm (not_lt.mp hcon) (Nat.cast_nonneg L)
    rw [this] at hL
    norm_num at hL
  have hδ6 : 0 < δ ^ 6 := by positivity
  have hδ12 : 0 < δ ^ 12 := by positivity
  have hΛne : Λ.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < Λ.card := lt_of_lt_of_le (by positivity) hcard
    exact_mod_cast this
  have hε0 : 0 ≤ ε := by
    obtain ⟨ℓ, hℓ⟩ := hΛne
    exact (norm_nonneg _).trans (h ℓ hℓ)
  set K : Finset ℤ := Λ.image (fun ℓ : ℕ => (ℓ : ℤ)) with hK
  have hKcard : K.card = Λ.card := Finset.card_image_of_injective _ Nat.cast_injective
  have hKmem : ∀ k ∈ K, ∃ ℓ ∈ Λ, (ℓ : ℤ) = k := fun k hk => by simpa [hK] using hk
  obtain ⟨q, hq0, hq, hq2, hq1, hq0'⟩ := quadratic_vinogradov (D := δ⁻¹) (ε := ε)
    (a := (L : ℝ) / 2) (M := (L : ℝ) / 2) (a₂ := P.coeff 2) (a₁ := P.coeff 1) (a₀ := P.coeff 0)
    ((one_le_inv₀ hδ).mpr hδ1) hε0
    (by
      have : (10 : ℝ) ^ 12 * ε * δ⁻¹ ^ 12 = 10 ^ 12 * ε / δ ^ 12 := by
        rw [inv_pow]; ring
      rw [this, div_le_one hδ12]
      exact hε)
    (by
      have : (10 : ℝ) ^ 6 * δ⁻¹ ^ 6 = 10 ^ 6 / δ ^ 6 := by rw [inv_pow]; ring
      rw [this, div_le_iff₀ hδ6]
      linarith)
    (by positivity) le_rfl K
    (fun k hk => by
      obtain ⟨ℓ, hℓ, rfl⟩ := hKmem k hk
      obtain ⟨h1, h2⟩ := hΛ ℓ hℓ
      push_cast
      constructor <;> linarith)
    (by
      rw [hKcard]
      have : (L : ℝ) / 2 / δ⁻¹ = δ * L / 2 := by field_simp
      rw [this]
      nlinarith [Nat.cast_nonneg (α := ℝ) Λ.card])
    (fun k hk => by
      obtain ⟨ℓ, hℓ, rfl⟩ := hKmem k hk
      have := h ℓ hℓ
      rw [eval_eq_of_natDegree_le_two P hP] at this
      simpa using this)
  refine ⟨q, hq0, ?_, ?_, ?_, ?_⟩
  · have : 2 * 10 ^ 5 * δ⁻¹ ^ 6 = 2 * 10 ^ 5 / δ ^ 6 := by rw [inv_pow]; ring
    rwa [this] at hq
  · refine hq2.trans (le_of_eq ?_)
    rw [inv_pow]
    field_simp
    ring
  · refine hq1.trans (le_of_eq ?_)
    rw [inv_pow]
    field_simp
  · refine hq0'.trans (le_of_eq ?_)
    rw [inv_pow]
    ring

/-- The elementary bound used to pass from explicit constants to one absolute constant `C`:
`c ε / (δ^m X) ≤ C (δ^n)⁻¹ ε / X` for `0 ≤ c ≤ C`, `m ≤ n` and `0 < δ ≤ 1`. -/
theorem div_pow_mul_le {δ ε c C : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) (hc0 : 0 ≤ c)
    (hc : c ≤ C) {m n : ℕ} (hmn : m ≤ n) {X : ℝ} (hX : 0 < X) :
    c * ε / (δ ^ m * X) ≤ C * (δ ^ n)⁻¹ * ε / X := by
  have hδn : 0 < δ ^ n := by positivity
  have hδm : 0 < δ ^ m := by positivity
  have h1 : δ ^ n ≤ δ ^ m := pow_le_pow_of_le_one hδ.le hδ1 hmn
  have h2 : (δ ^ m)⁻¹ ≤ (δ ^ n)⁻¹ := inv_anti₀ hδn h1
  have h3 : c * ε / (δ ^ m * X) = c * (δ ^ m)⁻¹ * ε / X := by
    field_simp
  rw [h3]
  apply div_le_div_of_nonneg_right _ hX.le
  have h4 : c * (δ ^ m)⁻¹ ≤ C * (δ ^ n)⁻¹ :=
    mul_le_mul hc h2 (by positivity) (hc0.trans hc)
  exact mul_le_mul_of_nonneg_right h4 hε

/-- **Many-dilates Vinogradov lemma, degree at most two** (Leng's `l:vinogradov`,
`Final_Version.tex` L1471, with the length and `ε` conditions below).

There is an absolute constant `C` (one may take `C = 4 · 10¹²`) such that: if `0 < δ ≤ 1`,
`ε ≤ δ^C / C`, `P` is a real polynomial of degree at most `2`, `L ≥ C δ^{-C}` is a natural number,
`Λ ⊆ (L/2, L]` is a set of integers with `|Λ| ≥ δ L`, and `‖P(ℓ)‖_{ℝ/ℤ} ≤ ε` for all `ℓ ∈ Λ`, then
there is a positive integer `q ≤ C δ^{-C}` with `‖q P₂‖ ≤ C δ^{-C} ε / L²`,
`‖q P₁‖ ≤ C δ^{-C} ε / L` and `‖q P₀‖ ≤ C δ^{-C} ε`.  The distance to the nearest integer is
`‖(x : UnitAddCircle)‖ = |x - round x|`. -/
theorem vinogradov_poly_deg_le_two :
    ∃ C : ℕ, ∀ (δ ε : ℝ), 0 < δ → δ ≤ 1 → ε ≤ δ ^ C / C →
      ∀ P : Polynomial ℝ, P.natDegree ≤ 2 → ∀ L : ℕ, (C : ℝ) * (δ ^ C)⁻¹ ≤ L →
        ∀ Λ : Finset ℕ, (∀ ℓ ∈ Λ, (L : ℝ) / 2 < ℓ ∧ (ℓ : ℝ) ≤ L) → δ * L ≤ Λ.card →
          (∀ ℓ ∈ Λ, ‖((P.eval (ℓ : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε) →
          ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ C * (δ ^ C)⁻¹ ∧
            ‖(((q : ℝ) * P.coeff 2 : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / L ^ 2 ∧
            ‖(((q : ℝ) * P.coeff 1 : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / L ∧
            ‖(((q : ℝ) * P.coeff 0 : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε := by
  refine ⟨4 * 10 ^ 12, ?_⟩
  intro δ ε hδ hδ1 hε P hP L hL Λ hΛ hcard h
  have hCr : (((4 * 10 ^ 12 : ℕ)) : ℝ) = 4 * 10 ^ 12 := by push_cast; ring
  rw [hCr] at hε hL ⊢
  set C : ℕ := 4 * 10 ^ 12 with hC
  have hδC : δ ^ C ≤ δ ^ 12 := pow_le_pow_of_le_one hδ.le hδ1 (by norm_num [hC])
  have hδC6 : δ ^ C ≤ δ ^ 6 := pow_le_pow_of_le_one hδ.le hδ1 (by norm_num [hC])
  have hδCpos : 0 < δ ^ C := by positivity
  have hδ12 : 0 < δ ^ 12 := by positivity
  have hL0 : (0 : ℝ) < L := by
    refine lt_of_lt_of_le ?_ hL
    positivity
  have hΛne : Λ.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < Λ.card := lt_of_lt_of_le (by positivity) hcard
    exact_mod_cast this
  have hε0 : 0 ≤ ε := by
    obtain ⟨ℓ, hℓ⟩ := hΛne
    exact (norm_nonneg _).trans (h ℓ hℓ)
  -- hypotheses of the explicit statement
  have hε' : 10 ^ 12 * ε ≤ δ ^ 12 := by
    have h1 : ε * (4 * 10 ^ 12) ≤ δ ^ C := by
      rwa [le_div_iff₀ (by positivity)] at hε
    nlinarith
  have hL' : 2 * 10 ^ 6 ≤ δ ^ 6 * L := by
    have h1 : 4 * 10 ^ 12 ≤ δ ^ C * L := by
      have h2 := mul_le_mul_of_nonneg_left hL hδCpos.le
      have h3 : δ ^ C * (4 * 10 ^ 12 * (δ ^ C)⁻¹) = 4 * 10 ^ 12 := by field_simp
      rw [h3] at h2
      exact h2
    nlinarith
  obtain ⟨q, hq0, hq, hq2, hq1, hq0'⟩ :=
    vinogradov_poly_deg_le_two_explicit hδ hδ1 hε' P hP L hL' Λ hΛ hcard h
  refine ⟨q, hq0, ?_, ?_, ?_, ?_⟩
  · refine hq.trans ?_
    have h1 : (2 * 10 ^ 5 : ℝ) / δ ^ 6 = 2 * 10 ^ 5 * (δ ^ 6)⁻¹ := by ring
    have h2 : (δ ^ 6)⁻¹ ≤ (δ ^ C)⁻¹ := inv_anti₀ hδCpos hδC6
    rw [h1]
    nlinarith [inv_pos.mpr (pow_pos hδ 6), inv_pos.mpr hδCpos]
  · refine hq2.trans ?_
    have := div_pow_mul_le (c := 4 * 10 ^ 12) (C := 4 * 10 ^ 12) hδ hδ1 hε0 (by norm_num) le_rfl
      (m := 12) (n := C) (by norm_num [hC]) (X := (L : ℝ) ^ 2) (by positivity)
    exact this
  · refine hq1.trans ?_
    have := div_pow_mul_le (c := 2 * 10 ^ 12) (C := 4 * 10 ^ 12) hδ hδ1 hε0 (by norm_num)
      (by norm_num) (m := 12) (n := C) (by norm_num [hC]) (X := (L : ℝ)) hL0
    exact this
  · refine hq0'.trans ?_
    have := div_pow_mul_le (c := 10 ^ 12) (C := 4 * 10 ^ 12) hδ hδ1 hε0 (by norm_num)
      (by norm_num) (m := 12) (n := C) (by norm_num [hC]) (X := 1) one_pos
    simpa using this

end PrimeCarleson.Proof.Fplus31

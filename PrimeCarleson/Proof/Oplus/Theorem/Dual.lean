module

public import PrimeCarleson.Proof.Oplus.Theorem.Basic

/-!
# Duality `ℓ^r`-`ℓ^{r'}` and a measurable argmax ([O+] L905-L913)

For the linearization of the chain supremum (Source: [O+], L897–L903):

* `dualCoeff r D`: the coefficients `a_k = conj(D_k) |D_k|^{r-2} / ‖D‖_r^{r-1}` (and `a = e_0` if
  `D = 0`), with `∑_k |a_k|^{r'} = 1` (`sum_norm_dualCoeff_rpow`) and `∑_k D_k a_k = ‖D‖_r`
  (`sum_mul_dualCoeff`), for `r > 2`;
* `exists_measurable_argmax`: for finitely many measurable `φ_j : ℝ → ℝ` there is a measurable
  selection `x ↦ j(x)` of a maximizing index (the first one), so that `x ↦ ψ(j(x))` is measurable
  for every `ψ`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- The `ℓ^r` norm `(∑ |D_i|^r)^{1/r}` of a finite family of complex numbers. -/
def lrNorm (r : ℝ) {K : ℕ} (D : Fin K → ℂ) : ℝ := (∑ i, ‖D i‖ ^ r) ^ (1 / r)

/-- The `ℓ^r` norm is nonnegative. -/
theorem lrNorm_nonneg (r : ℝ) {K : ℕ} (D : Fin K → ℂ) : 0 ≤ lrNorm r D :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _

/-- `‖D‖_r^r = ∑ |D_i|^r`. -/
theorem lrNorm_rpow {r : ℝ} (hr : 0 < r) {K : ℕ} (D : Fin K → ℂ) :
    lrNorm r D ^ r = ∑ i, ‖D i‖ ^ r := by
  unfold lrNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _),
    one_div, inv_mul_cancel₀ hr.ne', Real.rpow_one]

/-- `‖D‖_r = 0` iff `D = 0`. -/
theorem lrNorm_eq_zero_iff {r : ℝ} (hr : 0 < r) {K : ℕ} (D : Fin K → ℂ) :
    lrNorm r D = 0 ↔ ∀ i, D i = 0 := by
  constructor
  · intro h i
    have h1 : ∑ i, ‖D i‖ ^ r = 0 := by
      rw [← lrNorm_rpow hr D, h, Real.zero_rpow hr.ne']
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Real.rpow_nonneg (norm_nonneg (D i)) r)).1 h1 i (Finset.mem_univ i)
    have h3 : ‖D i‖ = 0 := by
      rcases (Real.rpow_eq_zero (norm_nonneg _) hr.ne').1 h2 with h4
      exact h4
    exact norm_eq_zero.1 h3
  · intro h
    unfold lrNorm
    have : ∑ i, ‖D i‖ ^ r = 0 := Finset.sum_eq_zero fun i _ => by
      rw [h i, norm_zero, Real.zero_rpow hr.ne']
    rw [this, Real.zero_rpow (by positivity)]

/-- The dual coefficients `a_k = conj(D_k) |D_k|^{r-2} / ‖D‖_r^{r-1}` (and `a = e_0` if `D = 0`). -/
def dualCoeff (r : ℝ) {n : ℕ} (D : Fin (n + 1) → ℂ) (k : Fin (n + 1)) : ℂ :=
  if lrNorm r D = 0 then (if k = 0 then 1 else 0)
  else (starRingEnd ℂ) (D k) * ((‖D k‖ ^ (r - 2) : ℝ) : ℂ) * ((lrNorm r D ^ (1 - r) : ℝ) : ℂ)

/-- `a · a^{r-2} = a^{r-1}`. -/
theorem mul_rpow_sub_two {r : ℝ} (hr : 2 < r) {a : ℝ} (ha : 0 ≤ a) :
    a * a ^ (r - 2) = a ^ (r - 1) := by
  rw [show r - 1 = 1 + (r - 2) by ring, Real.rpow_add' ha (by linarith), Real.rpow_one]

/-- `a² · a^{r-2} = a^r`. -/
theorem sq_mul_rpow_sub_two {r : ℝ} (hr : 2 < r) {a : ℝ} (ha : 0 ≤ a) :
    a ^ 2 * a ^ (r - 2) = a ^ r := by
  rw [← Real.rpow_two, ← Real.rpow_add' ha (by linarith)]
  congr 1
  ring

/-- `|a_k| = |D_k|^{r-1} / ‖D‖_r^{r-1}` if `D ≠ 0`. -/
theorem norm_dualCoeff {r : ℝ} (hr : 2 < r) {n : ℕ} (D : Fin (n + 1) → ℂ) (k : Fin (n + 1))
    (hN : lrNorm r D ≠ 0) :
    ‖dualCoeff r D k‖ = ‖D k‖ ^ (r - 1) * lrNorm r D ^ (1 - r) := by
  simp only [dualCoeff, hN, ↓reduceIte]
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (lrNorm_nonneg r D) _),
    mul_rpow_sub_two hr (norm_nonneg _)]

/-- **`∑_k |a_k|^{r'} = 1`.** -/
theorem sum_norm_dualCoeff_rpow {r : ℝ} (hr : 2 < r) {n : ℕ} (D : Fin (n + 1) → ℂ) :
    ∑ k, ‖dualCoeff r D k‖ ^ (Real.conjExponent r) = 1 := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  by_cases hN : lrNorm r D = 0
  · have h0 : ∀ k : Fin (n + 1), dualCoeff r D k = if k = 0 then 1 else 0 := fun k => by
      simp only [dualCoeff, hN, ↓reduceIte]
    simp_rw [h0]
    rw [Finset.sum_eq_single (0 : Fin (n + 1))]
    · simp
    · intro k _ hk
      have hcpos : 0 < Real.conjExponent r := by unfold Real.conjExponent; exact div_pos hr0 hr1
      simp [hk, Real.zero_rpow hcpos.ne']
    · simp
  · have hNpos : 0 < lrNorm r D := lt_of_le_of_ne (lrNorm_nonneg r D) (Ne.symm hN)
    have hconj : (r - 1) * Real.conjExponent r = r := by
      unfold Real.conjExponent; field_simp
    have hterm : ∀ k : Fin (n + 1), ‖dualCoeff r D k‖ ^ (Real.conjExponent r) =
        ‖D k‖ ^ r * lrNorm r D ^ (-r) := by
      intro k
      rw [norm_dualCoeff hr D k hN, Real.mul_rpow (Real.rpow_nonneg (norm_nonneg _) _)
        (Real.rpow_nonneg hNpos.le _), ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_mul hNpos.le,
        hconj]
      congr 2
      have : (1 - r) * Real.conjExponent r = -((r - 1) * Real.conjExponent r) := by ring
      rw [this, hconj]
    simp_rw [hterm]
    rw [← Finset.sum_mul, ← lrNorm_rpow hr0 D, ← Real.rpow_add hNpos]
    simp

/-- **`∑_k D_k a_k = ‖D‖_r`.** -/
theorem sum_mul_dualCoeff {r : ℝ} (hr : 2 < r) {n : ℕ} (D : Fin (n + 1) → ℂ) :
    ∑ k, D k * dualCoeff r D k = (lrNorm r D : ℂ) := by
  have hr0 : 0 < r := by linarith
  by_cases hN : lrNorm r D = 0
  · have hD := (lrNorm_eq_zero_iff hr0 D).1 hN
    simp [hD, hN]
  · have hNpos : 0 < lrNorm r D := lt_of_le_of_ne (lrNorm_nonneg r D) (Ne.symm hN)
    have hterm : ∀ k : Fin (n + 1), D k * dualCoeff r D k =
        ((‖D k‖ ^ r * lrNorm r D ^ (1 - r) : ℝ) : ℂ) := by
      intro k
      simp only [dualCoeff, hN, ↓reduceIte]
      have h1 : D k * (starRingEnd ℂ) (D k) = ((‖D k‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      calc D k * ((starRingEnd ℂ) (D k) * ((‖D k‖ ^ (r - 2) : ℝ) : ℂ) *
            ((lrNorm r D ^ (1 - r) : ℝ) : ℂ))
          = (D k * (starRingEnd ℂ) (D k)) * ((‖D k‖ ^ (r - 2) : ℝ) : ℂ) *
            ((lrNorm r D ^ (1 - r) : ℝ) : ℂ) := by ring
        _ = _ := by
          rw [h1]
          push_cast
          rw [← sq_mul_rpow_sub_two hr (norm_nonneg (D k))]
          push_cast
          ring
    simp_rw [hterm]
    rw [← Complex.ofReal_sum, ← Finset.sum_mul, ← lrNorm_rpow hr0 D, ← Real.rpow_add hNpos]
    simp


/-- **Measurable argmax over finitely many measurable functions.** -/
theorem exists_measurable_argmax {N : ℕ} (φ : Fin (N + 1) → ℝ → ℝ) (hφ : ∀ c, Measurable (φ c)) :
    ∃ s : ℝ → Fin (N + 1), (∀ x c, φ c x ≤ φ (s x) x) ∧
      ∀ ψ : Fin (N + 1) → ℝ, Measurable fun x => ψ (s x) := by
  classical
  have hne : ∀ x, (Finset.univ.filter fun j : Fin (N + 1) => ∀ j', φ j' x ≤ φ j x).Nonempty := by
    intro x
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => φ j x) Finset.univ_nonempty
    exact ⟨j, by simpa using hj⟩
  set s : ℝ → Fin (N + 1) := fun x =>
    (Finset.univ.filter fun j : Fin (N + 1) => ∀ j', φ j' x ≤ φ j x).min' (hne x) with hs
  have hmem : ∀ x, ∀ c, φ c x ≤ φ (s x) x := by
    intro x c
    have := Finset.min'_mem _ (hne x)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this c
  refine ⟨s, hmem, fun ψ => ?_⟩
  have hM : ∀ j, MeasurableSet {x | ∀ j', φ j' x ≤ φ j x} := fun j => by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j' => measurableSet_le (hφ j') (hφ j)
  have hsm : Measurable s := by
    refine measurable_to_countable' fun j => ?_
    have hset : s ⁻¹' {j} = {x | ∀ j', φ j' x ≤ φ j x} ∩
        ⋂ j'' ∈ {j'' : Fin (N + 1) | j'' < j}, {x | ∀ j', φ j' x ≤ φ j'' x}ᶜ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
        Set.mem_iInter, Set.mem_compl_iff]
      constructor
      · intro hx
        refine ⟨?_, fun j'' hj'' hmax => ?_⟩
        · rw [← hx]; exact hmem x |> fun h => fun j' => h j'
        · have hmin : s x ≤ j'' :=
            Finset.min'_le _ j'' (by simpa using hmax)
          rw [hx] at hmin
          exact absurd hj'' (not_lt.2 hmin)
      · rintro ⟨hj, hj'⟩
        have hle : s x ≤ j := Finset.min'_le _ j (by simpa using hj)
        by_contra hne'
        have hlt : s x < j := lt_of_le_of_ne hle hne'
        exact hj' (s x) hlt (hmem x)
    rw [hset]
    exact (hM j).inter (MeasurableSet.biInter (Set.to_countable _) fun j'' _ => (hM j'').compl)
  exact (measurable_of_finite ψ).comp hsm


end PrimeCarleson.Proof.Oplus

/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/UnitExpansionCorrelation.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_weighted_term {I : Type*} [Fintype I] (c z : I → ℂ)
    {delta M : ℝ} (hdelta : 0 < delta) (hM : 0 < M)
    (hc : (∑ i, ‖c i‖) ≤ M) (hsum : delta ≤ ‖∑ i, c i * z i‖) :
    ∃ i, delta / M ≤ ‖z i‖ := by
  classical
  have hI : (Finset.univ : Finset I).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty, norm_zero] at hsum
    linarith
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖z i‖) hI
  refine ⟨i, (div_le_iff₀ hM).mpr ?_⟩
  calc
    delta ≤ ‖∑ j, c j * z j‖ := hsum
    _ ≤ ∑ j, ‖c j * z j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖c j‖ * ‖z i‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ _)) (norm_nonneg _)
    _ = (∑ j, ‖c j‖) * ‖z i‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ M * ‖z i‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ = ‖z i‖ * M := mul_comm _ _

theorem sum_pair_coefficient_norms_le {I : Type*} {J : I → Type*}
    [Fintype I] [∀ i, Fintype (J i)] (c : I → ℂ) (d : ∀ i, J i → ℂ)
    {C D : ℝ} (hD : 0 ≤ D) (hc : (∑ i, ‖c i‖) ≤ C)
    (hd : ∀ i, (∑ j, ‖d i j‖) ≤ D) :
    (∑ p : Sigma J, ‖c p.1 * d p.1 p.2‖) ≤ C * D := by
  rw [Fintype.sum_sigma]
  simp_rw [norm_mul, ← Finset.mul_sum]
  calc
    _ ≤ ∑ i, ‖c i‖ * D := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hd i) (norm_nonneg _))
    _ = (∑ i, ‖c i‖) * D := (Finset.sum_mul _ _ _).symm
    _ ≤ C * D := mul_le_mul_of_nonneg_right hc hD

theorem exists_large_weighted_pair {I : Type*} {J : I → Type*}
    [Fintype I] [∀ i, Fintype (J i)] (c : I → ℂ) (d z : ∀ i, J i → ℂ)
    {delta C D : ℝ} (hdelta : 0 < delta) (hC : 0 < C) (hD : 0 < D)
    (hc : (∑ i, ‖c i‖) ≤ C) (hd : ∀ i, (∑ j, ‖d i j‖) ≤ D)
    (hsum : delta ≤ ‖∑ i, ∑ j, (c i * d i j) * z i j‖) :
    ∃ i j, delta / (C * D) ≤ ‖z i j‖ := by
  obtain ⟨p, hp⟩ := exists_large_weighted_term
    (fun p : Sigma J => c p.1 * d p.1 p.2) (fun p => z p.1 p.2)
    hdelta (mul_pos hC hD) (sum_pair_coefficient_norms_le c d hD.le hc hd)
    (by simpa only [Fintype.sum_sigma] using hsum)
  exact ⟨p.1, p.2, hp⟩

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

theorem complex_unit_vector_resolution {K : Type*} [Fintype K] (u : K → ℂ)
    (hu : ∑ k, ‖u k‖ ^ 2 = 1) (z : ℂ) : z = ∑ k, (z * star (u k)) * u k := by
  have hunit : (∑ k, star (u k) * u k) = (1 : ℂ) := by
    calc
      _ = ∑ k, ((‖u k‖ ^ 2 : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
      _ = ((∑ k, ‖u k‖ ^ 2 : ℝ) : ℂ) := (Complex.ofReal_sum _ _).symm
      _ = 1 := by rw [hu, Complex.ofReal_one]
  rw [show (∑ k, (z * star (u k)) * u k) = z * ∑ k, star (u k) * u k by
    rw [Finset.mul_sum]; simp only [mul_assoc], hunit, mul_one]

theorem exists_unit_expansion_correlation {X K : Type*} {A : K → Type*}
    [Fintype K] [∀ k, Fintype (A k)] (s : Finset X)
    (f Q : X → ℂ) (P : K → X → ℂ) (c : ∀ k, A k → ℂ) (psi : ∀ k, A k → X → ℂ)
    (hunit : ∀ x ∈ s, ∑ k, ‖P k x‖ ^ 2 = 1)
    (hexp : ∀ k x, x ∈ s → Q x * star (P k x) = ∑ a, c k a * psi k a x)
    {rho D M : ℝ} (hrho : 0 < rho) (hD : 0 < D) (hM : 0 < M)
    (hcard : (Fintype.card K : ℝ) ≤ D) (hc : ∀ k, (∑ a, ‖c k a‖) ≤ M)
    (hcorr : rho ≤ ‖𝔼 x ∈ s, f x * Q x‖) :
    ∃ k a, rho / (D * M) ≤ ‖𝔼 x ∈ s, f x * P k x * psi k a x‖ := by
  have hpoint (x : X) (hx : x ∈ s) :
      f x * Q x = ∑ k, ∑ a, c k a * (f x * P k x * psi k a x) := by
    rw [complex_unit_vector_resolution (fun k => P k x) (hunit x hx) (Q x), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hexp k x hx, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hmean : (𝔼 x ∈ s, f x * Q x) =
      ∑ k, ∑ a, c k a * (𝔼 x ∈ s, f x * P k x * psi k a x) := by
    calc
      _ = 𝔼 x ∈ s, ∑ k, ∑ a, c k a * (f x * P k x * psi k a x) :=
        Finset.expect_congr rfl hpoint
      _ = _ := by simp_rw [Finset.expect_sum_comm, ← Finset.mul_expect]
  apply exists_large_weighted_pair (fun _ : K => (1 : ℂ)) c
    (fun k a => 𝔼 x ∈ s, f x * P k x * psi k a x) hrho hD hM
  · simpa only [norm_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hcard
  · exact hc
  · simpa only [one_mul, ← hmean] using hcorr

end Erdos3

end

end OAI

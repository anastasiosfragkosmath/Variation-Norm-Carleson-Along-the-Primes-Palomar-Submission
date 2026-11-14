module

public import PrimeCarleson.Proof.Paper.P5.Assembly

/-!
# The coefficients `b(D)` of `w_{Q,B}` on `ℤ/N`

Source: main paper `p:transferprop`, L2153–L2163 and L2266–L2268, and the Ramanujan-sum expansion
of `w_{Q,B}` (L605–L607) used by `e:keyidentity` and by the bounds of `A₁` and `B₁` in `l:A1B1`.

For a block `B` with `N = 𝒬_B = lcm B`, the coefficient `b(D) = μ(q)/φ(q)` when `D/N = a/q` is a
reduced fraction with `q ∈ B`, and `b(D) = 0` otherwise (`bnat B D` for `D < N`; `bcoef B D` the
`N`-periodic extension to `D ∈ ℤ`). Facts:

* `blockWeight_eq_sum_bnat`: `w_{Q,B}(n) = ∑_{D < N} b(D) e(n D/N)`;
* `avg_blockWeight_mul_e`: `N⁻¹ ∑_{r < N} w_{Q,B}(r) e(r j/N) = b(-j)`;
* `sum_norm_sq_bnat_le`: `∑_{D < N} |b(D)|² ≤ ∑_{q ∈ B} 1/φ(q)`
  (the paper's `Q^{o(1)-2} #{a/q : q ∈ B}`).
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-! ### One residue class -/

/-- Exactly one `A ∈ {0, …, N-1}` is congruent to `k` mod `N`. -/
theorem sum_range_dvd {M : Type*} [AddCommMonoid M] {N : ℕ} (hN : 0 < N) (k : ℤ) (G : ℕ → M) :
    ∑ A ∈ Finset.range N, (if (N : ℤ) ∣ k - (A : ℤ) then G A else 0) =
      G (k % (N : ℤ)).toNat := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have h0 : 0 ≤ k % (N : ℤ) := Int.emod_nonneg _ hN'.ne'
  have h1 : k % (N : ℤ) < N := Int.emod_lt_of_pos _ hN'
  have hmem : (k % (N : ℤ)).toNat ∈ Finset.range N := by
    rw [Finset.mem_range]; omega
  rw [Finset.sum_eq_single_of_mem _ hmem]
  · have : (N : ℤ) ∣ k - ((k % (N : ℤ)).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg h0]
      exact ⟨k / (N : ℤ), by rw [Int.emod_def]; ring⟩
    rw [ite_eq_left this]
  · intro A hA hne
    rw [ite_eq_right]
    intro hdvd
    apply hne
    obtain ⟨m, hm⟩ := hdvd
    have hk : k = (A : ℤ) + (N : ℤ) * m := by linarith
    have hA' : (A : ℤ) < N := by exact_mod_cast Finset.mem_range.1 hA
    have : k % (N : ℤ) = (A : ℤ) := by
      rw [hk, Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (by positivity) hA'
    rw [this]
    simp

/-! ### The coefficients -/

/-- `b(D)` for `0 ≤ D < N`: `μ(q)/φ(q)` if `D/N` is a reduced fraction with denominator in `B`,
`0` otherwise (L2160-L2163). -/
def bnat (B : Finset ℕ) (D : ℕ) : ℂ :=
  if ((D : ℚ) / (lcmQ B : ℚ)) ∈ reducedFractions B then coefFrac ((D : ℚ) / (lcmQ B : ℚ)) else 0

/-- `b(D)` for `D ∈ ℤ`, `N`-periodic (`D ∈ ℤ/N`). -/
def bcoef (B : Finset ℕ) (D : ℤ) : ℂ := bnat B (D % (lcmQ B : ℤ)).toNat

theorem bcoef_natCast (B : Finset ℕ) {D : ℕ} (hD : D < lcmQ B) : bcoef B (D : ℤ) = bnat B D := by
  unfold bcoef
  have : (D : ℤ) % (lcmQ B : ℤ) = D := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hD)
  rw [this]
  simp

theorem bcoef_add_period (B : Finset ℕ) (D : ℤ) : bcoef B (D + (lcmQ B : ℤ)) = bcoef B D := by
  unfold bcoef
  rw [Int.add_emod_right]

theorem bcoef_periodic (B : Finset ℕ) : Function.Periodic (bcoef B) (lcmQ B : ℤ) :=
  bcoef_add_period B

/-- The set of residues `D < N` with `D/N` a reduced fraction of `B` maps onto the reduced
fractions. -/
theorem image_filter_eq_reducedFractions {B : Finset ℕ} (hB : ∀ q ∈ B, 0 < q) :
    ((Finset.range (lcmQ B)).filter fun D : ℕ =>
        ((D : ℚ) / (lcmQ B : ℚ)) ∈ reducedFractions B).image
      (fun D : ℕ => (D : ℚ) / (lcmQ B : ℚ)) = reducedFractions B := by
  classical
  have hN : 0 < lcmQ B := lcmQ_pos hB
  have hNq : (lcmQ B : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  ext r
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨D, ⟨_, hD⟩, rfl⟩
    exact hD
  · intro hr
    have hr' := mem_reducedFractions.1 hr
    obtain ⟨m, hm⟩ := dvd_lcmQ hr'.2.2
    have hnum : 0 ≤ r.num := Rat.num_nonneg.2 hr'.1
    have hcast : (lcmQ B : ℚ) * r = ((m * r.num).toNat : ℚ) := by
      have h1 : (r.den : ℚ) * r = r.num := by
        have := Rat.mul_den_eq_num r
        linarith [this, mul_comm (r.den : ℚ) r]
      have h2 : ((m * r.num).toNat : ℤ) = m * r.num := Int.toNat_of_nonneg (by positivity)
      have h3 : (((m * r.num).toNat : ℕ) : ℚ) = ((m : ℚ) * r.num) := by
        have : (((m * r.num).toNat : ℕ) : ℚ) = (((m * r.num).toNat : ℤ) : ℚ) := by norm_cast
        rw [this, h2]; push_cast; ring
      rw [h3, hm]
      push_cast
      rw [← h1]
      ring
    refine ⟨(m * r.num).toNat, ⟨?_, ?_⟩, ?_⟩
    · have : ((m * r.num).toNat : ℚ) < (lcmQ B : ℚ) := by
        rw [← hcast]
        have := hr'.2.1
        have hNpos : (0 : ℚ) < lcmQ B := by exact_mod_cast hN
        nlinarith
      exact_mod_cast this
    · have : (((m * r.num).toNat : ℚ) / (lcmQ B : ℚ)) = r := by
        rw [← hcast]; field_simp
      rw [this]; exact hr
    · rw [← hcast]; field_simp

/-- A sum over the reduced fractions is a sum over the residues `D < N` (`D/N` reduced). -/
theorem sum_reducedFractions_eq_sum_range {M : Type*} [AddCommMonoid M] {B : Finset ℕ}
    (hB : ∀ q ∈ B, 0 < q) (F : ℚ → M) :
    ∑ r ∈ reducedFractions B, F r =
      ∑ D ∈ Finset.range (lcmQ B),
        (if ((D : ℚ) / (lcmQ B : ℚ)) ∈ reducedFractions B then
          F ((D : ℚ) / (lcmQ B : ℚ)) else 0) := by
  classical
  have hNq : (lcmQ B : ℚ) ≠ 0 := by exact_mod_cast (lcmQ_pos hB).ne'
  have hinj : Set.InjOn (fun D : ℕ => (D : ℚ) / (lcmQ B : ℚ))
      (↑((Finset.range (lcmQ B)).filter fun D : ℕ => ((D : ℚ) / (lcmQ B : ℚ)) ∈
        reducedFractions B)) := by
    intro D₁ _ D₂ _ h
    have : (D₁ : ℚ) = D₂ := by
      simp only at h
      field_simp at h
      exact h
    exact_mod_cast this
  have h := Finset.sum_image (f := F) hinj
  rw [image_filter_eq_reducedFractions hB] at h
  rw [h, Finset.sum_filter]

/-- **The Ramanujan-sum expansion** `w_{Q,B}(n) = ∑_{D ∈ ℤ/N} b(D) e(n D/N)` (L2268). -/
theorem blockWeight_eq_sum_bnat {B : Finset ℕ} (hB : ∀ q ∈ B, 0 < q) (n : ℤ) :
    blockWeight B n = ∑ D ∈ Finset.range (lcmQ B), bnat B D * e ((n : ℝ) * D / (lcmQ B : ℝ)) := by
  classical
  rw [blockWeight_eq_sum_reducedFractions,
    sum_reducedFractions_eq_sum_range hB (fun r : ℚ =>
      (((ArithmeticFunction.moebius r.den : ℤ) : ℝ) / (Nat.totient r.den : ℝ) : ℂ) *
        e ((n : ℝ) * (r : ℝ)))]
  refine Finset.sum_congr rfl fun D _ => ?_
  unfold bnat coefFrac
  split_ifs with h
  · congr 2
    push_cast
    ring
  · simp

/-- `N⁻¹ ∑_{r < N} w_{Q,B}(r) e(r j/N) = b(-j)`: orthogonality of the characters of `ℤ/N`. -/
theorem avg_blockWeight_mul_e {B : Finset ℕ} (hB : ∀ q ∈ B, 0 < q) (j : ℤ) :
    ((lcmQ B : ℕ) : ℂ)⁻¹ * ∑ r ∈ Finset.range (lcmQ B),
        blockWeight B (r : ℤ) * e ((r : ℝ) * j / (lcmQ B : ℝ)) = bcoef B (-j) := by
  classical
  have hN : 0 < lcmQ B := lcmQ_pos hB
  have hNC : ((lcmQ B : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : ∀ r : ℕ, blockWeight B (r : ℤ) * e ((r : ℝ) * j / (lcmQ B : ℝ)) =
      ∑ D ∈ Finset.range (lcmQ B), bnat B D * e ((r : ℝ) * ((D : ℤ) + j : ℤ) / (lcmQ B : ℝ)) := by
    intro r
    rw [blockWeight_eq_sum_bnat hB, Finset.sum_mul]
    refine Finset.sum_congr rfl fun D _ => ?_
    rw [mul_assoc, ← e_add]
    congr 2
    push_cast
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ D ∈ Finset.range (lcmQ B),
      ∑ r ∈ Finset.range (lcmQ B), bnat B D * e ((r : ℝ) * ((D : ℤ) + j : ℤ) / (lcmQ B : ℝ)) =
        ((lcmQ B : ℕ) : ℂ) * (if ((lcmQ B : ℕ) : ℤ) ∣ (-j) - (D : ℤ) then bnat B D else 0) := by
    intro D _
    rw [← Finset.mul_sum, sum_range_e_mul_div hN]
    have hiff : ((lcmQ B : ℕ) : ℤ) ∣ ((D : ℤ) + j) ↔ ((lcmQ B : ℕ) : ℤ) ∣ (-j) - (D : ℤ) := by
      rw [← dvd_neg]
      congr! 1
      ring
    by_cases hd : ((lcmQ B : ℕ) : ℤ) ∣ ((D : ℤ) + j)
    · rw [ite_eq_left hd, ite_eq_left (hiff.1 hd)]; ring
    · rw [ite_eq_right hd, ite_eq_right (fun h => hd (hiff.2 h))]; ring
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, sum_range_dvd hN (-j) (bnat B)]
  rw [← mul_assoc, inv_mul_cancel₀ hNC, one_mul]
  rfl

/-- `|μ(q)/φ(q)| ≤ 1/φ(q)`. -/
theorem norm_coefFrac_le (r : ℚ) : ‖coefFrac r‖ ≤ ((Nat.totient r.den : ℝ))⁻¹ := by
  unfold coefFrac
  rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs, abs_div]
  have h1 : |((ArithmeticFunction.moebius r.den : ℤ) : ℝ)| ≤ 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := r.den)
    exact_mod_cast this
  have h2 : (0 : ℝ) ≤ (Nat.totient r.den : ℝ) := Nat.cast_nonneg _
  rw [abs_of_nonneg h2]
  rw [inv_eq_one_div]
  exact div_le_div_of_nonneg_right h1 h2

/-- **The bound for `B₁` of `l:A1B1`, arithmetic part**: `∑_{D ∈ ℤ/N} |b(D)|² ≤ ∑_{q ∈ B} 1/φ(q)`.
-/
theorem sum_norm_sq_bnat_le {B : Finset ℕ} (hB : ∀ q ∈ B, 0 < q) :
    ∑ D ∈ Finset.range (lcmQ B), ‖bnat B D‖ ^ 2 ≤ ∑ q ∈ B, ((Nat.totient q : ℝ))⁻¹ := by
  classical
  have h1 : ∀ D ∈ Finset.range (lcmQ B), ‖bnat B D‖ ^ 2 =
      (if ((D : ℚ) / (lcmQ B : ℚ)) ∈ reducedFractions B then
        ‖coefFrac ((D : ℚ) / (lcmQ B : ℚ))‖ ^ 2 else 0) := by
    intro D _
    unfold bnat
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h1, ← sum_reducedFractions_eq_sum_range hB (fun r => ‖coefFrac r‖ ^ 2),
    sum_reducedFractions]
  refine Finset.sum_le_sum fun q hq => ?_
  have hq0 : 0 < q := hB q hq
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq0
  have hcard : (((Finset.range q).filter (fun a => Nat.Coprime a q)).card : ℝ) = Nat.totient q := by
    rw [Nat.totient_eq_card_coprime]
    congr 2
    ext a
    simp [Nat.coprime_comm]
  calc ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ‖coefFrac ((a : ℚ) / q)‖ ^ 2
      ≤ ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ((Nat.totient q : ℝ))⁻¹ ^ 2 := by
        refine Finset.sum_le_sum fun a ha => ?_
        have hden : ((a : ℚ) / q).den = q := den_natCast_div hq0 (Finset.mem_filter.1 ha).2
        have := norm_coefFrac_le ((a : ℚ) / q)
        rw [hden] at this
        exact pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = ((Nat.totient q : ℝ))⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        field_simp

end PrimeCarleson.Proof.Paper

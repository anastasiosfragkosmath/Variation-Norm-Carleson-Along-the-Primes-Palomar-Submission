module

public import PrimeCarleson.Proof.Paper.P6a.KQFourier
public import PrimeCarleson.Proof.Paper.P6a.Moments
public import PrimeCarleson.Proof.Paper.P6a.KQAnnuli
public import PrimeCarleson.Proof.Paper.P6a.KQDecay

/-!
# The crude `ℓ^s` bound for the `K_Q`-replacement error

Source: main paper `p:red-var`, L1504.
The error weight `w_Q E_Q` is not compactly supported (`E_Q = ∑_{k ≥ k₀} ψ_k - K_Q`, `K_Q`
involves the Schwartz kernel `φ_{N(Q)}`), so `l:crude-lambda-var-scale` is applied on dyadic annuli
and summed: `V^r(T^g) ≤ ∑_j V^r(T^{g 1_{A_j}})`, `‖V^r(T^{g 1_{A_j}} f)‖_{ℓ^s} ≲ 2^{j/r}
‖g 1_{A_j}‖_{ℓ^{r'}} ‖f‖_{ℓ^s}`, which needs `∑_j 2^j sup_{A_j} |E_Q| < ∞`: the decay of the
error kernel.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- The dyadic sum of the annular bounds: `β_j = a` for `j ≤ k₀`, `β_j = c 4^{-j}` for `j > k₀`
satisfy `∑_j 2^j β_j ≤ 2^{k₀+1} a + c 2^{-k₀}`. -/
theorem dyadic_annuli_sum {a c : ℝ} (ha : 0 ≤ a) (k₀ : ℕ) :
    Summable (fun j : ℕ => (2 : ℝ) ^ j * (if j ≤ k₀ then a else c * ((4 : ℝ) ^ j)⁻¹)) ∧
      ∑' j : ℕ, (2 : ℝ) ^ j * (if j ≤ k₀ then a else c * ((4 : ℝ) ^ j)⁻¹) ≤
        2 ^ (k₀ + 1) * a + c * ((2 : ℝ) ^ k₀)⁻¹ := by
  set f : ℕ → ℝ := fun j => (2 : ℝ) ^ j * (if j ≤ k₀ then a else c * ((4 : ℝ) ^ j)⁻¹) with hf
  have hshift : ∀ i : ℕ, f (i + (k₀ + 1)) = c * ((2 : ℝ) ^ k₀)⁻¹ * (1 / 2) ^ (i + 1) := by
    intro i
    have h1 : ¬ (i + (k₀ + 1) ≤ k₀) := by omega
    simp only [hf, h1, ↓reduceIte]
    have h4 : (4 : ℝ) ^ (i + (k₀ + 1)) = ((2 : ℝ) ^ (i + (k₀ + 1))) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h4]
    have : (2 : ℝ) ^ (i + (k₀ + 1)) = 2 ^ i * 2 * 2 ^ k₀ := by ring
    rw [this]
    simp only [one_div, inv_pow]
    field_simp
    ring
  have hsum_shift : Summable (fun i : ℕ => f (i + (k₀ + 1))) := by
    simp_rw [hshift]
    exact (summable_geometric_two.mul_left (1 / 2) |>.congr fun i => by ring).mul_left _
  have hsum : Summable f := (summable_nat_add_iff (k₀ + 1)).1 hsum_shift
  refine ⟨hsum, ?_⟩
  rw [← hsum.sum_add_tsum_nat_add (k₀ + 1)]
  have h1 : ∑ i ∈ Finset.range (k₀ + 1), f i ≤ 2 ^ (k₀ + 1) * a := by
    calc ∑ i ∈ Finset.range (k₀ + 1), f i
        = ∑ i ∈ Finset.range (k₀ + 1), (2 : ℝ) ^ i * a := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have : i ≤ k₀ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          simp only [hf, this, ↓reduceIte]
      _ = a * ∑ i ∈ Finset.range (k₀ + 1), (2 : ℝ) ^ i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ a * 2 ^ (k₀ + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ ha
          rw [geom_sum_eq (by norm_num)]; norm_num
      _ = _ := by ring
  have h2 : ∑' i : ℕ, f (i + (k₀ + 1)) = c * ((2 : ℝ) ^ k₀)⁻¹ := by
    simp_rw [hshift]
    rw [tsum_mul_left]
    have : ∑' i : ℕ, ((1 : ℝ) / 2) ^ (i + 1) = 1 := by
      simp_rw [pow_succ]
      rw [tsum_mul_right, tsum_geometric_two]; norm_num
    rw [this, mul_one]
  rw [h2]
  linarith

/-- The uniform bound `N(Q) 2^{-k₀(Q)} ≤ Θ`. -/
theorem exists_NQ_mul_inv_le (S : KQSetup) :
    ∃ Θ : ℝ, 0 ≤ Θ ∧ ∀ Q : ℕ, 1 ≤ Q → S.P.NQ Q * ((2 : ℝ) ^ S.P.kmin Q)⁻¹ ≤ Θ := by
  obtain ⟨m, hm1, C, hC0, hC⟩ := P5.exists_error_decay S.P S.δ_pos 0
  refine ⟨S.δ / 2 * max 1 C, by have := S.δ_pos; positivity, fun Q hQ => ?_⟩
  have h := hC Q hQ
  simp only [neg_zero, Real.rpow_zero, mul_one] at h
  set R : ℝ := ((2 : ℝ) ^ S.P.kmin Q * (S.δ / (2 * S.P.NQ Q)))⁻¹ with hR
  have hN := S.P.NQ_pos Q
  have hp : (0 : ℝ) < (2 : ℝ) ^ S.P.kmin Q := by positivity
  have hRe : S.P.NQ Q * ((2 : ℝ) ^ S.P.kmin Q)⁻¹ = S.δ / 2 * R := by
    have := S.δ_pos
    rw [hR]; field_simp
  have hR0 : 0 ≤ R := by rw [hR]; have := S.δ_pos; positivity
  have hRle : R ≤ max 1 C := by
    by_cases h1 : R ≤ 1
    · exact h1.trans (le_max_left _ _)
    · push Not at h1
      refine le_trans ?_ (le_max_right _ _)
      calc R = R ^ 1 := (pow_one R).symm
        _ ≤ R ^ m := pow_le_pow_right₀ h1.le hm1
        _ ≤ C := h
  rw [hRe]
  exact mul_le_mul_of_nonneg_left hRle (by have := S.δ_pos; positivity)

/-- The final arithmetic of `KQ_error_crude`. -/
theorem crude_arith {L B m₁ m₂ N p Θ : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (hm₁ : 0 ≤ m₁)
    (hm₂ : 0 ≤ m₂) (hN : 0 ≤ N) (hp : 0 < p) (hΘ : N * p⁻¹ ≤ Θ) :
    2 * p * (4 / 3 * L * (p ^ 2)⁻¹ * (N * m₁)) +
      (2 * (N * m₁) + (2 + 8 * B) * p⁻¹ * (N ^ 2 * m₂)) * p⁻¹ ≤
      8 / 3 * L * m₁ * Θ + 2 * m₁ * Θ + (2 + 8 * B) * m₂ * Θ ^ 2 := by
  set u : ℝ := N * p⁻¹ with hu
  have hu0 : 0 ≤ u := by positivity
  have e : 2 * p * (4 / 3 * L * (p ^ 2)⁻¹ * (N * m₁)) +
      (2 * (N * m₁) + (2 + 8 * B) * p⁻¹ * (N ^ 2 * m₂)) * p⁻¹ =
      8 / 3 * L * m₁ * u + 2 * m₁ * u + (2 + 8 * B) * m₂ * u ^ 2 := by
    rw [hu]; field_simp; ring
  rw [e]
  have h2 : u ^ 2 ≤ Θ ^ 2 := pow_le_pow_left₀ hu0 hΘ 2
  have h3 : 0 ≤ (2 + 8 * B) * m₂ := by positivity
  have h4 : 0 ≤ 8 / 3 * L * m₁ := by positivity
  have h5 : 0 ≤ 2 * m₁ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hΘ h4, mul_le_mul_of_nonneg_left hΘ h5,
    mul_le_mul_of_nonneg_left h2 h3]

/-- **The crude bound for the `K_Q`-replacement error**: for `r > 2`, `s ≥ r'` there is `C` such
that for every `Q ≥ 1`, `‖V^r(∑_n f(x-n) w_Q(n) E_Q(n) e(λ n) : λ)‖_{ℓ^s} ≤ C Q ‖f‖_{ℓ^s}`
(`Q^{O(1)}`). -/
theorem KQ_error_crude (S : KQSetup) {r : ℝ} (hr : 2 < r) {s : ℝ} (hs : r / (r - 1) ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ f : ℤ →₀ ℂ,
      eLpNorm (varOp r (fun n => wQ Q n * errW S Q n) (⇑f)) (ENNReal.ofReal s) Measure.count ≤
        ENNReal.ofReal (C * (Q : ℝ)) * eLpNorm (⇑f) (ENNReal.ofReal s) Measure.count := by
  obtain ⟨CA, hCA, hA⟩ := varOp_le_annuli hr
  obtain ⟨B, hB0, hB⟩ := exists_bound_psi S.ψ
  obtain ⟨L, hL0, hL⟩ := exists_lip_psi S.ψ
  obtain ⟨Θ, hΘ0, hΘ⟩ := exists_NQ_mul_inv_le S
  set m₁ : ℝ := phiMoment S 1 with hm₁
  set m₂ : ℝ := phiMoment S 2 with hm₂
  have hm₁0 : 0 ≤ m₁ := phiMoment_nonneg S 1
  have hm₂0 : 0 ≤ m₂ := phiMoment_nonneg S 2
  set K : ℝ := 8 / 3 * L * m₁ * Θ + 2 * m₁ * Θ + (2 + 8 * B) * m₂ * Θ ^ 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨CA * K, by positivity, fun Q hQ f => ?_⟩
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  set k₀ := S.P.kmin Q with hk₀
  set N : ℝ := S.P.NQ Q with hN
  have hN0 : 0 ≤ N := (S.P.NQ_pos Q).le
  have hp : (0 : ℝ) < (2 : ℝ) ^ k₀ := by positivity
  set a : ℝ := Q * (4 / 3 * L * ((4 : ℝ) ^ k₀)⁻¹ * (N * m₁)) with ha
  set c : ℝ := Q * (2 * (N * m₁) + (2 + 8 * B) * ((2 : ℝ) ^ k₀)⁻¹ * (N ^ 2 * m₂)) with hc
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  set β : ℕ → ℝ := fun j => if j ≤ k₀ then a else c * ((4 : ℝ) ^ j)⁻¹ with hβ
  have hβ0 : ∀ j, 0 ≤ β j := fun j => by
    simp only [hβ]; split_ifs
    · exact ha0
    · positivity
  obtain ⟨hsum, hbound⟩ := dyadic_annuli_sum ha0 k₀
  have hwQ : ∀ n : ℤ, ‖wQ Q n‖ ≤ Q := fun n => by
    have h1 : ‖wQ Q n‖ ≤ ((Finset.Ioc (Q / 2) Q).card : ℝ) :=
      FplusProp21.norm_blockWeight_le_card _ _
    refine h1.trans ?_
    rw [Nat.card_Ioc]
    exact_mod_cast Nat.sub_le _ _
  have hg : ∀ n : ℤ, n ≠ 0 → ‖wQ Q n * errW S Q n‖ ≤ β (Nat.log 2 n.natAbs) := by
    intro n hn
    have hna : n.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hn
    rw [norm_mul]
    by_cases hj : Nat.log 2 n.natAbs ≤ k₀
    · simp only [hβ, hj, ↓reduceIte]
      have h := norm_errW_le_global S hB hL Q n
      rw [ha]
      calc ‖wQ Q n‖ * ‖errW S Q n‖ ≤ Q * ‖errW S Q n‖ :=
            mul_le_mul_of_nonneg_right (hwQ n) (norm_nonneg _)
        _ ≤ Q * (4 / 3 * L * ((4 : ℝ) ^ k₀)⁻¹ * (N * m₁)) :=
            mul_le_mul_of_nonneg_left h hQ0.le
    · push Not at hj
      simp only [hβ, not_le.2 hj, ↓reduceIte]
      have h2j : (2 : ℝ) ^ (Nat.log 2 n.natAbs) ≤ |(n : ℝ)| := by
        have h := Nat.pow_log_le_self 2 hna
        have : ((2 ^ Nat.log 2 n.natAbs : ℕ) : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast h
        rw [Nat.cast_natAbs, Int.cast_abs] at this
        simpa using this
      have hfar : (2 : ℝ) ^ (k₀ + 1) ≤ |(n : ℝ)| :=
        (pow_le_pow_right₀ (by norm_num) hj).trans h2j
      have h := norm_errW_le_far S hB hL hQ n hfar
      have h4j : (4 : ℝ) ^ (Nat.log 2 n.natAbs) ≤ (n : ℝ) ^ 2 := by
        have : (4 : ℝ) ^ (Nat.log 2 n.natAbs) = ((2 : ℝ) ^ (Nat.log 2 n.natAbs)) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [this, ← sq_abs (n : ℝ)]
        exact pow_le_pow_left₀ (by positivity) h2j 2
      have h4pos : (0 : ℝ) < (4 : ℝ) ^ (Nat.log 2 n.natAbs) := by positivity
      set E : ℝ := 2 * (N * m₁) + (2 + 8 * B) * ((2 : ℝ) ^ k₀)⁻¹ * (N ^ 2 * m₂) with hE
      have hE0 : 0 ≤ E := by rw [hE]; positivity
      have h5 : E / (n : ℝ) ^ 2 ≤ E * ((4 : ℝ) ^ (Nat.log 2 n.natAbs))⁻¹ := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ h4pos h4j) hE0
      rw [hc]
      calc ‖wQ Q n‖ * ‖errW S Q n‖ ≤ Q * ‖errW S Q n‖ :=
            mul_le_mul_of_nonneg_right (hwQ n) (norm_nonneg _)
        _ ≤ Q * (E / (n : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h hQ0.le
        _ ≤ Q * (E * ((4 : ℝ) ^ (Nat.log 2 n.natAbs))⁻¹) :=
            mul_le_mul_of_nonneg_left h5 hQ0.le
        _ = _ := by ring
  have hmain := hA (fun n => wQ Q n * errW S Q n) β hβ0 hg hsum s hs f
  refine hmain.trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hT : ∑' j : ℕ, (2 : ℝ) ^ j * β j ≤ Q * K := by
    refine hbound.trans ?_
    have h := crude_arith (N := N) (p := (2 : ℝ) ^ k₀) hL0 hB0 hm₁0 hm₂0 hN0 hp (hΘ Q hQ)
    have e : 2 ^ (k₀ + 1) * a + c * ((2 : ℝ) ^ k₀)⁻¹ = Q *
        (2 * (2 : ℝ) ^ k₀ * (4 / 3 * L * (((2 : ℝ) ^ k₀) ^ 2)⁻¹ * (N * m₁)) +
        (2 * (N * m₁) + (2 + 8 * B) * ((2 : ℝ) ^ k₀)⁻¹ * (N ^ 2 * m₂)) *
          ((2 : ℝ) ^ k₀)⁻¹) := by
      have h4 : (4 : ℝ) ^ k₀ = ((2 : ℝ) ^ k₀) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [ha, hc, h4, pow_succ]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h hQ0.le
  calc CA * ∑' j : ℕ, (2 : ℝ) ^ j * β j ≤ CA * (Q * K) := mul_le_mul_of_nonneg_left hT hCA
    _ = CA * K * Q := by ring

end PrimeCarleson.Proof.Paper

module

public import PrimeCarleson.Proof.Goal0.Ramanujan
public import PrimeCarleson.Frozen.BlockWeight
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Data.Nat.Totient

/-!
# Envelope of the fibre kernels for `p:goal0`

The fibre kernels `K̃_ρ(u) = 𝔼_{l ∈ [D]} w_B(u + d l) e_D(l ρ)` of the proof of Proposition
p:goal0 (Source: main paper `e:Henv`, L2765–L2768) satisfy a pointwise envelope. This replaces
Lemma l:periodicfiber (`sources/Variational_Carleson.tex` L2599–L2743) and gives (e:Henv)
(L2765–L2768); the counting input is Lemma l:elemestat (L2583–L2594).

* `norm_avg_ramanujanSum_le`: for `q₂ ∣ D` and `(d, D) = 1` the average
  `𝔼_{l ∈ [D]} c_{q₂}(u + d l) e(l ρ / D)` has modulus at most `1`, and vanishes unless
  `q₂ · (ρ, D) = D`. Expanding `c_{q₂}` and applying the orthogonality of characters
  (`sum_range_e_mul_div`), the average is `∑ e(a u / q₂)` over the `a ∈ [1, q₂]` coprime to `q₂`
  with `D ∣ a d (D / q₂) + ρ`, and there is at most one such `a`, and none unless
  `q₂ · (ρ, D) = D`;
* `norm_avg_blockWeight_le`: writing `q = (q, d) (q, D)` for `q ∣ d D`, the Ramanujan sum
  factors as `c_q = c_{(q, d)} c_{(q, D)}` and `c_{(q, d)}(u + d l) = c_{(q, d)}(u)`, so
  `|K̃_ρ(u)| ≤ ∑_{q ∈ B, (q, D) (ρ, D) = D} |c_{(q, d)}(u)| / φ(q)`;
* `card_filter_gcd_eq_le`: `q ↦ (q, d)` is injective on `{q ∈ B : (q, D) = t}`;
* `norm_avg_blockWeight_le_card`: `|K̃_ρ(u)| ≤ τ(d) M ∑_{r ∣ d} |c_r(u)|` if `1 / φ(q) ≤ M`
  on `B`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Goal0

/-- The `D`-average of `c_{q₂}(u + d l) e(l ρ / D)` is a sum over at most one frequency. -/
theorem avg_ramanujanSum_eq {d q₂ m : ℕ} (hq : 0 < q₂) (hm : 0 < m) (ρ u : ℤ) :
    ((q₂ * m : ℕ) : ℂ)⁻¹ * ∑ l ∈ Finset.range (q₂ * m),
        ramanujanSum q₂ (u + d * l) * e ((l : ℝ) * ρ / ((q₂ * m : ℕ) : ℝ)) =
      ∑ a ∈ (Finset.Icc 1 q₂).filter
        (fun a => Nat.Coprime a q₂ ∧ ((q₂ * m : ℕ) : ℤ) ∣ (a : ℤ) * d * m + ρ),
        e ((a : ℝ) * u / q₂) := by
  have hD : 0 < q₂ * m := Nat.mul_pos hq hm
  have hqR : (q₂ : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hDC : ((q₂ * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  unfold ramanujanSum
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have step : ∀ a ∈ (Finset.Icc 1 q₂).filter (fun a => Nat.Coprime a q₂),
      ∑ l ∈ Finset.range (q₂ * m), e ((a : ℝ) * ((u + d * l : ℤ) : ℝ) / q₂) *
          e ((l : ℝ) * ρ / ((q₂ * m : ℕ) : ℝ)) =
        e ((a : ℝ) * u / q₂) * (if ((q₂ * m : ℕ) : ℤ) ∣ (a : ℤ) * d * m + ρ
          then ((q₂ * m : ℕ) : ℂ) else 0) := by
    intro a _
    rw [← sum_range_e_mul_div hD, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← e_add, ← e_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl step]
  rw [Finset.sum_filter, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h1 h2 h3 h4 h5
  all_goals first
    | (exfalso; tauto)
    | (rw [mul_comm, mul_assoc, mul_inv_cancel₀ hDC, mul_one])
    | simp

/-- The frequencies `a` surviving the orthogonality are unique. -/
theorem eq_of_dvd_mul_add {d q₂ m : ℕ} (hm : 0 < m) (hdq : d.Coprime q₂) (ρ : ℤ) {a a' : ℕ}
    (ha : a ∈ Finset.Icc 1 q₂) (ha' : a' ∈ Finset.Icc 1 q₂)
    (h : ((q₂ * m : ℕ) : ℤ) ∣ (a : ℤ) * d * m + ρ)
    (h' : ((q₂ * m : ℕ) : ℤ) ∣ (a' : ℤ) * d * m + ρ) : a = a' := by
  rw [Finset.mem_Icc] at ha ha'
  have h1 : ((q₂ * m : ℕ) : ℤ) ∣ (((a : ℤ) - a') * d) * m := by
    have := dvd_sub h h'
    convert this using 1
    ring
  have hmZ : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Nat.cast_mul, mul_dvd_mul_iff_right hmZ] at h1
  have hcop : IsCoprime (q₂ : ℤ) (d : ℤ) := Nat.isCoprime_iff_coprime.mpr hdq.symm
  have h2 : (q₂ : ℤ) ∣ (a : ℤ) - a' := hcop.dvd_of_dvd_mul_right h1
  have h3 : (a : ℤ) - a' = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd h2 ?_
    rw [abs_lt]
    constructor <;> omega
  omega

/-- If a frequency survives, then `q₂ · (ρ, D) = D`. -/
theorem mul_gcd_eq_of_dvd_mul_add {d q₂ m : ℕ} (hm : 0 < m) (hdq : d.Coprime q₂)
    (ρ : ℤ) {a : ℕ} (ha : a.Coprime q₂) (h : ((q₂ * m : ℕ) : ℤ) ∣ (a : ℤ) * d * m + ρ) :
    q₂ * Int.gcd ρ ((q₂ * m : ℕ) : ℤ) = q₂ * m := by
  have hmZ : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmρ : (m : ℤ) ∣ ρ := by
    have h1 : (m : ℤ) ∣ (a : ℤ) * d * m + ρ :=
      dvd_trans ⟨q₂, by push_cast; ring⟩ h
    exact (dvd_add_right (Dvd.intro_left _ rfl)).mp h1
  obtain ⟨ρ', rfl⟩ := hmρ
  have h2 : (q₂ : ℤ) ∣ (a : ℤ) * d + ρ' := by
    have : ((q₂ : ℤ) * m) ∣ ((a : ℤ) * d + ρ') * m := by
      convert h using 1
      · push_cast; ring
      · ring
    exact (mul_dvd_mul_iff_right hmZ).mp this
  obtain ⟨k, hk⟩ := h2
  have hcopA : IsCoprime ((a : ℤ) * d) (q₂ : ℤ) :=
    (Nat.isCoprime_iff_coprime.mpr ha).mul_left (Nat.isCoprime_iff_coprime.mpr hdq)
  have hρ' : IsCoprime ρ' (q₂ : ℤ) := by
    have : ρ' = -((a : ℤ) * d) + q₂ * k := by linarith
    rw [this]
    exact hcopA.neg_left.add_mul_left_left k
  have hg : Int.gcd ρ' q₂ = 1 := Int.isCoprime_iff_gcd_eq_one.mp hρ'
  have : Int.gcd ((m : ℤ) * ρ') ((q₂ * m : ℕ) : ℤ) = m := by
    rw [Nat.cast_mul, mul_comm (q₂ : ℤ) m, Int.gcd_mul_left, hg]
    simp
  rw [this]

/-- The `D`-average of `c_{q₂}(u + d l) e(l ρ / D)`: modulus at most 1, and zero unless
`q₂ · (ρ, D) = D`. -/
theorem norm_avg_ramanujanSum_le {d D q₂ : ℕ} (hD : 0 < D) (hdD : d.Coprime D) (hq : q₂ ∣ D)
    (ρ u : ℤ) :
    ‖(D : ℂ)⁻¹ * ∑ l ∈ Finset.range D, ramanujanSum q₂ (u + d * l) * e ((l : ℝ) * ρ / D)‖ ≤
      if q₂ * Int.gcd ρ D = D then 1 else 0 := by
  obtain ⟨m, rfl⟩ := hq
  have hq0 : 0 < q₂ := Nat.pos_of_ne_zero (by rintro rfl; simp at hD)
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hD)
  have hdq : d.Coprime q₂ := Nat.Coprime.coprime_mul_right_right hdD
  rw [avg_ramanujanSum_eq hq0 hm0]
  set S := (Finset.Icc 1 q₂).filter
    (fun a => Nat.Coprime a q₂ ∧ ((q₂ * m : ℕ) : ℤ) ∣ (a : ℤ) * d * m + ρ) with hS
  have hcard : S.card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha a' ha' => ?_
    rw [hS, Finset.mem_filter] at ha ha'
    exact eq_of_dvd_mul_add hm0 hdq ρ ha.1 ha'.1 ha.2.2 ha'.2.2
  have hnorm : ‖∑ a ∈ S, e ((a : ℝ) * u / q₂)‖ ≤ S.card := by
    refine (norm_sum_le _ _).trans ?_
    simp [norm_e]
  split_ifs with h
  · exact hnorm.trans (by exact_mod_cast hcard)
  · have hS0 : S = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun a ha => h ?_
      rw [hS, Finset.mem_filter] at ha
      exact mul_gcd_eq_of_dvd_mul_add hm0 hdq ρ ha.2.1 ha.2.2
    rw [hS0]
    simp

/-- `q = (q, d) (q, D)` for `q ∣ d D` with `(d, D) = 1`. -/
theorem eq_gcd_mul_gcd {d D q : ℕ} (hdD : d.Coprime D) (hq : q ∣ d * D) :
    q = Nat.gcd q d * Nat.gcd q D := by
  rw [← Nat.Coprime.gcd_mul q hdD, Nat.gcd_eq_left hq]

/-- For `q ∣ d D` with `(d, D) = 1`: `c_q(u + d k) = c_{(q, d)}(u) c_{(q, D)}(u + d k)`. -/
theorem ramanujanSum_add_mul_gcd {d D q : ℕ} (hdD : d.Coprime D) (hq : q ∣ d * D) (u k : ℤ) :
    ramanujanSum q (u + d * k) =
      ramanujanSum (Nat.gcd q d) u * ramanujanSum (Nat.gcd q D) (u + d * k) := by
  have hcop : (Nat.gcd q d).Coprime (Nat.gcd q D) :=
    (hdD.coprime_dvd_left (Nat.gcd_dvd_right q d)).coprime_dvd_right (Nat.gcd_dvd_right q D)
  have h1 : ∀ q₁ : ℕ, q₁ ∣ d → ramanujanSum q₁ (u + d * k) = ramanujanSum q₁ u := by
    intro q₁ ⟨k', hk'⟩
    have : u + (d : ℤ) * k = u + q₁ * (k' * k) := by rw [hk']; push_cast; ring
    rw [this, ramanujanSum_add_mul]
  conv_lhs => rw [eq_gcd_mul_gcd hdD hq]
  rw [ramanujanSum_mul hcop, h1 _ (Nat.gcd_dvd_right q d)]

/-- `|μ(q) / φ(q)| ≤ 1 / φ(q)`. -/
theorem norm_moebius_div_totient_le (q : ℕ) :
    ‖(((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ) : ℂ)‖ ≤
      ((Nat.totient q : ℝ))⁻¹ := by
  rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs, abs_div, Nat.abs_cast,
    div_eq_mul_inv]
  calc |((ArithmeticFunction.moebius q : ℤ) : ℝ)| * ((Nat.totient q : ℝ))⁻¹
      ≤ 1 * ((Nat.totient q : ℝ))⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (Nat.cast_nonneg _))
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    _ = ((Nat.totient q : ℝ))⁻¹ := one_mul _

/-- Envelope of the fibre kernel `K̃_ρ(u) = E_{l ∈ [D]} w_B(u + d l) e_D(l ρ)`. -/
theorem norm_avg_blockWeight_le {B : Finset ℕ} {d D : ℕ} (hD : 0 < D) (hdD : d.Coprime D)
    (hB : ∀ q ∈ B, q ∣ d * D) (ρ u : ℤ) :
    ‖(D : ℂ)⁻¹ * ∑ l ∈ Finset.range D, blockWeight B (u + d * l) * e ((l : ℝ) * ρ / D)‖ ≤
      ∑ q ∈ B with Nat.gcd q D * Int.gcd ρ D = D,
        ‖ramanujanSum (Nat.gcd q d) u‖ / (q.totient : ℝ) := by
  unfold blockWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_filter]
  refine Finset.sum_le_sum fun q hqB => ?_
  set c : ℂ := (((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ) : ℂ) with hc
  have key : (D : ℂ)⁻¹ * ∑ l ∈ Finset.range D,
      c * ramanujanSum q (u + d * l) * e ((l : ℝ) * ρ / D) =
      c * ramanujanSum (Nat.gcd q d) u * ((D : ℂ)⁻¹ * ∑ l ∈ Finset.range D,
        ramanujanSum (Nat.gcd q D) (u + d * l) * e ((l : ℝ) * ρ / D)) := by
    have : ∀ l ∈ Finset.range D, c * ramanujanSum q (u + d * l) * e ((l : ℝ) * ρ / D) =
        c * ramanujanSum (Nat.gcd q d) u *
          (ramanujanSum (Nat.gcd q D) (u + d * l) * e ((l : ℝ) * ρ / D)) := by
      intro l _
      rw [ramanujanSum_add_mul_gcd hdD (hB q hqB) u l]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    ring
  rw [key, norm_mul, norm_mul]
  have hX := norm_avg_ramanujanSum_le hD hdD (Nat.gcd_dvd_right q D) ρ u
  have hcn := norm_moebius_div_totient_le q
  rw [← hc] at hcn
  split_ifs at hX ⊢ with h
  · calc ‖c‖ * ‖ramanujanSum (Nat.gcd q d) u‖ *
          ‖(D : ℂ)⁻¹ * ∑ l ∈ Finset.range D,
            ramanujanSum (Nat.gcd q D) (u + d * l) * e ((l : ℝ) * ρ / D)‖
        ≤ ((Nat.totient q : ℝ))⁻¹ * ‖ramanujanSum (Nat.gcd q d) u‖ * 1 := by
          gcongr
      _ = ‖ramanujanSum (Nat.gcd q d) u‖ / (Nat.totient q : ℝ) := by ring
  · have h0 : ‖(D : ℂ)⁻¹ * ∑ l ∈ Finset.range D,
        ramanujanSum (Nat.gcd q D) (u + d * l) * e ((l : ℝ) * ρ / D)‖ = 0 :=
      le_antisymm hX (norm_nonneg _)
    rw [h0, mul_zero]

/-- `q ↦ (q, d)` is injective on `{q ∈ B : (q, D) = t}`, so it has at most `τ(d)` elements
(as in Lemma l:elemestat, L2583–L2594). -/
theorem card_filter_gcd_eq_le {B : Finset ℕ} {d D : ℕ} (hd : 0 < d) (hdD : d.Coprime D)
    (hB : ∀ q ∈ B, q ∣ d * D) (t : ℕ) :
    (B.filter (fun q => Nat.gcd q D = t)).card ≤ d.divisors.card := by
  refine Finset.card_le_card_of_injOn (fun q => Nat.gcd q d) ?_ ?_
  · intro q _
    rw [Finset.mem_coe, Nat.mem_divisors]
    exact ⟨Nat.gcd_dvd_right q d, hd.ne'⟩
  · intro q hq q' hq' h
    rw [Finset.mem_coe, Finset.mem_filter] at hq hq'
    have h1 := eq_gcd_mul_gcd hdD (hB q hq.1)
    have h2 := eq_gcd_mul_gcd hdD (hB q' hq'.1)
    simp only at h
    rw [h1, h2, h, hq.2, hq'.2]

/-- Packaged envelope: `|K̃_ρ(u)| ≤ τ(d) M ∑_{r ∣ d} |c_r(u)|` when `1/φ(q) ≤ M` on `B`. -/
theorem norm_avg_blockWeight_le_card {B : Finset ℕ} {d D : ℕ} (hd : 0 < d) (hD : 0 < D)
    (hdD : d.Coprime D) (hB : ∀ q ∈ B, q ∣ d * D) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ q ∈ B, ((q.totient : ℝ))⁻¹ ≤ M) (ρ u : ℤ) :
    ‖(D : ℂ)⁻¹ * ∑ l ∈ Finset.range D, blockWeight B (u + d * l) * e ((l : ℝ) * ρ / D)‖ ≤
      d.divisors.card * M * ∑ r ∈ d.divisors, ‖ramanujanSum r u‖ := by
  refine (norm_avg_blockWeight_le hD hdD hB ρ u).trans ?_
  have hg : 0 < Int.gcd ρ D := Int.gcd_pos_of_ne_zero_right ρ (by exact_mod_cast hD.ne')
  set S : ℝ := ∑ r ∈ d.divisors, ‖ramanujanSum r u‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun r _ => norm_nonneg _
  have hsub : (B.filter fun q => Nat.gcd q D * Int.gcd ρ D = D) ⊆
      B.filter fun q => Nat.gcd q D = D / Int.gcd ρ D := by
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, (Nat.div_eq_of_eq_mul_left hg hq.2.symm).symm⟩
  have hcard := (Finset.card_le_card hsub).trans
    (card_filter_gcd_eq_le hd hdD hB (D / Int.gcd ρ D))
  calc ∑ q ∈ B with Nat.gcd q D * Int.gcd ρ D = D,
        ‖ramanujanSum (Nat.gcd q d) u‖ / (q.totient : ℝ)
      ≤ ∑ q ∈ B with Nat.gcd q D * Int.gcd ρ D = D, M * S := by
        refine Finset.sum_le_sum fun q hq => ?_
        rw [Finset.mem_filter] at hq
        have h1 : ‖ramanujanSum (Nat.gcd q d) u‖ ≤ S :=
          Finset.single_le_sum (f := fun r => ‖ramanujanSum r u‖) (fun r _ => norm_nonneg _)
            (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right q d, hd.ne'⟩)
        rw [div_eq_mul_inv, mul_comm]
        exact mul_le_mul (hM q hq.1) h1 (norm_nonneg _) hM0
    _ = ((B.filter fun q => Nat.gcd q D * Int.gcd ρ D = D).card : ℝ) * (M * S) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ d.divisors.card * (M * S) := by
        gcongr
    _ = d.divisors.card * M * S := by ring

end PrimeCarleson.Proof.Goal0

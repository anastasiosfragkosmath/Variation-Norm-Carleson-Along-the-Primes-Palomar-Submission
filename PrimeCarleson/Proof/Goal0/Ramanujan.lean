module

public import PrimeCarleson.Proof.Goal0.Basic
public import PrimeCarleson.Frozen.RamanujanSum
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Divisors

/-!
# Ramanujan-sum identities for the proof of `p:goal0`

Facts about the Ramanujan sum `PrimeCarleson.ramanujanSum`
`c_q(n) = ∑_{1 ≤ a ≤ q, (a, q) = 1} e(a n / q)` used in `sources/Variational_Carleson.tex`
((e:ram) L587-L589, the proof of the periodic-fiber lemma L2308-L2312, and the proof of
(e:supLest) L2611-L2621):

* `ramanujanSum_eq_sum_divisors` (the evaluation of Ramanujan sums, a classical fact):
  `c_q(n) = ∑_{f ∣ (q, n)} f μ(q / f)`, from `1_{(a, q) = 1} = ∑_{g ∣ (a, q)} μ(g)` and the
  orthogonality of characters (`sum_range_e_mul_div`, a folklore fact);
* `ramanujanSum_add_mul`: `c_q(n + q k) = c_q(n)`;
* `ramanujanSum_mul` (Source: main paper `e:ram`, L587–L589): `c_{q₁ q₂} = c_{q₁} c_{q₂}`
  for coprime `q₁, q₂`, since `c_q(n)` is the Dirichlet convolution of the multiplicative
  functions `f ↦ f 1_{f ∣ n}` and `μ`;
* `norm_ramanujanSum_le` and `sum_norm_ramanujanSum_le` (Source: main paper `e:supLest`,
L2611–L2615): `‖c_q(n)‖ ≤ ∑_{f ∣ (q, n)} f` and
  `∑_{u < d} ‖c_r(u)‖ ≤ d τ(r)` for `r ∣ d`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Goal0

/-- `∑_{d ∣ n} μ d = 1_{n = 1}`. -/
theorem sum_divisors_moebius_eq_ite (n : ℕ) :
    ∑ d ∈ n.divisors, ArithmeticFunction.moebius d = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply] at h
  rw [h]
  simp [ArithmeticFunction.one_apply]

/-- Indicator of coprimality through the Möbius function. -/
theorem ite_coprime_eq_sum_moebius {q : ℕ} (hq : q ≠ 0) (a : ℕ) :
    (if Nat.Coprime a q then (1 : ℂ) else 0) =
      ∑ g ∈ q.divisors with g ∣ a, ((ArithmeticFunction.moebius g : ℤ) : ℂ) := by
  have hdiv : (Nat.gcd a q).divisors = q.divisors.filter (· ∣ a) := by
    ext g
    simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
    have : Nat.gcd a q ≠ 0 := Nat.gcd_ne_zero_right hq
    tauto
  have h := sum_divisors_moebius_eq_ite (Nat.gcd a q)
  rw [hdiv] at h
  have h' := congrArg (fun z : ℤ => (z : ℂ)) h
  simp only [Int.cast_sum] at h'
  rw [h']
  unfold Nat.Coprime
  split_ifs <;> simp_all

/-- Shifting `[1, m]` to `[0, m)`. -/
theorem sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (m : ℕ) (F : ℕ → M) :
    ∑ b ∈ Finset.Icc 1 m, F b = ∑ b ∈ Finset.range m, F (b + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

/-- Orthogonality of characters over the period `[1, m]`. -/
theorem sum_Icc_e_mul_div {m : ℕ} (hm : 0 < m) (n : ℤ) :
    ∑ b ∈ Finset.Icc 1 m, e ((b : ℝ) * n / m) = if (m : ℤ) ∣ n then (m : ℂ) else 0 := by
  rw [sum_Icc_one_eq_sum_range m (fun b => e ((b : ℝ) * n / m))]
  have hper : Function.Periodic (fun x : ℤ => e ((x : ℝ) * n / m)) (m : ℕ) := by
    intro x
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have : (((x + (m : ℕ) : ℤ) : ℝ) * n / m) = (x : ℝ) * n / m + (n : ℤ) := by
      push_cast
      field_simp
    simp only [this, e_add_intCast]
  have h1 := sum_range_add_of_periodic hper 1
  have h2 := sum_range_e_mul_div hm n
  rw [← h2]
  calc ∑ b ∈ Finset.range m, e (((b + 1 : ℕ) : ℝ) * n / m)
      = ∑ l ∈ Finset.range m, e ((((l : ℤ) + 1 : ℤ) : ℝ) * n / m) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        push_cast
        rfl
    _ = ∑ l ∈ Finset.range m, e ((((l : ℤ) : ℝ)) * n / m) := h1
    _ = ∑ l ∈ Finset.range m, e ((l : ℝ) * n / m) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        simp

/-- The multiples of `g` in `[1, g m]` are `g b` with `b ∈ [1, m]`. -/
theorem sum_filter_dvd_Icc {M : Type*} [AddCommMonoid M] {g : ℕ} (hg : 0 < g) (m : ℕ)
    (F : ℕ → M) :
    ∑ a ∈ (Finset.Icc 1 (g * m)).filter (g ∣ ·), F a = ∑ b ∈ Finset.Icc 1 m, F (g * b) := by
  refine Finset.sum_nbij' (fun a => a / g) (fun b => g * b) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha ⊢
    obtain ⟨⟨h1, h2⟩, c, rfl⟩ := ha
    rw [Nat.mul_div_cancel_left _ hg]
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos c with rfl | h
      · simp at h1
      · exact h
    · exact Nat.le_of_mul_le_mul_left h2 hg
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_Icc] at hb ⊢
    refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
    · exact Nat.mul_pos hg hb.1
    · exact Nat.mul_le_mul_left g hb.2
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    exact Nat.mul_div_cancel' ha.2
  · intro b hb
    exact Nat.mul_div_cancel_left _ hg
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    rw [Nat.mul_div_cancel' ha.2]

/-- The part of the Ramanujan sum coming from the multiples of `g`. -/
theorem sum_filter_dvd_e {g m : ℕ} (hg : 0 < g) (hm : 0 < m) (n : ℤ) :
    ∑ a ∈ (Finset.Icc 1 (g * m)).filter (g ∣ ·), e ((a : ℝ) * n / ((g * m : ℕ) : ℝ)) =
      if (m : ℤ) ∣ n then (m : ℂ) else 0 := by
  rw [sum_filter_dvd_Icc hg m (fun a => e ((a : ℝ) * n / ((g * m : ℕ) : ℝ)))]
  rw [← sum_Icc_e_mul_div hm n]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  congr 1
  push_cast
  field_simp

/-- `c_q(n) = ∑_{f ∣ (q, n)} f μ(q / f)` (the classical evaluation). -/
theorem ramanujanSum_eq_sum_divisors (q : ℕ) (n : ℤ) :
    ramanujanSum q n = ∑ f ∈ q.divisors with ((f : ℕ) : ℤ) ∣ n,
      (f : ℂ) * ((ArithmeticFunction.moebius (q / f) : ℤ) : ℂ) := by
  by_cases hq : q = 0
  · subst hq
    simp [ramanujanSum]
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq
  unfold ramanujanSum
  rw [Finset.sum_filter]
  have step1 : ∀ a ∈ Finset.Icc 1 q,
      (if Nat.Coprime a q then e ((a : ℝ) * n / q) else 0) =
        ∑ g ∈ q.divisors, if g ∣ a then ((ArithmeticFunction.moebius g : ℤ) : ℂ) *
          e ((a : ℝ) * n / q) else 0 := by
    intro a _
    have h := ite_coprime_eq_sum_moebius hq a
    rw [← Finset.sum_filter, ← Finset.sum_mul, ← h]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  have step2 : ∀ g ∈ q.divisors,
      (∑ a ∈ Finset.Icc 1 q, if g ∣ a then ((ArithmeticFunction.moebius g : ℤ) : ℂ) *
          e ((a : ℝ) * n / q) else 0) =
        if ((q / g : ℕ) : ℤ) ∣ n then ((ArithmeticFunction.moebius g : ℤ) : ℂ) * (q / g : ℕ)
          else 0 := by
    intro g hg
    rw [Nat.mem_divisors] at hg
    obtain ⟨⟨m, hm⟩, -⟩ := hg
    have hgpos : 0 < g := Nat.pos_of_ne_zero (by rintro rfl; exact hq (by simpa using hm))
    have hmpos : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hq (by simpa using hm))
    have hqg : q / g = m := by rw [hm, Nat.mul_div_cancel_left _ hgpos]
    rw [← Finset.sum_filter, ← Finset.mul_sum, hqg]
    have := sum_filter_dvd_e hgpos hmpos n
    rw [← hm] at this
    rw [this]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl step2, Finset.sum_filter]
  rw [← Nat.sum_div_divisors q (fun f => if (f : ℤ) ∣ n then
    (f : ℂ) * ((ArithmeticFunction.moebius (q / f) : ℤ) : ℂ) else 0)]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [Nat.mem_divisors] at hg
  rw [Nat.div_div_self hg.1 hq]
  split_ifs <;> ring

/-- The Ramanujan sum `c_q(n)` is `q`-periodic in `n`. -/
theorem ramanujanSum_add_mul (q : ℕ) (n k : ℤ) :
    ramanujanSum q (n + q * k) = ramanujanSum q n := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [ramanujanSum]
  unfold ramanujanSum
  refine Finset.sum_congr rfl fun a _ => ?_
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have : (a : ℝ) * ((n + q * k : ℤ) : ℝ) / q = (a : ℝ) * n / q + ((a * k : ℤ) : ℝ) := by
    push_cast
    field_simp
  rw [this, e_add_intCast]

/-- `f ↦ f 1_{f ∣ n}` as an arithmetic function. -/
def divisorWeight (n : ℤ) : ArithmeticFunction ℂ :=
  ⟨fun f => if (f : ℤ) ∣ n then (f : ℂ) else 0, by simp⟩

/-- Evaluation of `divisorWeight`. -/
theorem divisorWeight_apply (n : ℤ) (f : ℕ) :
    divisorWeight n f = if (f : ℤ) ∣ n then (f : ℂ) else 0 := rfl

/-- `f ↦ f 1_{f ∣ n}` is multiplicative. -/
theorem isMultiplicative_divisorWeight (n : ℤ) : (divisorWeight n).IsMultiplicative := by
  refine ⟨by simp [divisorWeight_apply], fun {m k} hmk => ?_⟩
  have hc : IsCoprime (m : ℤ) (k : ℤ) := Nat.isCoprime_iff_coprime.mpr hmk
  have key : ((m * k : ℕ) : ℤ) ∣ n ↔ (m : ℤ) ∣ n ∧ (k : ℤ) ∣ n := by
    refine ⟨fun h => ⟨dvd_trans ⟨k, by push_cast; ring⟩ h, dvd_trans ⟨m, by push_cast; ring⟩ h⟩,
      fun h => ?_⟩
    rw [Nat.cast_mul]
    exact hc.mul_dvd h.1 h.2
  simp only [divisorWeight_apply, key]
  by_cases h1 : (m : ℤ) ∣ n <;> by_cases h2 : (k : ℤ) ∣ n <;> simp [h1, h2]

/-- The Ramanujan sum as a Dirichlet convolution. -/
theorem ramanujanSum_eq_mul_apply (q : ℕ) (n : ℤ) :
    ramanujanSum q n = (divisorWeight n *
      ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)) q := by
  rw [ramanujanSum_eq_sum_divisors, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun i j => divisorWeight n i *
      ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) j),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [divisorWeight_apply, ArithmeticFunction.intCoe_apply]
  split_ifs <;> simp

/-- The Ramanujan sum `c_q(n)` is multiplicative in `q`. -/
theorem ramanujanSum_mul {q₁ q₂ : ℕ} (h : q₁.Coprime q₂) (n : ℤ) :
    ramanujanSum (q₁ * q₂) n = ramanujanSum q₁ n * ramanujanSum q₂ n := by
  rw [ramanujanSum_eq_mul_apply, ramanujanSum_eq_mul_apply, ramanujanSum_eq_mul_apply]
  exact ((isMultiplicative_divisorWeight n).mul
    ArithmeticFunction.isMultiplicative_moebius.intCast).map_mul_of_coprime h

/-- `‖c_q(n)‖ ≤ ∑_{f ∣ (q, n)} f`. -/
theorem norm_ramanujanSum_le (q : ℕ) (n : ℤ) :
    ‖ramanujanSum q n‖ ≤ ∑ f ∈ q.divisors with ((f : ℕ) : ℤ) ∣ n, (f : ℝ) := by
  rw [ramanujanSum_eq_sum_divisors]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun f _ => ?_)
  rw [norm_mul, Complex.norm_natCast, Complex.norm_intCast]
  have := (ArithmeticFunction.abs_moebius_le_one (n := q / f))
  have h0 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  calc (f : ℝ) * |((ArithmeticFunction.moebius (q / f) : ℤ) : ℝ)| ≤ f * 1 := by
        apply mul_le_mul_of_nonneg_left _ h0
        exact_mod_cast this
    _ = f := mul_one _

/-- The number of multiples of `f` in `[0, f m)` is `m`. -/
theorem card_filter_dvd_range {f : ℕ} (hf : 0 < f) (m : ℕ) :
    ((Finset.range (f * m)).filter (f ∣ ·)).card = m := by
  have : (Finset.range (f * m)).filter (f ∣ ·) = (Finset.range m).image (f * ·) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hu, c, rfl⟩
      exact ⟨c, Nat.lt_of_mul_lt_mul_left hu, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨Nat.mul_lt_mul_of_pos_left hs hf, dvd_mul_right _ _⟩
  rw [this, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hf h),
    Finset.card_range]

/-- Average bound `∑_{u < d} ‖c_r(u)‖ ≤ d τ(r)` for `r ∣ d`. -/
theorem sum_norm_ramanujanSum_le {r d : ℕ} (hd : 0 < d) (hr : r ∣ d) :
    ∑ u ∈ Finset.range d, ‖ramanujanSum r u‖ ≤ d * r.divisors.card := by
  calc ∑ u ∈ Finset.range d, ‖ramanujanSum r u‖
      ≤ ∑ u ∈ Finset.range d, ∑ f ∈ r.divisors with ((f : ℕ) : ℤ) ∣ (u : ℤ), (f : ℝ) :=
        Finset.sum_le_sum fun u _ => norm_ramanujanSum_le r u
    _ = ∑ u ∈ Finset.range d, ∑ f ∈ r.divisors, if f ∣ u then (f : ℝ) else 0 := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun f _ => ?_
        simp only [Int.natCast_dvd_natCast]
    _ = ∑ f ∈ r.divisors, ∑ u ∈ Finset.range d, if f ∣ u then (f : ℝ) else 0 :=
        Finset.sum_comm
    _ = ∑ f ∈ r.divisors, (d : ℝ) := by
        refine Finset.sum_congr rfl fun f hf => ?_
        rw [Nat.mem_divisors] at hf
        have hfd : f ∣ d := hf.1.trans hr
        have hfpos : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hfd; omega)
        obtain ⟨m, rfl⟩ := hfd
        rw [← Finset.sum_filter, Finset.sum_const, card_filter_dvd_range hfpos, nsmul_eq_mul]
        push_cast
        ring
    _ = d * r.divisors.card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

end PrimeCarleson.Proof.Goal0

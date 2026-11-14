module

public import PrimeCarleson.Frozen.HeathBrownModel
public import PrimeCarleson.Proof.Goal0.Ramanujan
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.GCDMonoid.Nat

/-!
# The arithmetic weights `Γ_Q`, `c_q`, `w_Q`, `w_{Q,B}`, `𝒬_B`

The definitions of `sources/Variational_Carleson.tex` L579–L607 (Source: main paper `e:GammaQ`,
L579–L581; `e:WQ`, L583–L585; `e:ram`, L587–L589; `e:lcmQ`, L601–L603; `s:Prelim`, L605–L607).

* the Ramanujan sum (`e:ram`, L587–L589): it is the `PrimeCarleson.ramanujanSum`
  `c_q(n) = ∑_{1 ≤ a ≤ q, (a, q) = 1} e(a n / q)`; here `ramanujanSum_eq_sum_range` (the sum over
  the residues `a ∈ {0, …, q-1}` coprime to `q`, i.e. over the fractions `a/q ∈ [0, 1)`),
  `ramanujanSum_neg` (evenness) and `ramanujanSum_eq_intCast` (`c_q(n) ∈ ℤ`);
* `Γ_Q` (`e:GammaQ`, L579–L581): `Γ_Q = {a/q reduced : Q/2 < q ≤ Q}` is the `Finset ℚ` `gammaQ Q` of
  reduced fractions in `[0, 1)` (`mem_gammaQ`: `0 ≤ r < 1` and `Q/2 < r.den ≤ Q`), a special case of
  `reducedFractions B`, the reduced fractions in `[0, 1)` with denominator in `B`;
* `w_{Q,B}` (`s:Prelim`, L605–L607): `w_{Q,B}` is the `PrimeCarleson.blockWeight B`
  `= ∑_{q ∈ B} μ(q)/φ(q) c_q(n)`; `blockWeight_eq_sum_reducedFractions` is the sum over the
  fractions `a/q`, `blockWeight_neg` its evenness;
* `w_Q` (`e:WQ`, L583–L585): `wQ Q = blockWeight (Ioc (Q/2) Q)` (for `Q : ℕ`; the dyadic case is
  `wQ (2^j)`), with `wQ_eq_sum_gammaQ`: `w_Q(n) = ∑_{a/q ∈ Γ_Q} μ(q)/φ(q) e(n a/q)`, `wQ_neg`, and
  `heathBrownModel_eq_sum_wQ`: the `heathBrownModel T = ∑_{2^j ≤ T} w_{2^j}`;
* `𝒬_B` (`e:lcmQ`, L601–L603): `lcmQ B = lcm(q : q ∈ B)`.

Conventions: `Q : ℕ` (the paper's `Q > 0` is dyadic in every use; `(Q/2, Q] ∩ ℕ` is
`Finset.Ioc (Q / 2) Q` with natural-number division, which is exact: `Q/2 < q ↔ ⌊Q/2⌋ < q`);
fractions `a/q` lie in `[0, 1)`, as the index set `𝕋 = [0, 1)` of the `rVariation`.
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-! ### Reduced fractions (L579-L581) -/

/-- The reduced fractions `a/q ∈ [0, 1)` (`0 ≤ a < q`, `(a, q) = 1`) with denominator `q ∈ B`;
the fractions are rational numbers, so `a/q` is counted once. -/
def reducedFractions (B : Finset ℕ) : Finset ℚ :=
  B.biUnion fun q =>
    ((Finset.range q).filter fun a => Nat.Coprime a q).image fun a : ℕ => (a : ℚ) / q

/-- A reduced fraction `a/q` has denominator `q`. -/
theorem den_natCast_div {a q : ℕ} (hq : 0 < q) (h : Nat.Coprime a q) :
    ((a : ℚ) / q).den = q := by
  have h1 := Rat.den_div_eq_of_coprime (a := (a : ℤ)) (b := (q : ℤ)) (by exact_mod_cast hq)
    (by simpa using h)
  simpa using h1

/-- Characterization of the reduced fractions with denominator in `B`:
`r ∈ [0, 1)` with `r.den ∈ B`. -/
theorem mem_reducedFractions {B : Finset ℕ} {r : ℚ} :
    r ∈ reducedFractions B ↔ 0 ≤ r ∧ r < 1 ∧ r.den ∈ B := by
  simp only [reducedFractions, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨q, hqB, a, ⟨haq, hcop⟩, rfl⟩
    have hq : 0 < q := by omega
    refine ⟨by positivity, ?_, by rwa [den_natCast_div hq hcop]⟩
    rw [div_lt_one (by exact_mod_cast hq)]
    exact_mod_cast haq
  · rintro ⟨h0, h1, hB⟩
    refine ⟨r.den, hB, r.num.toNat, ⟨?_, ?_⟩, ?_⟩
    · have hnum : 0 ≤ r.num := Rat.num_nonneg.2 h0
      have hlt : r.num < (r.den : ℤ) := by
        have : (r.num : ℚ) < r.den := by
          rw [← div_lt_one (by exact_mod_cast r.den_pos), Rat.num_div_den]
          exact h1
        exact_mod_cast this
      omega
    · have hnum := Rat.num_nonneg.2 h0
      have h2 : r.num.toNat = r.num.natAbs := by omega
      rw [h2]
      exact r.reduced
    · have h2 : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg (Rat.num_nonneg.2 h0)
      have h3 : ((r.num.toNat : ℕ) : ℚ) = (r.num : ℚ) := by exact_mod_cast h2
      rw [h3, Rat.num_div_den]

/-- Sums over reduced fractions regroup by denominator: for `F : ℚ → M`,
`∑_{r ∈ reducedFractions B} F(r) = ∑_{q ∈ B} ∑_{a < q, (a, q) = 1} F(a/q)`. -/
theorem sum_reducedFractions {M : Type*} [AddCommMonoid M] (B : Finset ℕ) (F : ℚ → M) :
    ∑ r ∈ reducedFractions B, F r =
      ∑ q ∈ B, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), F ((a : ℚ) / q) := by
  unfold reducedFractions
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun q hq => ?_
    rw [Finset.sum_image]
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
    have hq : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    have : (a : ℚ) = b := by
      field_simp at hab
      exact hab
    exact_mod_cast this
  · intro q₁ _ q₂ _ hne
    refine Finset.disjoint_left.2 fun r h1 h2 => hne ?_
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at h1 h2
    obtain ⟨a, ⟨ha, hca⟩, rfl⟩ := h1
    obtain ⟨b, ⟨hb, hcb⟩, hb'⟩ := h2
    have e1 := den_natCast_div (by omega : 0 < q₁) hca
    have e2 := den_natCast_div (by omega : 0 < q₂) hcb
    rw [hb'] at e2
    omega

/-- `Γ_Q := {a/q reduced : Q/2 < q ≤ Q}` (Source: main paper `e:GammaQ`, L579–L581), the reduced
fractions in `[0, 1)` with denominator in `(Q/2, Q]`. -/
def gammaQ (Q : ℕ) : Finset ℚ := reducedFractions (Finset.Ioc (Q / 2) Q)

/-- `r ∈ Γ_Q` exactly when `0 ≤ r < 1` and `Q/2 < r.den ≤ Q`. -/
theorem mem_gammaQ {Q : ℕ} {r : ℚ} :
    r ∈ gammaQ Q ↔ 0 ≤ r ∧ r < 1 ∧ Q / 2 < r.den ∧ r.den ≤ Q := by
  rw [gammaQ, mem_reducedFractions, Finset.mem_Ioc]

/-- The denominator bound `Q/2 < q` in natural-number division is the real inequality
`Q/2 < q`. -/
theorem nat_div_two_lt_iff {Q q : ℕ} : Q / 2 < q ↔ (Q : ℝ) / 2 < q := by
  rw [Nat.div_lt_iff_lt_mul (by norm_num), div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
  norm_cast

/-- `Γ_Q` with the paper's real inequalities `Q/2 < q ≤ Q`. -/
theorem mem_gammaQ_real {Q : ℕ} {r : ℚ} :
    r ∈ gammaQ Q ↔ 0 ≤ r ∧ r < 1 ∧ (Q : ℝ) / 2 < r.den ∧ (r.den : ℝ) ≤ Q := by
  rw [mem_gammaQ, nat_div_two_lt_iff]
  norm_cast

/-- The cardinality of `Γ_Q` is at most `Q²` (at most `q` fractions with denominator `q ≤ Q`). -/
theorem card_gammaQ_le (Q : ℕ) : (gammaQ Q).card ≤ Q * Q := by
  have h : (gammaQ Q).card ≤ ∑ q ∈ Finset.Ioc (Q / 2) Q, q := by
    unfold gammaQ reducedFractions
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun q _ => ?_)
    refine Finset.card_image_le.trans ?_
    exact (Finset.card_filter_le _ _).trans (by simp)
  refine h.trans ?_
  calc ∑ q ∈ Finset.Ioc (Q / 2) Q, q ≤ ∑ _q ∈ Finset.Ioc (Q / 2) Q, Q :=
        Finset.sum_le_sum fun q hq => (Finset.mem_Ioc.1 hq).2
    _ = (Q - Q / 2) * Q := by simp
    _ ≤ Q * Q := Nat.mul_le_mul_right Q (Nat.sub_le Q (Q / 2))

/-! ### The Ramanujan sum (L587-L589) -/

/-- The Ramanujan sum over the residues `a ∈ {0, …, q-1}` coprime to `q`, i.e. over the
reduced fractions `a/q ∈ [0, 1)` (the paper's `e:ram` is read this way):
`c_q(n) = ∑_{a < q, (a, q) = 1} e(a n / q)`; the `ramanujanSum` sums over `1 ≤ a ≤ q`. -/
theorem ramanujanSum_eq_sum_range (q : ℕ) (n : ℤ) :
    ramanujanSum q n =
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), e ((a : ℝ) * n / q) := by
  rcases Nat.lt_or_ge q 2 with hq | hq
  · interval_cases q
    · simp [ramanujanSum]
    · simp [ramanujanSum, e_zero, e_intCast]
  · unfold ramanujanSum
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, hc⟩
      refine ⟨?_, hc⟩
      rcases h2.lt_or_eq with h | rfl
      · exact h
      · exfalso
        have h3 := hc
        unfold Nat.Coprime at h3
        rw [Nat.gcd_self] at h3
        omega
    · rintro ⟨h, hc⟩
      refine ⟨⟨?_, h.le⟩, hc⟩
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · exfalso
        have h3 := hc
        unfold Nat.Coprime at h3
        rw [Nat.gcd_zero_left] at h3
        omega
      · exact ha

/-- The Ramanujan sum is even: `c_q(-n) = c_q(n)`. -/
theorem ramanujanSum_neg (q : ℕ) (n : ℤ) : ramanujanSum q (-n) = ramanujanSum q n := by
  rw [ramanujanSum_eq_sum_divisors, ramanujanSum_eq_sum_divisors]
  congr 1
  ext f
  simp

/-- The Ramanujan sum is an integer: `c_q(n) = ∑_{f ∣ (q, n)} f μ(q/f)`. -/
theorem ramanujanSum_eq_intCast (q : ℕ) (n : ℤ) :
    ramanujanSum q n = ((∑ f ∈ q.divisors with ((f : ℕ) : ℤ) ∣ n,
      (f : ℤ) * ArithmeticFunction.moebius (q / f) : ℤ) : ℂ) := by
  rw [ramanujanSum_eq_sum_divisors]
  push_cast
  rfl

/-! ### The block weights `w_{Q,B}` and `𝒬_B` (L601-L607) -/

/-- `𝒬_B := lcm(q : q ∈ B)` (Source: main paper `e:lcmQ`, L601–L603), `lcm ∅ = 1`. -/
def lcmQ (B : Finset ℕ) : ℕ := B.lcm id

/-- Every `q ∈ B` divides `𝒬_B`. -/
theorem dvd_lcmQ {B : Finset ℕ} {q : ℕ} (hq : q ∈ B) : q ∣ lcmQ B :=
  Finset.dvd_lcm hq

/-- `𝒬_B > 0` when `B` consists of positive integers. -/
theorem lcmQ_pos {B : Finset ℕ} (h : ∀ q ∈ B, 0 < q) : 0 < lcmQ B := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  obtain ⟨q, hq, hq0⟩ := Finset.lcm_eq_zero_iff.1 h0
  exact (h q hq).ne' hq0

/-- `w_{Q,B}` is even: `w_{Q,B}(-n) = w_{Q,B}(n)`. -/
theorem blockWeight_neg (B : Finset ℕ) (n : ℤ) : blockWeight B (-n) = blockWeight B n := by
  simp [blockWeight, ramanujanSum_neg]

/-- `w_{Q,B}` as a sum over the reduced fractions `a/q`, `q ∈ B`:
`w_{Q,B}(n) = ∑_{a/q} μ(q)/φ(q) e(n a/q)` (the first form of `e:WQ`, L583-L585, for general
`B`). -/
theorem blockWeight_eq_sum_reducedFractions (B : Finset ℕ) (n : ℤ) :
    blockWeight B n = ∑ r ∈ reducedFractions B,
      (((ArithmeticFunction.moebius r.den : ℤ) : ℝ) / (Nat.totient r.den : ℝ) : ℂ) *
        e ((n : ℝ) * (r : ℝ)) := by
  rw [sum_reducedFractions]
  unfold blockWeight
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [ramanujanSum_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at ha
  rw [den_natCast_div (by omega) ha.2]
  congr 2
  push_cast
  ring_nf

/-! ### The weight `w_Q` (L583-L585) -/

/-- `w_Q(n) := ∑_{Q/2 < q ≤ Q} μ(q)/φ(q) c_q(n)` (Source: main paper `e:WQ`, L583–L585), for
`Q : ℕ` (dyadic in every use, `Q = 2^j`): the block weight of the block `(Q/2, Q] ∩ ℕ`. -/
def wQ (Q : ℕ) (n : ℤ) : ℂ := blockWeight (Finset.Ioc (Q / 2) Q) n

/-- The second form of `e:WQ`: `w_Q(n) = ∑_{Q/2 < q ≤ Q} μ(q)/φ(q) c_q(n)`. -/
theorem wQ_eq_sum_ramanujanSum (Q : ℕ) (n : ℤ) :
    wQ Q n = ∑ q ∈ Finset.Ioc (Q / 2) Q,
      (((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ) : ℂ) *
        ramanujanSum q n := rfl

/-- The first form of `e:WQ`: `w_Q(n) = ∑_{a/q ∈ Γ_Q} μ(q)/φ(q) e(n a/q)`, `q` the denominator
of the reduced fraction `r = a/q`. -/
theorem wQ_eq_sum_gammaQ (Q : ℕ) (n : ℤ) :
    wQ Q n = ∑ r ∈ gammaQ Q,
      (((ArithmeticFunction.moebius r.den : ℤ) : ℝ) / (Nat.totient r.den : ℝ) : ℂ) *
        e ((n : ℝ) * (r : ℝ)) :=
  blockWeight_eq_sum_reducedFractions _ n

/-- `w_Q` is even: `w_Q(-n) = w_Q(n)`. -/
theorem wQ_neg (Q : ℕ) (n : ℤ) : wQ Q (-n) = wQ Q n := blockWeight_neg _ n

/-- The Heath-Brown model is `∑_{Q ≤ T dyadic} w_Q`, the sum over `Q = 2^j`, `2^j ≤ T`
(here over the finite range `j ≤ ⌊T⌋₊` of the definition). -/
theorem heathBrownModel_eq_sum_wQ (T : ℝ) (n : ℤ) :
    heathBrownModel T n =
      ∑ j ∈ (Finset.range (⌊T⌋₊ + 1)).filter (fun j => (2 : ℝ) ^ j ≤ T), wQ (2 ^ j) n := rfl

/-- The Heath-Brown model `Λ_{≤T} = ∑_{j : 2^j ≤ T} w_{2^j}`, for any finite set `S` of
exponents with `j ∈ S ↔ 2^j ≤ T`. -/
theorem heathBrownModel_eq_sum_of_mem_iff (T : ℝ) (S : Finset ℕ)
    (hS : ∀ j : ℕ, j ∈ S ↔ (2 : ℝ) ^ j ≤ T) (n : ℤ) :
    heathBrownModel T n = ∑ j ∈ S, wQ (2 ^ j) n := by
  rw [heathBrownModel_eq_sum_wQ]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, hS]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have h1 : (j : ℝ) < (2 : ℝ) ^ j := by exact_mod_cast Nat.lt_two_pow_self
  have : j ≤ ⌊T⌋₊ := Nat.le_floor (by linarith)
  omega

/-- The Heath-Brown model is even: `Λ_{≤T}(-n) = Λ_{≤T}(n)`. -/
theorem heathBrownModel_neg (T : ℝ) (n : ℤ) : heathBrownModel T (-n) = heathBrownModel T n := by
  simp [heathBrownModel, blockWeight_neg]

end PrimeCarleson.Proof.Paper

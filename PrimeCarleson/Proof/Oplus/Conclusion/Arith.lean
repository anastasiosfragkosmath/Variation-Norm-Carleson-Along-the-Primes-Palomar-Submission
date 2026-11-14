module

public import PrimeCarleson.Proof.Oplus.Conclusion.TreeBlock
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# The real-number bookkeeping of the conclusion ([O+] L2611-L2650, L2677-L2685)

The real-number bookkeeping of [O+] `L1except` (L2580–L2685): the choice of the parameters and the
inequalities of Chebyshev's bound in the large-`F` case, the arithmetic check of the source's
display "`2^{(j+k)((1+ε)(2/r)-1)/2} 2^{-ℓ(N-14)} |F|^{1/2 - 1/(q'r)}`", and the sum in the
small-`F` case.

* the rates `ν = 2^{-1/2}` (energy halving, `ν² = 1/2`) and `μ = 2^{-1/r'}` (density halving,
  `μ^{r'} = 1/2`) of the decomposition, both in `[1/2, 1)`;
* `exists_large_params`: the choice of `ε` small and `q` large with `(1 + ε) 2/r < 1` and
  `1/2 - 1/(q' r) ≤ 1/p`, possible exactly because `1/p > 1/2 - 1/r` (that is `p < 2r/(r-2)`);
* `stage_real_bound`: the term of `S_1 + S_2` for the indices `(j, k, ℓ)` is at most
  `Γ |F|^{1/p} γ^{j+k} 2^{-ℓ}` with `γ = 2^{(1+ε)/r} ν < 1`;
* `measure_real_bound`: the bound `|G_{j,k,ℓ}| ≤ C^q 2^ℓ σ b^{q-1}/B^q` is at most
  `(C c/C')^q (2^{-ε})^{j+k+2ℓ}`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section Arith


/-- The rate `ν = 2^{-1/2}` at which the energy bound is lowered from stage to stage
(`ν² = 1/2`). -/
noncomputable def nuE : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ))

/-- `ν > 0`. -/
theorem nuE_pos : 0 < nuE := Real.rpow_pos_of_pos (by norm_num) _

/-- `ν < 1`. -/
theorem nuE_lt_one : nuE < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- `ν² = 1/2`. -/
theorem nuE_sq : nuE ^ 2 = 1 / 2 := by
  unfold nuE
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `ν ≥ 1/2`, so that halving the energy lowers it at least at the rate `ν`. -/
theorem one_half_le_nuE : 1 / 2 ≤ nuE := by
  have h := nuE_sq
  have h0 := nuE_pos
  nlinarith [nuE_lt_one]

/-- The rate `μ = 2^{-1/r'}` at which the density bound is lowered (`μ^{r'} = 1/2`). -/
noncomputable def muD (r : ℝ) : ℝ := (2 : ℝ) ^ (-(1 / Real.conjExponent r))

/-- `μ > 0`. -/
theorem muD_pos (r : ℝ) : 0 < muD r := Real.rpow_pos_of_pos (by norm_num) _

/-- `μ < 1`. -/
theorem muD_lt_one {r : ℝ} (hr : 1 < r) : muD r < 1 := by
  have h := (Real.HolderConjugate.conjExponent hr).symm.pos
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by rw [neg_neg_iff_pos]; positivity)

/-- `μ 2^{1/r'} = 1`: the factors `μ^j` and `(2^j)^{1/r'}` cancel. -/
theorem muD_mul_two_rpow (r : ℝ) : muD r * (2 : ℝ) ^ (1 / Real.conjExponent r) = 1 := by
  unfold muD
  rw [← Real.rpow_add (by norm_num)]
  simp

/-- `μ^{r'} = 1/2`. -/
theorem muD_rpow {r : ℝ} (hr : 1 < r) : muD r ^ Real.conjExponent r = 1 / 2 := by
  have h := (Real.HolderConjugate.conjExponent hr).symm.pos
  unfold muD
  rw [← Real.rpow_mul (by norm_num)]
  have : -(1 / Real.conjExponent r) * Real.conjExponent r = -1 := by field_simp
  rw [this, Real.rpow_neg_one]; norm_num

/-- `μ ≥ 1/2`, so that halving the density lowers it at least at the rate `μ`. -/
theorem one_half_le_muD {r : ℝ} (hr : 1 < r) : 1 / 2 ≤ muD r := by
  have h1 := (Real.HolderConjugate.conjExponent hr)
  have h2 : 1 < Real.conjExponent r := h1.symm.lt
  have h3 : muD r = (1 / 2 : ℝ) ^ (1 / Real.conjExponent r) := by
    unfold muD
    rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by rw [Real.rpow_neg_one]; norm_num,
      ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  rw [h3]
  calc (1 / 2 : ℝ) = (1 / 2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (1 / 2 : ℝ) ^ (1 / Real.conjExponent r) := by
        apply Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
        rw [div_le_one (by linarith)]; linarith

/-- **The choice of `ε` and `q`** (L2647-L2650): `ε > 0` and `q ∈ ℕ` with `(1 + ε) 2/r < 1` and
`1/2 - 1/(q' r) ≤ 1/p`, where `1/q' = 1 - 1/q`; possible because `1/p > 1/2 - 1/r`. -/
theorem exists_large_params {r p : ℝ} (hr : 2 < r) (hp : 1 / 2 - 1 / r < 1 / p) :
    ∃ (q : ℕ) (ε : ℝ), 1 ≤ q ∧ 0 < ε ∧ (1 + ε) * 2 < r ∧
      1 / 2 - (1 - 1 / (q : ℝ)) / r ≤ 1 / p := by
  set δ : ℝ := 1 / p - (1 / 2 - 1 / r) with hδ
  have hδ0 : 0 < δ := by linarith
  have hr0 : 0 < r := by linarith
  refine ⟨⌈1 / (r * δ)⌉₊ + 1, (r - 2) / 4, by omega, by linarith, by linarith, ?_⟩
  have hq : 1 / (r * δ) ≤ ((⌈1 / (r * δ)⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.le_ceil (1 / (r * δ))]
  have hqpos : (0 : ℝ) < ((⌈1 / (r * δ)⌉₊ + 1 : ℕ) : ℝ) := by positivity
  have h1 : 1 / ((⌈1 / (r * δ)⌉₊ + 1 : ℕ) : ℝ) ≤ r * δ := by
    rw [div_le_iff₀ hqpos]
    rw [div_le_iff₀ (by positivity)] at hq
    nlinarith
  have h2 : (1 / ((⌈1 / (r * δ)⌉₊ + 1 : ℕ) : ℝ)) / r ≤ δ := by
    rw [div_le_iff₀ hr0]; nlinarith
  have : 1 / 2 - (1 - 1 / ((⌈1 / (r * δ)⌉₊ + 1 : ℕ) : ℝ)) / r =
      1 / 2 - 1 / r + (1 / ((⌈1 / (r * δ)⌉₊ + 1 : ℕ) : ℝ)) / r := by ring
  rw [this]; linarith


/-- **The arithmetic of `S_1 + S_2`** (L2641-L2650): the term for `(j, k, ℓ)`, built from the
bound `B = C' (2 · 2^ε)^{j+k+2ℓ} / |F|^{1 - 1/q}` of the covering function, the tree estimate with
energy `A |F|^{1/2} ν^{j+k}`, density `A μ^j` and `∑ |I_T| ≤ c 2^j`, is at most
`Γ |F|^{1/p} γ^{j+k} 2^{-ℓ}` with `γ = (2 · 2^ε)^{1/r} ν`. -/
theorem stage_real_bound {r p : ℝ} {q : ℕ} (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε)
    (hεr : (1 + ε) * 2 < r) (hqp : 1 / 2 - (1 - 1 / (q : ℝ)) / r ≤ 1 / p)
    {A c C' K Fm tw : ℝ} (hA : 0 < A) (hc : 0 < c) (hC' : 0 < C') (hK : 0 ≤ K) (hFm : 1 < Fm)
    (j k ℓ : ℕ) (htw : tw ≤ 4 * (1 / 4 : ℝ) ^ ℓ) :
    (C' * (2 * (2 : ℝ) ^ ε) ^ (j + k + 2 * ℓ) / Fm ^ (1 - 1 / (q : ℝ))) ^ (1 / r) *
      (2 : ℝ) ^ (1 / r) *
      (K * tw * (A * Fm ^ (1 / 2 : ℝ) * nuE ^ (j + k)) * (A * muD r ^ j) *
        (c * 2 ^ j) ^ (1 / Real.conjExponent r)) ≤
    (4 * C' ^ (1 / r) * (2 : ℝ) ^ (1 / r) * K * A ^ 2 * c ^ (1 / Real.conjExponent r)) *
      Fm ^ (1 / p) * ((2 * (2 : ℝ) ^ ε) ^ (1 / r) * nuE) ^ (j + k) * (1 / 2 : ℝ) ^ ℓ := by
  have hr1 : 1 < r := by linarith
  have hr0 : 0 < r := by linarith
  have hFm0 : 0 < Fm := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set r' := Real.conjExponent r with hr'
  have hr'0 : 0 < r' := (Real.HolderConjugate.conjExponent hr1).symm.pos
  set β : ℝ := (2 * (2 : ℝ) ^ ε) ^ (1 / r) with hβ
  have h2ε : 0 < 2 * (2 : ℝ) ^ ε := by positivity
  have hβ0 : 0 < β := Real.rpow_pos_of_pos h2ε _
  set τ : ℝ := (2 : ℝ) ^ (1 / r') with hτ
  set η : ℝ := (1 - 1 / (q : ℝ)) / r with hη
  have hν0 := nuE_pos
  have hμ0 := muD_pos r
  have hpow : ∀ (x : ℝ), 0 ≤ x → ∀ (n : ℕ) (y : ℝ), (x ^ n) ^ y = (x ^ y) ^ n := fun x hx n y => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx, mul_comm, Real.rpow_mul hx, Real.rpow_natCast]
  have e1 : (C' * (2 * (2 : ℝ) ^ ε) ^ (j + k + 2 * ℓ) / Fm ^ (1 - 1 / (q : ℝ))) ^ (1 / r) =
      C' ^ (1 / r) * β ^ (j + k + 2 * ℓ) * (Fm ^ η)⁻¹ := by
    have hFq : 0 ≤ Fm ^ (1 - 1 / (q : ℝ)) := by positivity
    rw [Real.div_rpow (by positivity) hFq, Real.mul_rpow hC'.le (by positivity),
      hpow _ h2ε.le, ← Real.rpow_mul hFm0.le, div_eq_mul_inv, hη, mul_one_div]
  have e2 : (c * 2 ^ j) ^ (1 / r') = c ^ (1 / r') * τ ^ j := by
    rw [Real.mul_rpow hc.le (by positivity), hpow 2 (by norm_num)]
  have e3 : muD r ^ j * τ ^ j = 1 := by
    rw [← mul_pow, hτ, muD_mul_two_rpow, one_pow]
  have hβ2 : β ^ 2 ≤ 2 := by
    rw [hβ, ← Real.rpow_natCast, ← Real.rpow_mul h2ε.le]
    have : 2 * (2 : ℝ) ^ ε = (2 : ℝ) ^ (1 + ε) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one]
    rw [this, ← Real.rpow_mul (by norm_num)]
    calc (2 : ℝ) ^ ((1 + ε) * (1 / r * ((2 : ℕ) : ℝ))) ≤ (2 : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          push_cast
          rw [show (1 + ε) * (1 / r * 2) = (1 + ε) * 2 / r by ring, div_le_one hr0]
          linarith
      _ = 2 := Real.rpow_one 2
  have hβℓ : tw * β ^ (2 * ℓ) ≤ 4 * (1 / 2 : ℝ) ^ ℓ := by
    calc tw * β ^ (2 * ℓ) ≤ 4 * (1 / 4 : ℝ) ^ ℓ * 2 ^ ℓ := by
          rw [pow_mul]
          exact mul_le_mul htw (pow_le_pow_left₀ (by positivity) hβ2 ℓ) (by positivity)
            (by positivity)
      _ = 4 * (1 / 2 : ℝ) ^ ℓ := by
          rw [mul_assoc, ← mul_pow]; norm_num
  have hFm' : Fm ^ (1 / 2 : ℝ) * (Fm ^ η)⁻¹ ≤ Fm ^ (1 / p) := by
    rw [← Real.rpow_neg hFm0.le, ← Real.rpow_add hFm0]
    exact Real.rpow_le_rpow_of_exponent_le hFm.le (by rw [hη] at *; linarith)
  have key : (C' * (2 * (2 : ℝ) ^ ε) ^ (j + k + 2 * ℓ) / Fm ^ (1 - 1 / (q : ℝ))) ^ (1 / r) *
      (2 : ℝ) ^ (1 / r) *
      (K * tw * (A * Fm ^ (1 / 2 : ℝ) * nuE ^ (j + k)) * (A * muD r ^ j) *
        (c * 2 ^ j) ^ (1 / r')) =
      (C' ^ (1 / r) * (2 : ℝ) ^ (1 / r) * K * A ^ 2 * c ^ (1 / r')) * (tw * β ^ (2 * ℓ)) *
        (β * nuE) ^ (j + k) * (Fm ^ (1 / 2 : ℝ) * (Fm ^ η)⁻¹) * (muD r ^ j * τ ^ j) := by
    rw [e1, e2]
    ring
  rw [key, e3, mul_one]
  have hG : 0 ≤ C' ^ (1 / r) * (2 : ℝ) ^ (1 / r) * K * A ^ 2 * c ^ (1 / r') := by positivity
  have hγ : 0 ≤ (β * nuE) ^ (j + k) := by positivity
  calc _ ≤ (C' ^ (1 / r) * (2 : ℝ) ^ (1 / r) * K * A ^ 2 * c ^ (1 / r')) *
        (4 * (1 / 2 : ℝ) ^ ℓ) * (β * nuE) ^ (j + k) * Fm ^ (1 / p) := by
        gcongr
    _ = _ := by ring

/-- **The arithmetic of the Chebyshev bound** (L2611-L2616): `C^q 2^ℓ σ b^{q-1} / B^q` is at most
`(C c/C')^q (2^{-ε})^{j+k+2ℓ}` for `σ = c 2^j`, `b = c 2^{2ℓ} 2^{j+k}/|F|` and
`B = C' (2 · 2^ε)^{j+k+2ℓ} / |F|^{1 - 1/q}`. -/
theorem measure_real_bound {q : ℕ} (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε) {Cq c C' Fm : ℝ}
    (hCq : 0 ≤ Cq) (hc : 0 < c) (hC' : 0 < C') (hFm : 0 < Fm) (j k ℓ : ℕ) :
    Cq ^ q * (2 ^ ℓ * (c * 2 ^ j)) * (c * 2 ^ (2 * ℓ) * 2 ^ (j + k) / Fm) ^ (q - 1) /
        (C' * (2 * (2 : ℝ) ^ ε) ^ (j + k + 2 * ℓ) / Fm ^ (1 - 1 / (q : ℝ))) ^ q ≤
      (Cq * c / C') ^ q * ((2 : ℝ) ^ (-ε)) ^ (j + k + 2 * ℓ) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set w : ℕ := j + k + 2 * ℓ with hw
  set ρ : ℝ := (2 : ℝ) ^ ε with hρ
  have hρ1 : 1 ≤ ρ := Real.one_le_rpow (by norm_num) hε.le
  have hρ0 : 0 < ρ := by linarith
  have hFq : (Fm ^ (1 - 1 / ((m + 1 : ℕ) : ℝ))) ^ (m + 1) = Fm ^ m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hFm.le]
    have : (1 - 1 / ((m + 1 : ℕ) : ℝ)) * ((m + 1 : ℕ) : ℝ) = (m : ℝ) := by
      push_cast; field_simp; ring
    rw [this, Real.rpow_natCast]
  have hFpos : 0 < Fm ^ m := by positivity
  have hD : (C' * (2 * ρ) ^ w / Fm ^ (1 - 1 / ((m + 1 : ℕ) : ℝ))) ^ (m + 1) =
      C' ^ (m + 1) * ((2 ^ w) ^ (m + 1) * (ρ ^ w) ^ (m + 1)) / Fm ^ m := by
    rw [div_pow, mul_pow, hFq, mul_pow, mul_pow]
  have hρinv : ((2 : ℝ) ^ (-ε)) = ρ⁻¹ := Real.rpow_neg (by norm_num) ε
  rw [hD, hρinv, inv_pow]
  have hexp : (2 : ℝ) ^ (2 * ℓ) * 2 ^ (j + k) = 2 ^ w := by
    rw [← pow_add, hw]; congr 1; ring
  have hwle : (2 : ℝ) ^ (ℓ + j) ≤ 2 ^ w := pow_le_pow_right₀ (by norm_num) (by omega)
  have hpos2 : (0 : ℝ) < 2 ^ w := by positivity
  have hρw : 1 ≤ ρ ^ w := one_le_pow₀ hρ1
  have hρw' : 0 < ρ ^ w := by positivity
  have hnum : Cq ^ (m + 1) * (2 ^ ℓ * (c * 2 ^ j)) * (c * 2 ^ (2 * ℓ) * 2 ^ (j + k) / Fm) ^ m =
      (Cq * c) ^ (m + 1) * 2 ^ (ℓ + j) * (2 ^ w) ^ m / Fm ^ m := by
    rw [mul_assoc (c) (2 ^ (2 * ℓ)), hexp, div_pow, mul_pow, pow_succ (Cq * c) m, mul_pow,
      pow_add]
    ring
  rw [hnum]
  have key : (Cq * c) ^ (m + 1) * 2 ^ (ℓ + j) * (2 ^ w) ^ m / Fm ^ m /
      (C' ^ (m + 1) * ((2 ^ w) ^ (m + 1) * (ρ ^ w) ^ (m + 1)) / Fm ^ m) =
      (Cq * c / C') ^ (m + 1) * (2 ^ (ℓ + j) / (2 ^ w * (ρ ^ w) ^ (m + 1))) := by
    rw [div_pow]
    field_simp
    ring
  rw [key]
  have h1 : (2 : ℝ) ^ (ℓ + j) / (2 ^ w * (ρ ^ w) ^ (m + 1)) ≤ (ρ ^ w)⁻¹ := by
    have h2 : (ρ ^ w) ^ (m + 1) ≥ ρ ^ w := by
      calc ρ ^ w = (ρ ^ w) ^ 1 := (pow_one _).symm
        _ ≤ (ρ ^ w) ^ (m + 1) := pow_le_pow_right₀ hρw (by omega)
    rw [div_le_iff₀ (by positivity)]
    calc (2 : ℝ) ^ (ℓ + j) ≤ 2 ^ w := hwle
      _ = (ρ ^ w)⁻¹ * (2 ^ w * ρ ^ w) := by field_simp
      _ ≤ (ρ ^ w)⁻¹ * (2 ^ w * (ρ ^ w) ^ (m + 1)) := by gcongr
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- **The decay rate** `γ = (2 · 2^ε)^{1/r} ν = 2^{(1+ε)/r - 1/2}` is less than `1` when
`(1 + ε) 2 < r` (the source's "`(1 + ε)(2/r) - 1 < 0`", L2647). -/
theorem gamma_lt_one {r ε : ℝ} (hr : 2 < r) (hεr : (1 + ε) * 2 < r) :
    (2 * (2 : ℝ) ^ ε) ^ (1 / r) * nuE < 1 := by
  have hr0 : 0 < r := by linarith
  have h2 : 2 * (2 : ℝ) ^ ε = (2 : ℝ) ^ (1 + ε) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
  unfold nuE
  rw [h2, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
  refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
  have : (1 + ε) * (1 / r) + -(1 / 2) = ((1 + ε) * 2 - r) / (2 * r) := by field_simp; ring
  rw [this]
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

/-- `γ > 0`. -/
theorem gamma_pos {r ε : ℝ} : 0 < (2 * (2 : ℝ) ^ ε) ^ (1 / r) * nuE :=
  mul_pos (Real.rpow_pos_of_pos (by positivity) _) nuE_pos

/-- `(x^n)^y = (x^y)^n` for `x ≥ 0`. -/
theorem pow_rpow_eq {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (y : ℝ) : (x ^ n) ^ y = (x ^ y) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, mul_comm, Real.rpow_mul hx, Real.rpow_natCast]

/-- **The cost of stage `j`** (L2582-L2587): the energy increment at the level `e₀ ν^j` with
`e₀ = A |F|^{1/2}` costs `K (e₀ ν^j)^{-2} |F| = K 2^j / A²`, the density increment at the level
`A μ^j` costs `K (A μ^j)^{-r'} |E| ≤ 2 K 2^j / A^{r'}`. -/
theorem stage_cost_le {r : ℝ} (hr : 1 < r) {K A Fm : ℝ} (hK : 0 ≤ K) (hA : 0 < A) (hFm : 0 < Fm)
    {E : ENNReal} (hE : E ≤ 2) (j : ℕ) :
    ENNReal.ofReal (K / (A * Fm ^ (1 / 2 : ℝ) * nuE ^ j) ^ 2) * ENNReal.ofReal Fm +
      ENNReal.ofReal (K / (A * muD r ^ j) ^ Real.conjExponent r) * E ≤
    ENNReal.ofReal ((K / A ^ 2 + 2 * K / A ^ Real.conjExponent r) * 2 ^ j) := by
  have hν := nuE_pos
  have hμ := muD_pos r
  have h1 : K / (A * Fm ^ (1 / 2 : ℝ) * nuE ^ j) ^ 2 * Fm = K / A ^ 2 * 2 ^ j := by
    have hF2 : (Fm ^ (1 / 2 : ℝ)) ^ 2 = Fm := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hFm.le]; norm_num
    have e1 : (A * Fm ^ (1 / 2 : ℝ) * nuE ^ j) ^ 2 = A ^ 2 * Fm * ((2 : ℝ) ^ j)⁻¹ := by
      rw [mul_pow, mul_pow, hF2, ← pow_mul, mul_comm j 2, pow_mul, nuE_sq, one_div, inv_pow]
    rw [e1]
    field_simp
  have h2 : K / (A * muD r ^ j) ^ Real.conjExponent r ≤ K / A ^ Real.conjExponent r * 2 ^ j := by
    have hA' : 0 < A ^ Real.conjExponent r := Real.rpow_pos_of_pos hA _
    rw [Real.mul_rpow hA.le (pow_nonneg hμ.le j), pow_rpow_eq hμ.le, muD_rpow hr]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hA']
    have : ((1 / 2 : ℝ) ^ j) * 2 ^ j = 1 := by rw [← mul_pow]; norm_num
    nlinarith [this, mul_nonneg hK hA'.le]
  calc ENNReal.ofReal (K / (A * Fm ^ (1 / 2 : ℝ) * nuE ^ j) ^ 2) * ENNReal.ofReal Fm +
        ENNReal.ofReal (K / (A * muD r ^ j) ^ Real.conjExponent r) * E
      ≤ ENNReal.ofReal (K / A ^ 2 * 2 ^ j) +
        ENNReal.ofReal (K / A ^ Real.conjExponent r * 2 ^ j) * ENNReal.ofReal 2 := by
        refine add_le_add (le_of_eq ?_)
          (mul_le_mul' (ENNReal.ofReal_le_ofReal h2) (by simpa using hE))
        rw [← ENNReal.ofReal_mul (by positivity), h1]
    _ = ENNReal.ofReal (K / A ^ 2 * 2 ^ j + K / A ^ Real.conjExponent r * 2 ^ j * 2) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
    _ = _ := by
        congr 1; ring

/-- **The sum over the stages for `|F| ≤ 1`** (L2681-L2685): with `ϑ = 2^{1/r}` (the product of
the density rate `μ^j` and the length bound `2^j`) and `ν = 2^{-1/2}`,
`∑_{j < J} ϑ^j min(|F|^{1/2} ν^j, |F|) ≤ C_r |F|^{1 - 1/r}` for `0 < |F| ≤ 1` and `r > 2`: the
terms with `2^j |F| ≤ 1` are at most `ϑ^j |F|` and the others at most `(ϑ ν)^j |F|^{1/2}`, two
geometric series with `ϑ ν = 2^{1/r - 1/2} < 1`. -/
theorem small_sum_le {r : ℝ} (hr : 2 < r) :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ {Fm : ℝ}, 0 < Fm → Fm ≤ 1 → ∀ J : ℕ,
      ∑ j ∈ Finset.range J, ((2 : ℝ) ^ (1 / r)) ^ j * min (Fm ^ (1 / 2 : ℝ) * nuE ^ j) Fm ≤
        Cs * Fm ^ (1 - 1 / r) := by
  have hr0 : 0 < r := by linarith
  set ϑ : ℝ := (2 : ℝ) ^ (1 / r) with hϑ
  have hϑ1 : 1 < ϑ := Real.one_lt_rpow (by norm_num) (by positivity)
  set κ : ℝ := ϑ * nuE with hκ
  have hκeq : κ = (2 : ℝ) ^ (1 / r - 1 / 2) := by
    rw [hκ, hϑ, nuE, ← Real.rpow_add (by norm_num), ← sub_eq_add_neg]
  have hκ0 : 0 < κ := mul_pos (by linarith) nuE_pos
  have hκ1 : κ < 1 := by
    rw [hκeq]
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
    have : 1 / r < 1 / 2 := by rw [div_lt_div_iff₀ hr0 (by norm_num)]; linarith
    linarith
  refine ⟨ϑ / (ϑ - 1) + 1 / (1 - κ), by
    have : 0 < ϑ - 1 := by linarith
    have : 0 < 1 - κ := by linarith
    positivity, ?_⟩
  intro Fm hFm0 hFm1 J
  obtain ⟨j₀, h1, h2⟩ := exists_nat_pow_near (x := 1 / Fm) (y := (2 : ℝ))
    (by rw [le_div_iff₀ hFm0]; linarith) (by norm_num)
  have hν := nuE_pos
  -- pointwise bound
  have hpt : ∀ j : ℕ, ϑ ^ j * min (Fm ^ (1 / 2 : ℝ) * nuE ^ j) Fm ≤
      (if j ≤ j₀ then ϑ ^ j * Fm else 0) + (if j₀ < j then κ ^ j * Fm ^ (1 / 2 : ℝ) else 0) := by
    intro j
    have hϑj : 0 ≤ ϑ ^ j := by positivity
    by_cases hj : j ≤ j₀
    · have hj' : ¬ j₀ < j := by omega
      simp only [hj, hj', ↓reduceIte, add_zero]
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) hϑj
    · have hj' : j₀ < j := by omega
      simp only [hj, hj', ↓reduceIte, zero_add]
      calc ϑ ^ j * min (Fm ^ (1 / 2 : ℝ) * nuE ^ j) Fm ≤ ϑ ^ j * (Fm ^ (1 / 2 : ℝ) * nuE ^ j) :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hϑj
        _ = κ ^ j * Fm ^ (1 / 2 : ℝ) := by rw [hκ, mul_pow]; ring
  have hsum1 : ∑ j ∈ Finset.range J, (if j ≤ j₀ then ϑ ^ j * Fm else 0) ≤
      ϑ / (ϑ - 1) * Fm ^ (1 - 1 / r) := by
    have hsub : ∑ j ∈ Finset.range J, (if j ≤ j₀ then ϑ ^ j * Fm else 0) ≤
        ∑ j ∈ Finset.range (j₀ + 1), ϑ ^ j * Fm := by
      rw [← Finset.sum_filter]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      omega
    refine hsub.trans ?_
    rw [← Finset.sum_mul, geom_sum_eq hϑ1.ne']
    have h3 : ϑ ^ (j₀ + 1) = ϑ * ϑ ^ j₀ := by ring
    have h4 : ϑ ^ j₀ ≤ Fm ^ (-(1 / r)) := by
      rw [hϑ, ← pow_rpow_eq (by norm_num)]
      have : ((2 : ℝ) ^ j₀) ^ (1 / r) ≤ (1 / Fm) ^ (1 / r) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
      rw [one_div Fm, Real.inv_rpow hFm0.le, ← Real.rpow_neg hFm0.le] at this
      simpa using this
    have h5 : Fm ^ (1 - 1 / r) = Fm * Fm ^ (-(1 / r)) := by
      rw [sub_eq_add_neg, Real.rpow_add hFm0, Real.rpow_one]
    have hϑ' : 0 < ϑ - 1 := by linarith
    rw [h5, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hϑ']
    calc (ϑ ^ (j₀ + 1) - 1) * Fm ≤ ϑ ^ (j₀ + 1) * Fm := by nlinarith
      _ = ϑ * ϑ ^ j₀ * Fm := by rw [h3]
      _ ≤ ϑ * (Fm ^ (-(1 / r))) * Fm := by gcongr
      _ = ϑ * (Fm * Fm ^ (-(1 / r))) := by ring
  have hsum2 : ∑ j ∈ Finset.range J, (if j₀ < j then κ ^ j * Fm ^ (1 / 2 : ℝ) else 0) ≤
      1 / (1 - κ) * Fm ^ (1 - 1 / r) := by
    have hsub : ∑ j ∈ Finset.range J, (if j₀ < j then κ ^ j * Fm ^ (1 / 2 : ℝ) else 0) ≤
        ∑ j ∈ Finset.Ico (j₀ + 1) J, κ ^ j * Fm ^ (1 / 2 : ℝ) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hj ⊢
      omega
    refine hsub.trans ?_
    rw [← Finset.sum_mul]
    have hg := geom_sum_Ico_le_of_lt_one (m := j₀ + 1) (n := J) hκ0.le hκ1
    have hz : 1 / r - 1 / 2 ≤ 0 := by
      have : 1 / r < 1 / 2 := by rw [div_lt_div_iff₀ hr0 (by norm_num)]; linarith
      linarith
    have h6 : κ ^ (j₀ + 1) ≤ Fm ^ (1 / 2 - 1 / r) := by
      rw [hκeq, ← pow_rpow_eq (by norm_num)]
      have h7 : ((2 : ℝ) ^ (j₀ + 1)) ^ (1 / r - 1 / 2) ≤ (1 / Fm) ^ (1 / r - 1 / 2) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h2.le hz
      rw [one_div Fm, Real.inv_rpow hFm0.le, ← Real.rpow_neg hFm0.le] at h7
      have : -(1 / r - 1 / 2) = 1 / 2 - 1 / r := by ring
      rw [this] at h7
      exact h7
    have h8 : Fm ^ (1 - 1 / r) = Fm ^ (1 / 2 - 1 / r) * Fm ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hFm0]; congr 1; ring
    have h1κ : 0 < 1 - κ := by linarith
    calc (∑ i ∈ Finset.Ico (j₀ + 1) J, κ ^ i) * Fm ^ (1 / 2 : ℝ)
        ≤ (κ ^ (j₀ + 1) / (1 - κ)) * Fm ^ (1 / 2 : ℝ) := by gcongr
      _ ≤ (Fm ^ (1 / 2 - 1 / r) / (1 - κ)) * Fm ^ (1 / 2 : ℝ) := by gcongr
      _ = 1 / (1 - κ) * Fm ^ (1 - 1 / r) := by rw [h8]; ring
  calc ∑ j ∈ Finset.range J, ϑ ^ j * min (Fm ^ (1 / 2 : ℝ) * nuE ^ j) Fm
      ≤ ∑ j ∈ Finset.range J, ((if j ≤ j₀ then ϑ ^ j * Fm else 0) +
          (if j₀ < j then κ ^ j * Fm ^ (1 / 2 : ℝ) else 0)) := Finset.sum_le_sum fun j _ => hpt j
    _ = _ := Finset.sum_add_distrib
    _ ≤ ϑ / (ϑ - 1) * Fm ^ (1 - 1 / r) + 1 / (1 - κ) * Fm ^ (1 - 1 / r) := add_le_add hsum1 hsum2
    _ = (ϑ / (ϑ - 1) + 1 / (1 - κ)) * Fm ^ (1 - 1 / r) := by ring

/-- `2 μ = 2^{1/r}`: the product of the density rate `μ^j` and the length bound `2^j` is
`(2^{1/r})^j`. -/
theorem muD_mul_two {r : ℝ} (hr : 1 < r) : muD r * 2 = (2 : ℝ) ^ (1 / r) := by
  have h := (Real.HolderConjugate.conjExponent hr).inv_add_inv_eq_one
  have h2 : (2 : ℝ) ^ (-(1 / Real.conjExponent r) + 1) =
      (2 : ℝ) ^ (-(1 / Real.conjExponent r)) * (2 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_add (by norm_num) _ _
  rw [Real.rpow_one] at h2
  have h3 : -(1 / Real.conjExponent r) + 1 = 1 / r := by
    rw [one_div, one_div]; linarith
  rw [h3] at h2
  exact h2.symm

end Arith

end PrimeCarleson.Proof.Oplus

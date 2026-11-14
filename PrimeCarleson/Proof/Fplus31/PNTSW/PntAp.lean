module

public import PrimeCarleson.Proof.Fplus31.PNTSW.ApRiesz
public import PrimeCarleson.Proof.Fplus31.PNT.ApSum

/-!
# `pnt_ap_sw`: the prime number theorem in arithmetic progressions, classical error term

Part of the prime number theorem in progressions on the classical zero-free region
(`PNTSW/Main.lean`). For a nonnegative weight sequence `w` and `0 < h ≤ x`, with
`R(y) = ∑_{n ≤ y} w(n)(y - n)` and `ψ(x) = ∑_{n ≤ x} w(n)`,

`R(x) - R(x - h) ≤ h ψ(x) ≤ R(x + h) - R(x)`  (`rieszMean_sub_le`, `le_rieszMean_add_sub`).

With `w(n) = Λ(n) 1_{n ≡ a (q)}`, `h = x exp (-c √(log x))` and `riesz_ap_sw` this gives
`pnt_ap_sw`: there are `c > 0` and `x₀` such that for `x ≥ x₀`, `log q ≤ c √(log x)` and all `a`,
`|ψ(x; q, a) - [(a, q) = 1] x/φ(q)| ≤ x exp (-c √(log x))`.  For `(a, q) > 1` only the powers of
one prime `p ∣ gcd(a, q)` occur and `ψ ≤ log x` (`vonMangoldt_apSet_noncoprime_le`).
-/

@[expose] public noncomputable section

open ArithmeticFunction Filter
open scoped Real

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.PNTSW

/-- The Riesz mean `∑_{1 ≤ n ≤ y} w(n)(y - n)` of a weight sequence. -/
def rieszMean (w : ℕ → ℝ) (y : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, w n * (y - n)

/-- The partial sum `∑_{1 ≤ n ≤ x} w(n)`. -/
def partialSumW (w : ℕ → ℝ) (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, w n

/-- The Riesz mean as a sum over `n ≤ M` with `max (y - n) 0`. -/
theorem rieszMean_eq_sum_max (w : ℕ → ℝ) {y : ℝ} (hy : 0 ≤ y) {M : ℕ} (hM : ⌊y⌋₊ ≤ M) :
    rieszMean w y = ∑ n ∈ Finset.Icc 1 M, w n * max (y - n) 0 := by
  unfold rieszMean
  have hsub : Finset.Icc 1 ⌊y⌋₊ ⊆ Finset.Icc 1 M := Finset.Icc_subset_Icc le_rfl hM
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have : (n : ℝ) ≤ y := (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le hy)
    rw [max_eq_left (by linarith)]
  · intro n hn hn'
    have h1 := Finset.mem_Icc.mp hn
    have h2 : ⌊y⌋₊ < n := by
      by_contra hc
      exact hn' (Finset.mem_Icc.mpr ⟨h1.1, not_lt.mp hc⟩)
    have : y < n := by
      have := Nat.lt_floor_add_one y
      have h3 : ((⌊y⌋₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast h2
      linarith
    rw [max_eq_right (by linarith), mul_zero]

/-- The partial sum as a sum over `n ≤ M` with an indicator. -/
theorem partialSumW_eq_sum_ite (w : ℕ → ℝ) {x : ℝ} (hx : 0 ≤ x) {M : ℕ} (hM : ⌊x⌋₊ ≤ M) :
    partialSumW w x = ∑ n ∈ Finset.Icc 1 M, if (n : ℝ) ≤ x then w n else 0 := by
  unfold partialSumW
  have hsub : Finset.Icc 1 ⌊x⌋₊ ⊆ Finset.Icc 1 M := Finset.Icc_subset_Icc le_rfl hM
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have : (n : ℝ) ≤ x := (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le hx)
    simp only [this, ↓reduceIte]
  · intro n hn hn'
    have h1 := Finset.mem_Icc.mp hn
    have h2 : ⌊x⌋₊ < n := by
      by_contra hc
      exact hn' (Finset.mem_Icc.mpr ⟨h1.1, not_lt.mp hc⟩)
    have : x < n := by
      have := Nat.lt_floor_add_one x
      have h3 : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast h2
      linarith
    simp only [not_le.mpr this, ↓reduceIte]

/-- `h ψ(x) ≤ R(x + h) - R(x)` for a nonnegative weight. -/
theorem le_rieszMean_add_sub {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {x h : ℝ} (hx : 0 ≤ x)
    (hh : 0 < h) : h * partialSumW w x ≤ rieszMean w (x + h) - rieszMean w x := by
  have hM : ⌊x⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_le_floor (by linarith)
  rw [rieszMean_eq_sum_max w (by linarith : 0 ≤ x + h) le_rfl,
    rieszMean_eq_sum_max w hx hM, partialSumW_eq_sum_ite w hx hM, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [← mul_sub]
  by_cases hn : (n : ℝ) ≤ x
  · simp only [hn, ↓reduceIte]
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    nlinarith [hw n]
  · simp only [hn, ↓reduceIte]
    rw [max_eq_right (by linarith : x - n ≤ 0)]
    have : 0 ≤ max (x + h - n) 0 := le_max_right _ _
    nlinarith [hw n]

/-- `R(x) - R(x - h) ≤ h ψ(x)` for a nonnegative weight. -/
theorem rieszMean_sub_le {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {x h : ℝ} (hh : 0 < h)
    (hxh : h ≤ x) : rieszMean w x - rieszMean w (x - h) ≤ h * partialSumW w x := by
  have hx : 0 ≤ x := by linarith
  have hM : ⌊x - h⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor (by linarith)
  rw [rieszMean_eq_sum_max w hx le_rfl, rieszMean_eq_sum_max w (by linarith : 0 ≤ x - h) hM,
    partialSumW_eq_sum_ite w hx le_rfl, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [← mul_sub]
  by_cases hn : (n : ℝ) ≤ x
  · simp only [hn, ↓reduceIte]
    rw [max_eq_left (by linarith)]
    have : x - h - n ≤ max (x - h - n) 0 := le_max_left _ _
    nlinarith [hw n]
  · simp only [hn, ↓reduceIte]
    rw [max_eq_right (by linarith : x - n ≤ 0), max_eq_right (by linarith : x - h - n ≤ 0)]
    simp

/-- The weight `Λ(n) 1_{n ≡ a (q)}`. -/
def apWeight (q : ℕ) (a : ℤ) (n : ℕ) : ℝ := if (n : ℤ) ≡ a [ZMOD q] then Λ n else 0

/-- `Λ(n) 1_{n ≡ a (q)} ≥ 0`. -/
theorem apWeight_nonneg (q : ℕ) (a : ℤ) (n : ℕ) : 0 ≤ apWeight q a n := by
  unfold apWeight
  split_ifs
  · exact vonMangoldt_nonneg
  · exact le_rfl

/-- The Riesz mean of the progression weight. -/
theorem rieszMean_apWeight (q : ℕ) (a : ℤ) (y : ℝ) :
    rieszMean (apWeight q a) y =
      ∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), Λ n * (y - n) := by
  unfold rieszMean apWeight
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> simp

/-- The partial sum of the progression weight is `ψ(x; q, a)`. -/
theorem partialSumW_apWeight (q : ℕ) (a : ℤ) (x : ℝ) :
    partialSumW (apWeight q a) x =
      ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), Λ n := by
  unfold partialSumW apWeight
  rw [Finset.sum_filter]


/-- The coprime case of the sandwich, abstract form: if `|R(y) - y² u/2| ≤ E` for `y ∈ [x/2, 2x]`
(`R` the Riesz mean of `Λ 1_{n ≡ a (q)}`, `u = 1/φ(q) ≤ 1`) and `0 < h ≤ x/2`, then
`h |ψ(x; q, a) - x u| ≤ h²/2 + 2E`. -/
theorem psi_coprime_sandwich {q : ℕ} (hq : 1 ≤ q) (a : ℤ) {x h E : ℝ} (hx : 0 < x) (hh : 0 < h)
    (hhx : h ≤ x / 2)
    (hbound : ∀ y : ℝ, x / 2 ≤ y → y ≤ 2 * x →
      |rieszMean (apWeight q a) y - y ^ 2 * (Nat.totient q : ℝ)⁻¹ / 2| ≤ E) :
    h * |∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), Λ n -
        x / (Nat.totient q : ℝ)| ≤ h ^ 2 / 2 + 2 * E := by
  have hφ1 : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  set u : ℝ := ((Nat.totient q : ℝ))⁻¹ with hu
  have hu1 : u ≤ 1 := inv_le_one_of_one_le₀ hφ1
  have hu0 : 0 ≤ u := inv_nonneg.mpr (by linarith)
  have hxu : x / (Nat.totient q : ℝ) = x * u := by rw [hu, div_eq_mul_inv]
  have e1 := hbound (x + h) (by linarith) (by linarith)
  have e2 := hbound x (by linarith) (by linarith)
  have e3 := hbound (x - h) (by linarith) (by linarith)
  rw [abs_le] at e1 e2 e3
  have up := le_rieszMean_add_sub (apWeight_nonneg q a) hx.le hh
  have lo := rieszMean_sub_le (apWeight_nonneg q a) hh (by linarith : h ≤ x)
  rw [partialSumW_apWeight] at up lo
  rw [hxu]
  set ψ : ℝ := ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), Λ n
    with hψ
  have hh2u : h ^ 2 * u ≤ h ^ 2 := by
    linarith only [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hu1)]
  have hup : h * (ψ - x * u) ≤ h ^ 2 / 2 + 2 * E := by
    have : h * ψ ≤ x * h * u + h ^ 2 * u / 2 + 2 * E := by linarith only [up, e1.2, e2.1]
    linarith only [this, hh2u]
  have hlo : -(h ^ 2 / 2 + 2 * E) ≤ h * (ψ - x * u) := by
    have : x * h * u - h ^ 2 * u / 2 - 2 * E ≤ h * ψ := by linarith only [lo, e2.1, e3.2]
    linarith only [this, hh2u]
  rw [← abs_of_pos hh, ← abs_mul, abs_of_pos hh, abs_le]
  exact ⟨hlo, hup⟩

/-- The trivial bound for `ψ(x; q, a)` when `gcd(a, q) > 1`. -/
theorem psi_noncoprime_le {q : ℕ} {a : ℤ} (hcop : ¬ IsCoprime a (q : ℤ)) {x : ℝ}
    (hx : 1 ≤ x) :
    ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), Λ n ≤ Real.log x := by
  have hx0 : 0 < x := by linarith
  have hfl : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have h1 := vonMangoldt_apSet_noncoprime_le (r := q) (a := a) (lo := 0) hcop
    (le_refl ⌊x⌋₊) hfl
  rw [sum_apSet_vonMangoldt q a (Nat.zero_le _)] at h1
  have h0 : psiAP q a 0 = 0 := by
    unfold psiAP; simp
  rw [h0, sub_zero] at h1
  exact h1.trans (Real.log_le_log (by exact_mod_cast hfl) (Nat.floor_le hx0.le))

/-- The Riesz mean of `Λ 1_{n ≡ a (q)}` on `[x/2, 2x]`, from `riesz_ap_sw`. -/
theorem rieszMean_ap_bound {c₁ y₀ : ℝ}
    (hR : ∀ y : ℝ, y₀ ≤ y → ∀ (q : ℕ), 1 ≤ q →
      Real.log q ≤ √(Real.log y) → ∀ (a : ℤ), IsCoprime a (q : ℤ) →
      |∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), Λ n * (y - n) -
          y ^ 2 / (2 * (Nat.totient q : ℝ))| ≤ 4 * (y ^ 2 * Real.exp (-(c₁ * √(Real.log y)))))
    (hc₁ : 0 < c₁) {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (hcop : IsCoprime a (q : ℤ)) {x v : ℝ}
    (hx0 : 0 < x) (hlog : Real.log x = v ^ 2) (hv2 : 2 ≤ v) (h2y₀ : 2 * y₀ ≤ x)
    (hy₀ : 1 ≤ y₀) (hlogq : Real.log q ≤ v / 2) {y : ℝ} (hy1 : x / 2 ≤ y) (hy2 : y ≤ 2 * x) :
    |rieszMean (apWeight q a) y - y ^ 2 * (Nat.totient q : ℝ)⁻¹ / 2| ≤
      16 * x ^ 2 * Real.exp (-(7 / 10 * (c₁ * v))) := by
  have hy0 : 0 < y := by linarith
  have hyy₀ : y₀ ≤ y := by linarith
  have hlogy : v ^ 2 / 2 ≤ Real.log y := by
    have h1 : Real.log (x / 2) ≤ Real.log y := Real.log_le_log (by positivity) hy1
    rw [Real.log_div hx0.ne' (by norm_num), hlog] at h1
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have hv4 : 4 ≤ v ^ 2 := by nlinarith only [hv2]
    linarith only [h1, h2, hv4]
  have hsq : 7 / 10 * v ≤ √(Real.log y) := by
    apply Real.le_sqrt_of_sq_le
    linarith only [hlogy, sq_nonneg v]
  have hlogqy : Real.log q ≤ √(Real.log y) := by linarith only [hlogq, hsq, hv2]
  have h1 := hR y hyy₀ q hq hlogqy a hcop
  rw [← rieszMean_apWeight] at h1
  have e : y ^ 2 / (2 * (Nat.totient q : ℝ)) = y ^ 2 * (Nat.totient q : ℝ)⁻¹ / 2 := by
    field_simp
  rw [e] at h1
  refine h1.trans ?_
  have h2 : Real.exp (-(c₁ * √(Real.log y))) ≤ Real.exp (-(7 / 10 * (c₁ * v))) :=
    Real.exp_le_exp.mpr (by linarith only [mul_le_mul_of_nonneg_left hsq hc₁.le])
  have h3 : y ^ 2 ≤ 4 * x ^ 2 := by
    have := pow_le_pow_left₀ hy0.le hy2 2
    linarith only [this]
  calc 4 * (y ^ 2 * Real.exp (-(c₁ * √(Real.log y))))
      ≤ 4 * (4 * x ^ 2 * Real.exp (-(7 / 10 * (c₁ * v)))) := by gcongr
    _ = _ := by ring

/-- The sandwich with `h = x P`, `E = 16 x² P²`: `|ψ - x/φ| ≤ 33 x P` if `P ≤ 1/2`. -/
theorem psi_coprime_of_bound {q : ℕ} (hq : 1 ≤ q) (a : ℤ) {x P : ℝ} (hx : 0 < x) (hP : 0 < P)
    (hP2 : P ≤ 1 / 2)
    (hbound : ∀ y : ℝ, x / 2 ≤ y → y ≤ 2 * x →
      |rieszMean (apWeight q a) y - y ^ 2 * (Nat.totient q : ℝ)⁻¹ / 2| ≤ 16 * x ^ 2 * (P * P)) :
    |∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), Λ n -
        x / (Nat.totient q : ℝ)| ≤ 33 * (x * P) := by
  have hh0 : 0 < x * P := by positivity
  have hhx : x * P ≤ x / 2 := by
    have := mul_le_mul_of_nonneg_left hP2 hx.le
    linarith only [this]
  have hsand := psi_coprime_sandwich hq a hx hh0 hhx hbound
  have h1 : (x * P) * |∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), Λ n -
      x / (Nat.totient q : ℝ)| ≤ (x * P) * (33 * (x * P)) := by
    refine hsand.trans ?_
    linarith only [sq_nonneg (x * P)]
  exact le_of_mul_le_mul_left h1 hh0

/-- **`pnt_ap_sw`: the prime number theorem in progressions with the classical error term.**
There are `c > 0` and `x₀` such that for all `x ≥ x₀`, all `q ≥ 1` with `log q ≤ c √(log x)` and
all `a`: `|ψ(x; q, a) - [(a, q) = 1] x/φ(q)| ≤ x exp (-c √(log x))`. -/
theorem pnt_ap_sw (hZ : ClassicalZeroFreeRegion) (hS : NoSiegelZero) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ (q : ℕ), 1 ≤ q → ∀ (a : ℤ) (x : ℝ), x₀ ≤ x →
      Real.log q ≤ c * √(Real.log x) →
      |∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), (Λ n : ℝ) -
          (if IsCoprime a (q : ℤ) then x / (Nat.totient q : ℝ) else 0)| ≤
        x * Real.exp (-(c * √(Real.log x))) := by
  obtain ⟨c₁, hc₁, y₀, hy₀, hR⟩ := riesz_ap_sw hZ hS
  obtain ⟨v₁, hv₁⟩ := eventually_atTop.mp (Fplus31.eventually_poly_le_exp 2 1 1 one_pos)
  set c : ℝ := min (3 / 10 * c₁) (1 / 2) with hc
  have hc0 : 0 < c := lt_min (by positivity) (by norm_num)
  have hcc : c ≤ 3 / 10 * c₁ := min_le_left _ _
  have hc2 : c ≤ 1 / 2 := min_le_right _ _
  set v₂ : ℝ := max (max (max 2 v₁) (640 / c₁)) (√(Real.log (2 * y₀))) with hv₂
  have hv₂2 : 2 ≤ v₂ := le_trans (le_trans (le_max_left 2 v₁) (le_max_left _ _)) (le_max_left _ _)
  refine ⟨c, hc0, Real.exp (v₂ ^ 2), ?_, ?_⟩
  · have : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    refine this.trans (Real.exp_le_exp.mpr ?_)
    nlinarith only [hv₂2]
  intro q hq a x hx hqx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlogx : v₂ ^ 2 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at this
  set v : ℝ := √(Real.log x) with hv
  have hlog : Real.log x = v ^ 2 := by
    rw [hv, Real.sq_sqrt (by linarith only [hlogx, sq_nonneg v₂])]
  have hvv : v₂ ≤ v := by
    rw [hv]; exact Real.le_sqrt_of_sq_le hlogx
  have hv2 : 2 ≤ v := le_trans hv₂2 hvv
  have hxe : x = Real.exp (v ^ 2) := by rw [← hlog, Real.exp_log hx0]
  have hx1 : 1 ≤ x := by rw [hxe]; exact Real.one_le_exp (by positivity)
  by_cases hcop : IsCoprime a (q : ℤ)
  · simp only [hcop, ↓reduceIte]
    set t : ℝ := c₁ * v with ht
    have ht640 : 640 ≤ t := by
      have h1 : 640 / c₁ ≤ v := le_trans (le_max_right (max 2 v₁) (640 / c₁))
        (le_trans (le_max_left _ _) hvv)
      rw [div_le_iff₀ hc₁] at h1
      rw [ht]; linarith
    set P : ℝ := Real.exp (-(7 / 20 * t)) with hP
    have hP0 : 0 < P := Real.exp_pos _
    have hP2 : P * P = Real.exp (-(7 / 10 * t)) := by
      rw [hP, ← Real.exp_add]; ring_nf
    have hP12 : P ≤ 1 / 2 := by
      have h1 : Real.exp (-(7 / 20 * t)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      have h2 : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg]
        have : (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp (1 : ℝ); linarith
        rw [inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) this
      exact h1.trans h2
    have hlogq : Real.log q ≤ v / 2 := by
      calc Real.log q ≤ c * v := hqx
        _ ≤ 1 / 2 * v := mul_le_mul_of_nonneg_right hc2 (by linarith only [hv2])
        _ = v / 2 := by ring
    have h2y₀ : 2 * y₀ ≤ x := by
      have h1 : √(Real.log (2 * y₀)) ≤ v₂ := le_max_right _ _
      have h2 : Real.log (2 * y₀) ≤ v₂ ^ 2 := by
        have h4 := Real.sq_sqrt (Real.log_nonneg (by linarith : 1 ≤ 2 * y₀))
        have h5 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
        linarith only [h4, h5]
      have h3 : Real.log (2 * y₀) ≤ Real.log x := h2.trans hlogx
      exact (Real.log_le_log_iff (by linarith) hx0).mp h3
    have hbound : ∀ y : ℝ, x / 2 ≤ y → y ≤ 2 * x →
        |rieszMean (apWeight q a) y - y ^ 2 * (Nat.totient q : ℝ)⁻¹ / 2| ≤
          16 * x ^ 2 * (P * P) := by
      intro y hy1 hy2
      rw [hP2]
      exact rieszMean_ap_bound hR hc₁ hq hcop hx0 hlog hv2 h2y₀ hy₀ hlogq hy1 hy2
    have hfin := psi_coprime_of_bound hq a hx0 hP0 hP12 hbound
    refine hfin.trans ?_
    have hcv : c * v ≤ 3 / 10 * t := by
      rw [ht]
      have := mul_le_mul_of_nonneg_right hcc (by linarith only [hv2] : (0 : ℝ) ≤ v)
      linarith only [this]
    have h33 : 33 * P ≤ Real.exp (-(3 / 10 * t)) := by
      have hexp : Real.exp (-(3 / 10 * t)) = Real.exp (-(7 / 20 * t)) * Real.exp (1 / 20 * t) := by
        rw [← Real.exp_add]; ring_nf
      rw [hexp, ← hP]
      have : (33 : ℝ) ≤ Real.exp (1 / 20 * t) := by
        have := Real.add_one_le_exp (1 / 20 * t); linarith
      have := mul_le_mul_of_nonneg_left this hP0.le
      linarith only [this]
    have hexp2 : Real.exp (-(3 / 10 * t)) ≤ Real.exp (-(c * v)) :=
      Real.exp_le_exp.mpr (by linarith)
    calc 33 * (x * P) = x * (33 * P) := by ring
      _ ≤ x * Real.exp (-(3 / 10 * t)) := mul_le_mul_of_nonneg_left h33 hx0.le
      _ ≤ x * Real.exp (-(c * v)) := mul_le_mul_of_nonneg_left hexp2 hx0.le
  · simp only [hcop, ↓reduceIte, sub_zero]
    have hψ := psi_noncoprime_le (q := q) hcop hx1
    have hnn : 0 ≤ ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), Λ n :=
      Finset.sum_nonneg fun n _ => vonMangoldt_nonneg
    rw [abs_of_nonneg hnn]
    refine hψ.trans ?_
    rw [hlog]
    have hv1 : v₁ ≤ v := le_trans (le_trans (le_max_right 2 v₁) (le_max_left _ _))
      (le_trans (le_max_left _ _) hvv)
    have hpoly := hv₁ v hv1
    have h1 : v ^ 2 ≤ Real.exp v := by simpa using hpoly
    have h2 : Real.exp v ≤ x * Real.exp (-(c * v)) := by
      rw [hxe, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have ha := mul_le_mul_of_nonneg_right hc2 (by linarith only [hv2] : (0 : ℝ) ≤ v)
      have hb := mul_le_mul_of_nonneg_left hv2 (by linarith only [hv2] : (0 : ℝ) ≤ v)
      linarith only [ha, hb, hv2]
    linarith

end PrimeCarleson.Proof.Fplus31.PNTSW

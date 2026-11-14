module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Cast.Field

/-!
# Vaughan's identity at `U = V = N^{1/3}`

Part of the Vaughan decomposition in the proof of [F+] Proposition 3.1 (Tao–Teräväinen
arXiv:2107.02158v4 TeX (`orthogonality.tex`) L215-L219). The identity is an exact pointwise identity
valid for every `n ≥ 1` (not only `n > N^{1/3}`):

`Λ(n) = Λ(n) 1_{n³ ≤ N} + ∑_{b ∣ n, b³ ≤ N} μ(b) log (n/b) - ∑_{d ∣ n} a_d
        + ∑_{c ∣ n} Λ(c) 1_{c³ > N} b_{n/c}`

with `a_d = ∑_{bc = d} μ(b) 1_{b³ ≤ N} Λ(c) 1_{c³ ≤ N}` (`vaughanA`, supported on `d³ ≤ N²`,
`|a_d| ≤ log d`) and `b_w = ∑_{e ∣ w, e³ > N} μ(e)` (`typeTwoCoeff`, `|b_w| ≤ τ(w)`, supported on
`w³ > N`).  The cut-offs are `b ≤ N^{1/3} ⟺ b³ ≤ N`, so no real cube root appears.

Provenance: the `openai/math` library has `vaughan_identity (U V : ℕ)`
(`OAI/NumberTheory/PrimeGaps/CharacterErrors.lean` L389, cut-offs `n ≤ U`, `n ≤ V`) but it is not in
the vendored `OAI` slice. The identity is the six-line algebra below, reproved here for arbitrary
decidable cut-off predicates: `Λ = Λ_s + log * μ_s - Λ_s * μ_s * ζ + Λ_b * μ_b * ζ` with
`Λ * ζ = log`, `μ * ζ = 1`.

* `restrictAF`: restriction of an arithmetic function to a decidable set of indices;
* `vaughan_identity`: the identity in the algebra of arithmetic functions;
* `vaughanA`, `typeTwoCoeff`, `vaughan_apply`: the pointwise form used by the decomposition;
* `abs_vaughanA_le_log`, `abs_typeTwoCoeff_le`, `vaughanA_eq_zero`, `typeTwoCoeff_eq_zero`.
-/

@[expose] public noncomputable section

open ArithmeticFunction Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- `Λ` as a real arithmetic function. -/
local notation "Λr" => (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ)
/-- `μ` as a real arithmetic function. -/
local notation "μr" =>
  ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
/-- `ζ` as a real arithmetic function. -/
local notation "ζr" => ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)

/-- Subtraction of real arithmetic functions is pointwise. -/
theorem af_sub_apply (f g : ArithmeticFunction ℝ) (n : ℕ) : (f - g) n = f n - g n := rfl

/-- The restriction of an arithmetic function to the indices satisfying `p`. -/
def restrictAF (p : ℕ → Prop) [DecidablePred p] (f : ArithmeticFunction ℝ) :
    ArithmeticFunction ℝ :=
  ⟨fun n => if p n then f n else 0, by simp⟩

/-- `restrictAF p f n = if p n then f n else 0`. -/
theorem restrictAF_apply (p : ℕ → Prop) [DecidablePred p] (f : ArithmeticFunction ℝ) (n : ℕ) :
    restrictAF p f n = if p n then f n else 0 := rfl

/-- **Vaughan's identity** for arbitrary cut-off predicates `p` (on `Λ`) and `q` (on `μ`):
`Λ = Λ_p + μ_q * log - μ_q * Λ_p * ζ + (μ - μ_q) * (Λ - Λ_p) * ζ`. -/
theorem vaughan_identity (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q] :
    Λr = restrictAF p Λr + restrictAF q μr * ArithmeticFunction.log -
        restrictAF q μr * restrictAF p Λr * ζr +
      (μr - restrictAF q μr) * (Λr - restrictAF p Λr) * ζr := by
  have hlog : Λr * ζr = ArithmeticFunction.log := vonMangoldt_mul_zeta
  have hmu : μr * ζr = 1 := coe_moebius_mul_coe_zeta
  rw [← hlog]
  linear_combination (restrictAF p Λr - Λr) * hmu

/-- The type I coefficients `a_d = ∑_{bc = d, b³ ≤ N, c³ ≤ N} μ(b) Λ(c)` of the `-Λ_U μ_V ζ`
term. -/
def vaughanA (N d : ℕ) : ℝ :=
  ∑ x ∈ d.divisorsAntidiagonal,
    (if x.1 ^ 3 ≤ N then ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) else 0) *
      (if x.2 ^ 3 ≤ N then ArithmeticFunction.vonMangoldt x.2 else 0)

/-- The type II coefficients `b_w = ∑_{e ∣ w, e³ > N} μ(e)`. -/
def typeTwoCoeff (N w : ℕ) : ℝ :=
  ∑ e ∈ w.divisors, if N < e ^ 3 then ((ArithmeticFunction.moebius e : ℤ) : ℝ) else 0

/-- **Vaughan's identity at `U = V = N^{1/3}`**, pointwise, for every `n ≥ 1`. -/
theorem vaughan_apply (N : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ArithmeticFunction.vonMangoldt n =
      (if n ^ 3 ≤ N then ArithmeticFunction.vonMangoldt n else 0) +
      ∑ b ∈ n.divisors, (if b ^ 3 ≤ N then ((ArithmeticFunction.moebius b : ℤ) : ℝ) else 0) *
        (Real.log n - Real.log b) -
      ∑ d ∈ n.divisors, vaughanA N d +
      ∑ c ∈ n.divisors, (if N < c ^ 3 then ArithmeticFunction.vonMangoldt c else 0) *
        typeTwoCoeff N (n / c) := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (vaughan_identity (fun m : ℕ => m ^ 3 ≤ N) (fun m : ℕ => m ^ 3 ≤ N))
  simp only [ArithmeticFunction.add_apply, af_sub_apply] at h
  have hA : (restrictAF (fun m : ℕ => m ^ 3 ≤ N) μr *
        restrictAF (fun m : ℕ => m ^ 3 ≤ N) Λr * ζr) n = ∑ d ∈ n.divisors, vaughanA N d := by
    rw [coe_mul_zeta_apply]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [ArithmeticFunction.mul_apply]
    simp [vaughanA, restrictAF_apply]
  have hL : (restrictAF (fun m : ℕ => m ^ 3 ≤ N) μr * ArithmeticFunction.log) n =
      ∑ b ∈ n.divisors, (if b ^ 3 ≤ N then ((ArithmeticFunction.moebius b : ℤ) : ℝ) else 0) *
        (Real.log n - Real.log b) := by
    rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
      (fun b m => restrictAF (fun m : ℕ => m ^ 3 ≤ N) μr b * ArithmeticFunction.log m)]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hbn : b ∣ n := Nat.dvd_of_mem_divisors hb
    have hb0 : (b : ℝ) ≠ 0 := by
      have := Nat.pos_of_mem_divisors hb
      exact_mod_cast this.ne'
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    rw [restrictAF_apply, ArithmeticFunction.log_apply, Nat.cast_div hbn hb0,
      Real.log_div hn0 hb0]
    simp
  have hB : (((μr - restrictAF (fun m : ℕ => m ^ 3 ≤ N) μr) *
        (Λr - restrictAF (fun m : ℕ => m ^ 3 ≤ N) Λr)) * ζr) n =
      ∑ c ∈ n.divisors, (if N < c ^ 3 then ArithmeticFunction.vonMangoldt c else 0) *
        typeTwoCoeff N (n / c) := by
    have hcomm : ((μr - restrictAF (fun m : ℕ => m ^ 3 ≤ N) μr) *
        (Λr - restrictAF (fun m : ℕ => m ^ 3 ≤ N) Λr)) * ζr =
        (Λr - restrictAF (fun m : ℕ => m ^ 3 ≤ N) Λr) *
          ((μr - restrictAF (fun m : ℕ => m ^ 3 ≤ N) μr) * ζr) := by ring
    rw [hcomm, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
      (fun c w => (Λr - restrictAF (fun m : ℕ => m ^ 3 ≤ N) Λr) c *
        ((μr - restrictAF (fun m : ℕ => m ^ 3 ≤ N) μr) * ζr) w)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [coe_mul_zeta_apply]
    congr 1
    · simp only [af_sub_apply, restrictAF_apply]
      by_cases hc : c ^ 3 ≤ N
      · simp [hc]
      · simp [hc, not_le.mp hc]
    · unfold typeTwoCoeff
      refine Finset.sum_congr rfl fun e _ => ?_
      simp only [af_sub_apply, restrictAF_apply, intCoe_apply]
      by_cases he : e ^ 3 ≤ N
      · simp [he, not_lt.mpr he]
      · simp [he, not_le.mp he]
  rw [hA, hL, hB] at h
  rw [restrictAF_apply] at h
  linarith

/-- `|a_d| ≤ log d`. -/
theorem abs_vaughanA_le_log (N d : ℕ) : |vaughanA N d| ≤ Real.log d := by
  unfold vaughanA
  calc |∑ x ∈ d.divisorsAntidiagonal,
        (if x.1 ^ 3 ≤ N then ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) else 0) *
          (if x.2 ^ 3 ≤ N then ArithmeticFunction.vonMangoldt x.2 else 0)|
      ≤ ∑ x ∈ d.divisorsAntidiagonal,
        |(if x.1 ^ 3 ≤ N then ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) else 0) *
          (if x.2 ^ 3 ≤ N then ArithmeticFunction.vonMangoldt x.2 else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ d.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt x.2 := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [abs_mul]
        have h1 : |(if x.1 ^ 3 ≤ N then ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) else 0)| ≤
            1 := by
          split_ifs
          · exact_mod_cast abs_moebius_le_one
          · simp
        have h2 : |(if x.2 ^ 3 ≤ N then ArithmeticFunction.vonMangoldt x.2 else 0)| ≤
            ArithmeticFunction.vonMangoldt x.2 := by
          split_ifs
          · rw [abs_of_nonneg vonMangoldt_nonneg]
          · simp
        calc |(if x.1 ^ 3 ≤ N then ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) else 0)| *
              |(if x.2 ^ 3 ≤ N then ArithmeticFunction.vonMangoldt x.2 else 0)|
            ≤ 1 * ArithmeticFunction.vonMangoldt x.2 :=
              mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
          _ = ArithmeticFunction.vonMangoldt x.2 := one_mul _
    _ = ∑ c ∈ d.divisors, ArithmeticFunction.vonMangoldt c := by
        rw [Nat.sum_divisorsAntidiagonal' (fun _ c => ArithmeticFunction.vonMangoldt c)]
    _ = Real.log d := vonMangoldt_sum

/-- `a_d = 0` unless `d³ ≤ N²` (the level of the type I sum is `N^{2/3}`). -/
theorem vaughanA_eq_zero {N d : ℕ} (h : N ^ 2 < d ^ 3) : vaughanA N d = 0 := by
  unfold vaughanA
  refine Finset.sum_eq_zero fun x hx => ?_
  have hxd : x.1 * x.2 = d := Nat.mem_divisorsAntidiagonal.mp hx |>.1
  by_cases h1 : x.1 ^ 3 ≤ N
  · by_cases h2 : x.2 ^ 3 ≤ N
    · exfalso
      have : d ^ 3 ≤ N ^ 2 := by
        calc d ^ 3 = x.1 ^ 3 * x.2 ^ 3 := by rw [← hxd, mul_pow]
          _ ≤ N * N := Nat.mul_le_mul h1 h2
          _ = N ^ 2 := by ring
      omega
    · simp [h2]
  · simp [h1]

/-- `|b_w| ≤ τ(w)`. -/
theorem abs_typeTwoCoeff_le (N w : ℕ) : |typeTwoCoeff N w| ≤ (w.divisors.card : ℝ) := by
  unfold typeTwoCoeff
  calc |∑ e ∈ w.divisors, if N < e ^ 3 then ((ArithmeticFunction.moebius e : ℤ) : ℝ) else 0|
      ≤ ∑ e ∈ w.divisors,
          |if N < e ^ 3 then ((ArithmeticFunction.moebius e : ℤ) : ℝ) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ w.divisors, (1 : ℝ) := by
        refine Finset.sum_le_sum fun e _ => ?_
        split_ifs
        · exact_mod_cast abs_moebius_le_one
        · simp
    _ = (w.divisors.card : ℝ) := by simp

/-- `b_w = 0` unless `w³ > N`. -/
theorem typeTwoCoeff_eq_zero {N w : ℕ} (h : w ^ 3 ≤ N) : typeTwoCoeff N w = 0 := by
  unfold typeTwoCoeff
  refine Finset.sum_eq_zero fun e he => ?_
  have hw : w ≠ 0 := (Nat.mem_divisors.mp he).2
  have hew : e ≤ w := Nat.le_of_dvd (Nat.pos_of_ne_zero hw) (Nat.dvd_of_mem_divisors he)
  have : e ^ 3 ≤ N := (Nat.pow_le_pow_left hew 3).trans h
  simp [not_lt.mpr this]

end PrimeCarleson.Proof.Fplus31

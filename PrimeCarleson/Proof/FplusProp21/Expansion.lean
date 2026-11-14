module

public import PrimeCarleson.Proof.FplusProp21.Counting
public import PrimeCarleson.Proof.Common.GowersLp
public import PrimeCarleson.Proof.Goal0.Basic
public import PrimeCarleson.Frozen.BlockWeight

/-!
# Expansion of `‖Λ_Q 1_{[M]}‖_{U³(ℤ)}⁸` over the cube

The first step of the proof of [F+] Proposition 2.1 ([F+] TeX
L738–L756 and L812–L817). The steps, with their sources:

* [F+] `cube-linear-form`, L749–L756 (`cubeL0`, `cubeLi`): for `θ_ω = (-1)^{|ω|} a_ω / q_ω`,
  `L_0 = ∑_ω θ_ω` and `L_i = ∑_{ω_i = 1} θ_ω = ∑_ω ω_i θ_ω`;
* [F+] `expansion-u3-norm`, L738–L748 (`gowersNorm_blockWeight_pow_eight`): with the pairs `(q, a)`,
  `q ∈ B`, `1 ≤ a ≤ q`, `(a, q) = 1` (`qaPairs`), and `w_B = ∑_{q ∈ B} μ(q)/φ(q) c_q`,
  `‖w_B 1_{[M]}‖_{U³(ℤ)}⁸ = ∑_{(q_ω, a_ω)_ω} ∏_ω μ(q_ω)/φ(q_ω) · W_M(L_0, L_1, L_2, L_3)`,
  `W_M(L) = ∑_{x, h} ∏_ω 1_{[M]}(x + ω·h) e(x L_0 + h_1 L_1 + h_2 L_2 + h_3 L_3)` (`cubeW`); the
  `c_q` uses `e(an/q)` and [F+] `e(-an/q)`, which only flips every `θ_ω`;
* [F+] L549 (the norm of the indicator of an interval), upper side, used by the diagonal reduction
  of [F+] L781–L791 (`gowersNorm_indicator_pow_eight`): `‖1_{[M]}‖_{U³(ℤ)}⁸ = W_M(0)`, and
  `W_M(L) = W_M(0)` when every `L_j` is an integer (`cubeW_eq_of_isInt`);
* [F+] `cube-faces-linear-form-2`, L812–L817 (`isInt_faceSum_of_cubeDiag`) and its scaled form
  (`faceIntegral_of_cubeDiag`): integral `L_0, …, L_3` make all six signed face sums
  `∑_{ω_i = j} θ_ω` integral (the face `ω_i = 0` is `L_0 - L_i`), which is the hypothesis
  `FaceIntegral` of the counting step.
-/

@[expose] public noncomputable section

open Finset
open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.FplusProp21

open PrimeCarleson.Proof.Goal0

/-! ### The cube points and the conjugations -/

/-- The vertex `x + ω · h = x + ω₁ h₁ + ω₂ h₂ + ω₃ h₃` of the parallelepiped. -/
def cubePt (ω : Cube) (x a b k : ℤ) : ℤ :=
  x + ((ω 0 : ℕ) : ℤ) * a + ((ω 1 : ℕ) : ℤ) * b + ((ω 2 : ℕ) : ℤ) * k

/-- `C^{|ω|} z`: complex conjugation applied `|ω|` times. -/
def cubeConj (ω : Cube) (z : ℂ) : ℂ := if Even (cubeWt ω) then z else conj z

/-- **The triple difference as a product over the cube**:
`Δ_{h₁,h₂,h₃} F(x) = ∏_ω C^{|ω|} F(x + ω · h)` ((e;GowersDef) of [F+]). -/
theorem multDiff_three_eq_prod (F : ℤ → ℂ) (x a b k : ℤ) :
    multDiff 3 ![a, b, k] F x = ∏ ω : Cube, cubeConj ω (F (cubePt ω x a b k)) := by
  have h1 : ¬ Even 1 := by decide
  have h2 : Even 2 := by decide
  have h3 : ¬ Even 3 := by decide
  rw [Common.gowersLp_multDiff_three, prod_cube]
  simp [cubeConj, cubePt, cubeWt, Fin.sum_univ_three, h1, h2, h3]

/-- The vertex `ω = 0` is `x`. -/
theorem cubePt_zero (x a b k : ℤ) : cubePt (fun _ => 0) x a b k = x := by
  simp [cubePt]

/-- The cube indicator `∏_ω 1_{[M]}(x + ω · h)`. -/
def CubeIn (M : ℕ) (x a b k : ℤ) : Prop := ∀ ω : Cube, cubePt ω x a b k ∈ Icc (1 : ℤ) M

/-- The cube indicator is decidable. -/
instance (M : ℕ) (x a b k : ℤ) : Decidable (CubeIn M x a b k) := by
  unfold CubeIn
  infer_instance

/-- **The `U³(ℤ)` sum over the cube**, for `F` supported in `[M] = {1, …, M}`: the variables
`x, h₁, h₂, h₃` all run over `[-M, M]`. -/
theorem gowersNorm_pow_eight_eq_sum_prod (F : ℤ →₀ ℂ) (M : ℕ)
    (hF : ∀ x, F x ≠ 0 → x ∈ Icc (1 : ℤ) M) :
    ((gowersNorm 3 F : ℝ) : ℂ) ^ 8 =
      ∑ x ∈ Icc (-(M : ℤ)) M, ∑ a ∈ Icc (-(M : ℤ)) M, ∑ b ∈ Icc (-(M : ℤ)) M,
        ∑ k ∈ Icc (-(M : ℤ)) M, ∏ ω : Cube, cubeConj ω (F (cubePt ω x a b k)) := by
  have hB : ∀ x ∈ Icc (1 : ℤ) M, ∀ y ∈ Icc (1 : ℤ) M, y - x ∈ Icc (-(M : ℤ)) M := by
    intro x hx y hy
    simp only [mem_Icc] at hx hy ⊢
    omega
  rw [Common.gowersLp_pow_eight_eq F _ _ hF hB]
  simp_rw [multDiff_three_eq_prod]
  refine sum_subset (fun x hx => ?_) (fun x _ hx => ?_)
  · simp only [mem_Icc] at hx ⊢
    omega
  · refine sum_eq_zero fun a _ => sum_eq_zero fun b _ => sum_eq_zero fun k _ => ?_
    refine prod_eq_zero (mem_univ (fun _ => 0)) ?_
    rw [cubePt_zero]
    have : F x = 0 := by
      by_contra h
      exact hx (hF x h)
    simp [this, cubeConj]

/-! ### The linear forms and the exponential sum `W_M` -/

/-- `L_0 = ∑_ω θ_ω` (Source: [F+] `cube-linear-form`, L749–L756). -/
def cubeL0 (θ : Cube → ℝ) : ℝ := ∑ ω, θ ω

/-- `L_i = ∑_{ω_i = 1} θ_ω = ∑_ω ω_i θ_ω` (Source: [F+] `cube-linear-form`, L749–L756). -/
def cubeLi (θ : Cube → ℝ) (i : Fin 3) : ℝ := ∑ ω, ((ω i : ℕ) : ℝ) * θ ω

/-- The phase `∑_ω θ_ω (x + ω · h) = x L_0 + h₁ L_1 + h₂ L_2 + h₃ L_3`. -/
theorem sum_mul_cubePt (θ : Cube → ℝ) (x a b k : ℤ) :
    ∑ ω, θ ω * (cubePt ω x a b k : ℝ) =
      x * cubeL0 θ + a * cubeLi θ 0 + b * cubeLi θ 1 + k * cubeLi θ 2 := by
  simp only [cubePt, cubeL0, cubeLi, Int.cast_add, Int.cast_mul, Int.cast_natCast, mul_sum]
  rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun ω _ => ?_
  ring

/-- The exponential sum `W_M(L) = ∑_{x, h ∈ [-M, M]} ∏_ω 1_{[M]}(x + ω·h) e(x L_0 + h · L)`. -/
def cubeW (M : ℕ) (L0 L1 L2 L3 : ℝ) : ℂ :=
  ∑ x ∈ Icc (-(M : ℤ)) M, ∑ a ∈ Icc (-(M : ℤ)) M, ∑ b ∈ Icc (-(M : ℤ)) M,
    ∑ k ∈ Icc (-(M : ℤ)) M,
      if CubeIn M x a b k then e (x * L0 + a * L1 + b * L2 + k * L3) else 0

/-- `x` is an integer. -/
def IsInt (x : ℝ) : Prop := ∃ n : ℤ, x = n

/-- All four linear forms `L_0, …, L_3` of `θ` are integers. -/
def CubeDiag (θ : Cube → ℝ) : Prop := IsInt (cubeL0 θ) ∧ ∀ i, IsInt (cubeLi θ i)

/-- `CubeDiag` is decided classically. -/
instance (θ : Cube → ℝ) : Decidable (CubeDiag θ) := Classical.dec _

/-- Sums of integers are integers. -/
theorem IsInt.add {x y : ℝ} (hx : IsInt x) (hy : IsInt y) : IsInt (x + y) := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  exact ⟨m + n, by push_cast; ring⟩

/-- Differences of integers are integers. -/
theorem IsInt.sub {x y : ℝ} (hx : IsInt x) (hy : IsInt y) : IsInt (x - y) := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  exact ⟨m - n, by push_cast; ring⟩

/-- Integer multiples of integers are integers. -/
theorem IsInt.intCast_mul {x : ℝ} (hx : IsInt x) (m : ℤ) : IsInt (m * x) := by
  obtain ⟨n, rfl⟩ := hx
  exact ⟨m * n, by push_cast; ring⟩

/-- Finite sums of integers are integers. -/
theorem IsInt.sum {ι : Type*} (s : Finset ι) {f : ι → ℝ} (hf : ∀ i ∈ s, IsInt (f i)) :
    IsInt (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert i s hi ih =>
    rw [sum_insert hi]
    exact (hf i (mem_insert_self i s)).add (ih fun j hj => hf j (mem_insert_of_mem hj))

/-- `W_M(L)` only depends on `L` modulo `ℤ⁴`; for integral `L` it is `W_M(0)`. -/
theorem cubeW_eq_of_isInt (M : ℕ) {L0 L1 L2 L3 : ℝ} (h0 : IsInt L0) (h1 : IsInt L1)
    (h2 : IsInt L2) (h3 : IsInt L3) : cubeW M L0 L1 L2 L3 = cubeW M 0 0 0 0 := by
  unfold cubeW
  refine sum_congr rfl fun x _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ =>
    sum_congr rfl fun k _ => ?_
  split_ifs
  · obtain ⟨n0, rfl⟩ := h0
    obtain ⟨n1, rfl⟩ := h1
    obtain ⟨n2, rfl⟩ := h2
    obtain ⟨n3, rfl⟩ := h3
    have : (x : ℝ) * n0 + a * n1 + b * n2 + k * n3 =
        ((x * n0 + a * n1 + b * n2 + k * n3 : ℤ) : ℝ) := by
      push_cast; ring
    rw [this, e_intCast]
    simp [e_zero]
  · rfl

/-! ### The expansion -/

/-- The pairs `(q, a)` with `q ∈ B`, `1 ≤ a ≤ q`, `(a, q) = 1`. -/
def qaPairs (B : Finset ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  B.sigma fun q => (Icc 1 q).filter (fun a => Nat.Coprime a q)

/-- The coefficient `μ(q) / φ(q)` of a pair. -/
def qaCoef (t : Σ _ : ℕ, ℕ) : ℝ := ((ArithmeticFunction.moebius t.1 : ℤ) : ℝ) / (t.1.totient : ℝ)

/-- The frequency `a / q` of a pair. -/
def qaFreq (t : Σ _ : ℕ, ℕ) : ℝ := (t.2 : ℝ) / t.1

/-- The signed frequencies `θ_ω = (-1)^{|ω|} a_ω / q_ω`. -/
def cubeTheta (q a : Cube → ℕ) (ω : Cube) : ℝ := (cubeSign ω : ℝ) * ((a ω : ℝ) / q ω)

/-- The signed frequencies of a tuple of pairs. -/
def tupleTheta (τ : Cube → Σ _ : ℕ, ℕ) : Cube → ℝ :=
  cubeTheta (fun ω => (τ ω).1) (fun ω => (τ ω).2)

/-- `w_B(n) = ∑_{(q, a)} μ(q)/φ(q) e(a n / q)`. -/
theorem blockWeight_eq_sum (B : Finset ℕ) (n : ℤ) :
    blockWeight B n = ∑ t ∈ qaPairs B, (qaCoef t : ℂ) * e (qaFreq t * n) := by
  unfold blockWeight ramanujanSum qaPairs
  rw [sum_sigma]
  refine sum_congr rfl fun q _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  simp only [qaCoef, qaFreq]
  push_cast
  congr 2
  ring

/-- `C^{|ω|} w_B(n) = ∑_{(q, a)} μ(q)/φ(q) e((-1)^{|ω|} a n / q)`. -/
theorem cubeConj_blockWeight (B : Finset ℕ) (ω : Cube) (n : ℤ) :
    cubeConj ω (blockWeight B n) =
      ∑ t ∈ qaPairs B, (qaCoef t : ℂ) * e ((cubeSign ω : ℝ) * qaFreq t * n) := by
  rw [blockWeight_eq_sum]
  have hlin : ∀ z : ℂ, cubeConj ω z = if Even (cubeWt ω) then z else conj z := fun _ => rfl
  rw [hlin]
  split_ifs with h
  · refine sum_congr rfl fun t _ => ?_
    have : cubeSign ω = 1 := by unfold cubeSign; exact h.neg_one_pow
    simp [this]
  · rw [map_sum]
    refine sum_congr rfl fun t _ => ?_
    have : cubeSign ω = -1 := by unfold cubeSign; exact (Nat.not_even_iff_odd.1 h).neg_one_pow
    rw [map_mul, Complex.conj_ofReal, ← e_neg, this]
    congr 2
    push_cast
    ring

/-- `e(∑ tᵢ) = ∏ e(tᵢ)`. -/
theorem e_sum {ι : Type*} (s : Finset ι) (t : ι → ℝ) : e (∑ i ∈ s, t i) = ∏ i ∈ s, e (t i) := by
  unfold e
  push_cast
  rw [mul_sum, Complex.exp_sum]

/-- The pointwise expansion of the cube product of `w_B 1_{[M]}`. -/
theorem prod_cubeConj_restrict_blockWeight (B : Finset ℕ) (M : ℕ+) (x a b k : ℤ) :
    ∏ ω : Cube, cubeConj ω (restrictInterval M (blockWeight B) (cubePt ω x a b k)) =
      ∑ τ ∈ Fintype.piFinset (fun _ : Cube => qaPairs B),
        (∏ ω, (qaCoef (τ ω) : ℂ)) *
          (if CubeIn M x a b k then
            e (x * cubeL0 (tupleTheta τ) + a * cubeLi (tupleTheta τ) 0 +
              b * cubeLi (tupleTheta τ) 1 + k * cubeLi (tupleTheta τ) 2) else 0) := by
  classical
  have hpt : ∀ ω : Cube, cubeConj ω (restrictInterval M (blockWeight B) (cubePt ω x a b k)) =
      (if cubePt ω x a b k ∈ Icc (1 : ℤ) (M : ℕ) then (1 : ℂ) else 0) *
        ∑ t ∈ qaPairs B, (qaCoef t : ℂ) * e ((cubeSign ω : ℝ) * qaFreq t * cubePt ω x a b k) := by
    intro ω
    rw [← cubeConj_blockWeight]
    simp only [restrictInterval, Finsupp.indicator_apply]
    split_ifs with h
    · simp
    · simp [cubeConj]
  simp_rw [hpt]
  rw [prod_mul_distrib, prod_boole, prod_univ_sum, mul_sum]
  refine sum_congr rfl fun τ _ => ?_
  have hci : (∀ ω ∈ (univ : Finset Cube), cubePt ω x a b k ∈ Icc (1 : ℤ) (M : ℕ)) ↔
      CubeIn M x a b k := by simp [CubeIn]
  rw [prod_mul_distrib, ← e_sum]
  have hphase : ∑ ω, (cubeSign ω : ℝ) * qaFreq (τ ω) * (cubePt ω x a b k : ℝ) =
      x * cubeL0 (tupleTheta τ) + a * cubeLi (tupleTheta τ) 0 + b * cubeLi (tupleTheta τ) 1 +
        k * cubeLi (tupleTheta τ) 2 := by
    rw [← sum_mul_cubePt]
    refine sum_congr rfl fun ω _ => ?_
    simp [tupleTheta, cubeTheta, qaFreq]
  rw [hphase]
  simp only [hci]
  by_cases h : CubeIn M x a b k
  · simp only [h, ↓reduceIte]
    ring
  · simp only [h, ↓reduceIte]
    ring

/-- Exchanging a finite sum with a fourfold box sum. -/
theorem sum4_sum_comm {ι : Type*} (J : Finset ℤ) (T : Finset ι) (g : ℤ → ℤ → ℤ → ℤ → ι → ℂ) :
    ∑ x ∈ J, ∑ a ∈ J, ∑ b ∈ J, ∑ k ∈ J, ∑ τ ∈ T, g x a b k τ =
      ∑ τ ∈ T, ∑ x ∈ J, ∑ a ∈ J, ∑ b ∈ J, ∑ k ∈ J, g x a b k τ := by
  calc _ = ∑ x ∈ J, ∑ a ∈ J, ∑ b ∈ J, ∑ τ ∈ T, ∑ k ∈ J, g x a b k τ :=
        sum_congr rfl fun x _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_comm
    _ = ∑ x ∈ J, ∑ a ∈ J, ∑ τ ∈ T, ∑ b ∈ J, ∑ k ∈ J, g x a b k τ :=
        sum_congr rfl fun x _ => sum_congr rfl fun a _ => sum_comm
    _ = ∑ x ∈ J, ∑ τ ∈ T, ∑ a ∈ J, ∑ b ∈ J, ∑ k ∈ J, g x a b k τ :=
        sum_congr rfl fun x _ => sum_comm
    _ = _ := sum_comm

/-- **Expansion of the `U³` norm** (Source: [F+] `expansion-u3-norm`, L738–L748):
`‖w_B 1_{[M]}‖_{U³(ℤ)}⁸ = ∑_{(q_ω, a_ω)} ∏_ω μ(q_ω)/φ(q_ω) · W_M(L_0, L_1, L_2, L_3)`. -/
theorem gowersNorm_blockWeight_pow_eight (B : Finset ℕ) (M : ℕ+) :
    ((gowersNorm 3 (restrictInterval M (blockWeight B)) : ℝ) : ℂ) ^ 8 =
      ∑ τ ∈ Fintype.piFinset (fun _ : Cube => qaPairs B),
        (∏ ω, (qaCoef (τ ω) : ℂ)) *
          cubeW M (cubeL0 (tupleTheta τ)) (cubeLi (tupleTheta τ) 0) (cubeLi (tupleTheta τ) 1)
            (cubeLi (tupleTheta τ) 2) := by
  have hF : ∀ x, restrictInterval M (blockWeight B) x ≠ 0 → x ∈ Icc (1 : ℤ) (M : ℕ) := by
    intro x hx
    by_contra h
    exact hx (by simp [restrictInterval, Finsupp.indicator_apply, h])
  rw [gowersNorm_pow_eight_eq_sum_prod _ M hF]
  simp_rw [prod_cubeConj_restrict_blockWeight]
  rw [sum4_sum_comm]
  refine sum_congr rfl fun τ _ => ?_
  unfold cubeW
  simp_rw [mul_sum]

/-- **The normalizing constant as an exponential sum**: `‖1_{[M]}‖_{U³(ℤ)}⁸ = W_M(0)`. -/
theorem gowersNorm_indicator_pow_eight (M : ℕ+) :
    ((gowersNorm 3 (restrictInterval M 1) : ℝ) : ℂ) ^ 8 = cubeW M 0 0 0 0 := by
  have hF : ∀ x, restrictInterval M 1 x ≠ 0 → x ∈ Icc (1 : ℤ) (M : ℕ) := by
    intro x hx
    by_contra h
    exact hx (by simp [restrictInterval, Finsupp.indicator_apply, h])
  rw [gowersNorm_pow_eight_eq_sum_prod _ M hF]
  unfold cubeW
  refine sum_congr rfl fun x _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ =>
    sum_congr rfl fun k _ => ?_
  have hpt : ∀ ω : Cube, cubeConj ω (restrictInterval M 1 (cubePt ω x a b k)) =
      if cubePt ω x a b k ∈ Icc (1 : ℤ) (M : ℕ) then (1 : ℂ) else 0 := by
    intro ω
    simp only [restrictInterval, Finsupp.indicator_apply]
    split_ifs <;> simp [cubeConj]
  simp_rw [hpt]
  rw [prod_boole]
  simp [CubeIn, e_zero]

/-! ### Integrality of the face sums -/

/-- The face sum `∑_{ω_i = 1} θ_ω` is `L_i`. -/
theorem sum_filter_eq_one_eq_cubeLi (θ : Cube → ℝ) (i : Fin 3) :
    ∑ ω ∈ univ.filter (fun ω : Cube => ω i = 1), θ ω = cubeLi θ i := by
  rw [sum_filter, cubeLi]
  refine sum_congr rfl fun ω _ => ?_
  rcases Fin.exists_fin_two.1 ⟨ω i, rfl⟩ with h | h <;> simp [h]

/-- The face sum `∑_{ω_i = 0} θ_ω` is `L_0 - L_i`. -/
theorem sum_filter_eq_zero_eq (θ : Cube → ℝ) (i : Fin 3) :
    ∑ ω ∈ univ.filter (fun ω : Cube => ω i = 0), θ ω = cubeL0 θ - cubeLi θ i := by
  rw [← sum_filter_eq_one_eq_cubeLi, cubeL0, ← sum_filter_add_sum_filter_not univ
    (fun ω : Cube => ω i = 1)]
  have : univ.filter (fun ω : Cube => ¬ ω i = 1) = univ.filter (fun ω : Cube => ω i = 0) := by
    ext ω
    rcases Fin.exists_fin_two.1 ⟨ω i, rfl⟩ with h | h <;> simp [h]
  rw [this]
  ring

/-- **Integrality of the six face sums** (Source: [F+] `cube-faces-linear-form-2`, L812–L817): if
`L_0, …, L_3` are integers, so is every signed face sum `∑_{ω_i = j} θ_ω`. -/
theorem isInt_faceSum_of_cubeDiag {θ : Cube → ℝ} (h : CubeDiag θ) (i : Fin 3) (j : Fin 2) :
    IsInt (∑ ω ∈ univ.filter (fun ω : Cube => ω i = j), θ ω) := by
  rcases Fin.exists_fin_two.1 ⟨j, rfl⟩ with rfl | rfl
  · rw [sum_filter_eq_zero_eq]
    exact h.1.sub (h.2 i)
  · rw [sum_filter_eq_one_eq_cubeLi]
    exact h.2 i

/-- The scaled face sums: integral `L_0, …, L_3` give `r ∣ ∑_{ω_i = j} (-1)^{|ω|} a_ω (r/q_ω)`
for `r = lcm(q_ω)`, the hypothesis `FaceIntegral` of the counting step. -/
theorem faceIntegral_of_cubeDiag {q a : Cube → ℕ} (hq : ∀ ω, q ω ≠ 0)
    (h : CubeDiag (cubeTheta q a)) : FaceIntegral q a := by
  intro i j
  obtain ⟨n, hn⟩ := isInt_faceSum_of_cubeDiag h i j
  refine ⟨n, ?_⟩
  have hr : ((cubeLcm q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast cubeLcm_ne_zero hq
  have hcast : ((faceSum (fun ω => (scaledNum q a ω : ℤ)) i j : ℤ) : ℝ) =
      (cubeLcm q : ℝ) * ∑ ω ∈ univ.filter (fun ω : Cube => ω i = j), cubeTheta q a ω := by
    unfold faceSum
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun ω _ => ?_
    have hqω : (q ω : ℝ) ≠ 0 := by exact_mod_cast hq ω
    simp only [scaledNum, cubeTheta]
    rw [Nat.cast_mul, Nat.cast_div (dvd_cubeLcm q ω) hqω]
    field_simp
  rw [hn] at hcast
  exact_mod_cast hcast

end PrimeCarleson.Proof.FplusProp21

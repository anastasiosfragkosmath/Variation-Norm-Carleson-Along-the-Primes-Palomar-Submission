/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/CorrelationDerivative.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.BigOperators.Fin
public import OAI.Combinatorics.Progressions.Estimates.WeightedSummandCorrelation
public import OAI.Combinatorics.Progressions.Probability.FiniteProbabilityLipschitz
@[expose] public section

namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

def multiplicativeDerivative (f : H → ℂ) (h : H) : H → ℂ :=
  fun x ↦ f x * star (f (x + h))

noncomputable def gowersMoment : ℕ → (H → ℂ) → ℂ
  | 0, f => 𝔼 x, f x
  | j + 1, f => 𝔼 h, gowersMoment j (multiplicativeDerivative f h)

omit [AddCommGroup H] in
theorem expect_star (f : H → ℂ) : (𝔼 x, star (f x)) = star (𝔼 x, f x) := by
  simp [Fintype.expect_eq_sum_div_card]

omit [AddCommGroup H] in
theorem expect_re (f : H → ℂ) : (𝔼 x, f x).re = 𝔼 x, (f x).re := by
  simp [Fintype.expect_eq_sum_div_card]

omit [AddCommGroup H] in
theorem expect_im (f : H → ℂ) : (𝔼 x, f x).im = 𝔼 x, (f x).im := by
  simp [Fintype.expect_eq_sum_div_card]

theorem expect_translate (f : H → ℂ) (x : H) : (𝔼 h, f (x + h)) = 𝔼 h, f h := by
  exact Fintype.expect_equiv (Equiv.addLeft x) _ f (fun _ ↦ rfl)

omit [Fintype H] in
theorem multiplicativeDerivative_comm (f : H → ℂ) (h k : H) :
    multiplicativeDerivative (multiplicativeDerivative f h) k =
      multiplicativeDerivative (multiplicativeDerivative f k) h := by
  funext x
  simp only [multiplicativeDerivative, star_mul, star_star]
  rw [show x + k + h = x + h + k by abel]
  ring

theorem gowersMoment_one (f : H → ℂ) :
    gowersMoment 1 f = (𝔼 x, f x) * star (𝔼 x, f x) := by
  change (𝔼 h, 𝔼 x, f x * star (f (x + h))) = _
  rw [Finset.expect_comm]
  calc
    (𝔼 x, 𝔼 h, f x * star (f (x + h))) =
        𝔼 x, f x * star (𝔼 h, f h) := by
      apply Finset.expect_congr rfl
      intro x hx
      rw [← Finset.mul_expect, expect_translate (fun h ↦ star (f h)), expect_star]
    _ = _ := (Finset.expect_mul _ _ _).symm

theorem gowersMoment_re_nonneg (j : ℕ) (f : H → ℂ) :
    0 ≤ (gowersMoment (j + 1) f).re := by
  induction j generalizing f with
  | zero =>
    rw [gowersMoment_one]
    change 0 ≤ ((𝔼 x, f x) * starRingEnd ℂ (𝔼 x, f x)).re
    rw [Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  | succ j ih =>
    rw [gowersMoment, expect_re]
    exact Finset.expect_nonneg (fun h _ ↦ ih (multiplicativeDerivative f h))

theorem gowersMoment_im_zero (j : ℕ) (f : H → ℂ) :
    (gowersMoment (j + 1) f).im = 0 := by
  induction j generalizing f with
  | zero =>
    rw [gowersMoment_one]
    change ((𝔼 x, f x) * starRingEnd ℂ (𝔼 x, f x)).im = 0
    rw [Complex.mul_conj, Complex.ofReal_im]
  | succ j ih =>
    rw [gowersMoment, expect_im]
    exact Finset.expect_eq_zero (fun h _ ↦ ih (multiplicativeDerivative f h))

theorem gowersMoment_const_one (j : ℕ) : gowersMoment j (fun _ : H ↦ 1) = 1 := by
  induction j with
  | zero => simp [gowersMoment]
  | succ j ih =>
    change (𝔼 h : H, gowersMoment j (multiplicativeDerivative (fun _ : H ↦ 1) h)) = 1
    have hder (h : H) : multiplicativeDerivative (fun _ : H ↦ 1) h = (fun _ : H ↦ 1) := by
      funext x
      simp [multiplicativeDerivative]
    simp_rw [hder, ih]
    exact Fintype.expect_one (ι := H)

noncomputable def gowersNorm (j : ℕ) (f : H → ℂ) : ℝ :=
  (gowersMoment j f).re ^ (((2 ^ j : ℕ) : ℝ)⁻¹)

theorem gowersNorm_nonneg (j : ℕ) (f : H → ℂ) : 0 ≤ gowersNorm (j + 1) f :=
  Real.rpow_nonneg (gowersMoment_re_nonneg j f) _

theorem gowersNorm_pow (j : ℕ) (f : H → ℂ) :
    gowersNorm (j + 1) f ^ (2 ^ (j + 1)) = (gowersMoment (j + 1) f).re := by
  exact Real.rpow_inv_natCast_pow (n := 2 ^ (j + 1)) (gowersMoment_re_nonneg j f)
    (pow_ne_zero _ (by norm_num))

theorem gowersNorm_one (f : H → ℂ) : gowersNorm 1 f = ‖𝔼 x, f x‖ := by
  have hmoment : (gowersMoment 1 f).re = ‖𝔼 x, f x‖ ^ 2 := by
    rw [gowersMoment_one]
    change ((𝔼 x, f x) * starRingEnd ℂ (𝔼 x, f x)).re = _
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  unfold gowersNorm
  rw [hmoment]
  norm_num only [pow_one, Nat.cast_ofNat]
  simpa using Real.pow_rpow_inv_natCast (norm_nonneg (𝔼 x : H, f x))
    (by norm_num : (2 : ℕ) ≠ 0)

theorem gowersNorm_const_one (j : ℕ) : gowersNorm j (fun _ : H ↦ 1) = 1 := by
  simp [gowersNorm, gowersMoment_const_one]

theorem gowersNorm_derivative (j : ℕ) (f : H → ℂ) :
    gowersNorm (j + 2) f ^ (2 ^ (j + 2)) =
      𝔼 h, gowersNorm (j + 1) (multiplicativeDerivative f h) ^ (2 ^ (j + 1)) := by
  simp only [gowersNorm_pow]
  exact expect_re _

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

def conjugationPower : ℕ → (ℂ →+* ℂ)
  | 0 => RingHom.id ℂ
  | n + 1 => (starRingEnd ℂ).comp (conjugationPower n)

theorem conjugationPower_star (n : ℕ) (z : ℂ) :
    conjugationPower n (star z) = star (conjugationPower n z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change star (conjugationPower n (star z)) = star (star (conjugationPower n z))
    exact congrArg star ih

variable {H : Type*} [AddCommGroup H]

def cubeProduct (f : H → ℂ) (hs : List H) (x : H) : ℂ :=
  (hs.sublists'.map fun ks ↦ conjugationPower ks.length (f (x + ks.sum))).prod

@[simp] theorem cubeProduct_nil (f : H → ℂ) (x : H) : cubeProduct f [] x = f x := by
  simp [cubeProduct, conjugationPower]

theorem cubeProduct_cons (f : H → ℂ) (h : H) (hs : List H) (x : H) :
    cubeProduct f (h :: hs) x = cubeProduct f hs x * star (cubeProduct f hs (x + h)) := by
  simp only [cubeProduct, List.sublists'_cons, List.map_append, List.prod_append,
    List.map_map, Function.comp_def, List.length_cons, List.sum_cons,
    conjugationPower, RingHom.comp_apply]
  congr 1
  change _ = (starRingEnd ℂ) _
  rw [map_list_prod, List.map_map]
  simp only [Function.comp_def, add_assoc]

theorem cubeProduct_derivative (f : H → ℂ) (h : H) (hs : List H) (x : H) :
    cubeProduct (multiplicativeDerivative f h) hs x =
      cubeProduct f hs x * star (cubeProduct f hs (x + h)) := by
  induction hs generalizing x with
  | nil => simp [multiplicativeDerivative]
  | cons k hs ih =>
    simp only [cubeProduct_cons, ih, star_mul, star_star]
    rw [show x + k + h = x + h + k by abel]
    ring

theorem cubeProduct_cons_eq_derivative (f : H → ℂ) (h : H) (hs : List H) (x : H) :
    cubeProduct f (h :: hs) x = cubeProduct (multiplicativeDerivative f h) hs x := by
  rw [cubeProduct_cons, cubeProduct_derivative]

variable [Fintype H]

noncomputable def cubeAverage {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M] :
    ℕ → (List H → M) → M
  | 0, F => F []
  | j + 1, F => 𝔼 h, cubeAverage j (fun hs ↦ F (h :: hs))

omit [AddCommGroup H] in

theorem cubeAverage_eq_expect_tuple {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (j : ℕ) (F : List H → M) :
    cubeAverage j F = 𝔼 h : Fin j → H, F (List.ofFn h) := by
  induction j generalizing F with
  | zero => simp [cubeAverage]
  | succ j ih =>
    rw [cubeAverage, expect_fin_cons]
    apply Finset.expect_congr rfl
    intro h hh
    rw [ih]
    apply Finset.expect_congr rfl
    intro hs hhs
    simp

omit [AddCommGroup H] in
theorem cubeAverage_re (j : ℕ) (F : List H → ℂ) :
    (cubeAverage j F).re = cubeAverage j (fun hs ↦ (F hs).re) := by
  simp only [cubeAverage_eq_expect_tuple, expect_re]

omit [AddCommGroup H] in
theorem cubeAverage_comm_expect {Ω : Type*} [Fintype Ω]
    {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M] (j : ℕ) (F : List H → Ω → M) :
    cubeAverage j (fun hs ↦ 𝔼 x, F hs x) = 𝔼 x, cubeAverage j (fun hs ↦ F hs x) := by
  simp only [cubeAverage_eq_expect_tuple]
  exact Finset.expect_comm _ _ _

omit [AddCommGroup H] in
theorem cubeAverage_norm_inner_sq_le (j : ℕ) (F G : List H → ℂ) :
    ‖cubeAverage j (fun hs ↦ F hs * star (G hs))‖ ^ 2 ≤
      cubeAverage j (fun hs ↦ ‖F hs‖ ^ 2) * cubeAverage j (fun hs ↦ ‖G hs‖ ^ 2) := by
  simp only [cubeAverage_eq_expect_tuple]
  exact norm_expect_mul_star_sq_le _ _

theorem gowersMoment_eq_cubeAverage (j : ℕ) (f : H → ℂ) :
    gowersMoment j f = cubeAverage j (fun hs ↦ 𝔼 x, cubeProduct f hs x) := by
  induction j generalizing f with
  | zero => simp [gowersMoment, cubeAverage]
  | succ j ih =>
    simp only [gowersMoment, cubeAverage, ih, cubeProduct_cons_eq_derivative]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {Ω H : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

variable [Fintype H]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

def crossDerivative (f g : H → ℂ) (h : H) : H → ℂ :=
  fun x ↦ f x * star (g (x + h))

omit [Fintype H] in
@[simp] theorem crossDerivative_self (f : H → ℂ) (h : H) :
    crossDerivative f f h = multiplicativeDerivative f h := rfl

omit [Fintype H] in
theorem cubeProduct_crossDerivative (f g : H → ℂ) (h : H) (hs : List H) (x : H) :
    cubeProduct (crossDerivative f g h) hs x =
      cubeProduct f hs x * star (cubeProduct g hs (x + h)) := by
  induction hs generalizing x with
  | nil => simp [crossDerivative]
  | cons k hs ih =>
    simp only [cubeProduct_cons, ih, star_mul, star_star]
    rw [show x + k + h = x + h + k by abel]
    ring

theorem expect_crossDerivative (f g : H → ℂ) :
    (𝔼 h, 𝔼 x, crossDerivative f g h x) = (𝔼 x, f x) * star (𝔼 x, g x) := by
  change (𝔼 h, 𝔼 x, f x * star (g (x + h))) = _
  rw [Finset.expect_comm]
  calc
    (𝔼 x, 𝔼 h, f x * star (g (x + h))) = 𝔼 x, f x * star (𝔼 y, g y) := by
      apply Finset.expect_congr rfl
      intro x hx
      rw [← Finset.mul_expect, expect_translate (fun y ↦ star (g y)), expect_star]
    _ = _ := (Finset.expect_mul _ _ _).symm

theorem expect_gowersMoment_crossDerivative (j : ℕ) (f g : H → ℂ) :
    (𝔼 h, gowersMoment j (crossDerivative f g h)) =
      cubeAverage j (fun hs ↦ (𝔼 x, cubeProduct f hs x) * star (𝔼 x, cubeProduct g hs x)) := by
  simp only [gowersMoment_eq_cubeAverage]
  rw [← cubeAverage_comm_expect]
  simp_rw [cubeProduct_crossDerivative]
  have hpoint : ∀ hs : List H,
      (𝔼 h, 𝔼 x, cubeProduct f hs x * star (cubeProduct g hs (x + h))) =
        (𝔼 x, cubeProduct f hs x) * star (𝔼 x, cubeProduct g hs x) := by
    intro hs
    exact expect_crossDerivative (cubeProduct f hs) (cubeProduct g hs)
  simp_rw [hpoint]

theorem mul_star_re_eq_norm_sq (z : ℂ) : (z * star z).re = ‖z‖ ^ 2 := by
  change (z * (starRingEnd ℂ) z).re = ‖z‖ ^ 2
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem gowersMoment_eq_average_square (j : ℕ) (f : H → ℂ) :
    (gowersMoment (j + 1) f).re =
      cubeAverage j (fun hs ↦ ‖𝔼 x, cubeProduct f hs x‖ ^ 2) := by
  have h := congrArg Complex.re (expect_gowersMoment_crossDerivative j f f)
  change (𝔼 h, gowersMoment j (multiplicativeDerivative f h)).re = _
  simpa only [crossDerivative_self, cubeAverage_re,
    mul_star_re_eq_norm_sq] using h

theorem norm_expect_gowersMoment_crossDerivative_sq_le (j : ℕ) (f g : H → ℂ) :
    ‖𝔼 h, gowersMoment j (crossDerivative f g h)‖ ^ 2 ≤
      (gowersMoment (j + 1) f).re * (gowersMoment (j + 1) g).re := by
  rw [expect_gowersMoment_crossDerivative,
    gowersMoment_eq_average_square, gowersMoment_eq_average_square]
  exact cubeAverage_norm_inner_sq_le j _ _

theorem expect_cross_gowersNorm_pow_le (j : ℕ) (f g : H → ℂ) :
    (𝔼 h, gowersNorm (j + 1) (crossDerivative f g h) ^ (2 ^ (j + 1))) ≤
      (gowersNorm (j + 2) f * gowersNorm (j + 2) g) ^ (2 ^ (j + 1)) := by
  let A := 𝔼 h, gowersNorm (j + 1) (crossDerivative f g h) ^ (2 ^ (j + 1))
  let B := (gowersNorm (j + 2) f * gowersNorm (j + 2) g) ^ (2 ^ (j + 1))
  have hA : 0 ≤ A := Finset.expect_nonneg (fun h _ ↦
    pow_nonneg (gowersNorm_nonneg j _) _)
  have hB : 0 ≤ B := pow_nonneg
    (mul_nonneg (gowersNorm_nonneg (j + 1) f) (gowersNorm_nonneg (j + 1) g)) _
  have hnorm : A ≤ ‖𝔼 h, gowersMoment (j + 1) (crossDerivative f g h)‖ := by
    dsimp [A]
    simp only [gowersNorm_pow, ← expect_re]
    exact Complex.re_le_norm _
  have hpower : (gowersMoment (j + 2) f).re * (gowersMoment (j + 2) g).re = B ^ 2 := by
    dsimp [B]
    rw [← gowersNorm_pow, ← gowersNorm_pow, ← mul_pow, ← pow_mul]
    congr 1
  have hsq : A ^ 2 ≤ B ^ 2 := (pow_le_pow_left₀ hA hnorm 2).trans
    ((norm_expect_gowersMoment_crossDerivative_sq_le (j + 1) f g).trans_eq hpower)
  change A ≤ B
  nlinarith

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] {Ω : J → Type*} [∀ j, Fintype (Ω j)]

end Erdos3.FiniteProbabilityWeights

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem correlation_sq_eq_expect_derivative (f u : H → ℂ) :
    ‖finiteCorrelation Finset.univ f u‖ ^ 2 =
      𝔼 h, (finiteCorrelation Finset.univ
        (multiplicativeDerivative f h) (multiplicativeDerivative u h)).re := by
  calc
    _ = (gowersMoment 1 (fun x => f x * star (u x))).re := by
      rw [gowersMoment_one, mul_star_re_eq_norm_sq]
      rfl
    _ = _ := by
      rw [gowersMoment, expect_re]
      apply Finset.expect_congr rfl
      intro h _
      congr 1
      change (𝔼 x, multiplicativeDerivative (fun x => f x * star (u x)) h x) = _
      apply Finset.expect_congr rfl
      intro x _
      simp only [multiplicativeDerivative, star_mul, star_star]
      ring

theorem correlation_sq_le_expect_norm_derivative (f u : H → ℂ) :
    ‖finiteCorrelation Finset.univ f u‖ ^ 2 ≤
      𝔼 h, ‖finiteCorrelation Finset.univ
        (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ := by
  rw [correlation_sq_eq_expect_derivative]
  exact Finset.expect_le_expect (fun _ _ => Complex.re_le_norm _)

theorem norm_derivativeCorrelation_le (f u : H → ℂ) {B : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ 1) (hu : ∀ x, ‖u x‖ ≤ B) (h : H) :
    ‖finiteCorrelation Finset.univ
      (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ ≤ B ^ 2 := by
  apply norm_finiteCorrelation_le Finset.univ_nonempty
  · intro x _
    simpa only [multiplicativeDerivative, norm_mul, norm_star, one_mul] using
      mul_le_mul (hf x) (hf (x + h)) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  · intro x _
    have hB : 0 ≤ B := (norm_nonneg (u x)).trans (hu x)
    simpa only [multiplicativeDerivative, norm_mul, norm_star, pow_two] using
      mul_le_mul (hu x) (hu (x + h)) (norm_nonneg _) hB

end Erdos3

end

end OAI

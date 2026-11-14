/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/IntegerPolynomialCongruence.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Tactic
@[expose] public section

namespace OAI

section

namespace Erdos3

open MvPolynomial

theorem integer_polynomial_sub_dvd {σ : Type*} (P : MvPolynomial σ ℤ)
    (x y : σ → ℤ) (m : ℤ) (hxy : ∀ i, m ∣ x i - y i) :
    m ∣ eval x P - eval y P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
    rw [eval_add, eval_add, add_sub_add_comm]
    exact dvd_add hP hQ
  | mul_X P i hP =>
    rw [eval_mul, eval_mul, eval_X, eval_X]
    have heq : eval x P * x i - eval y P * y i =
        (eval x P - eval y P) * x i + eval y P * (x i - y i) := by ring
    rw [heq]
    exact dvd_add (dvd_mul_of_dvd_left hP _) (dvd_mul_of_dvd_right (hxy i) _)

end Erdos3

end

end OAI

module

public import PrimeCarleson.Frozen.BlockWeight
public import PrimeCarleson.Proof.Goal0.Ramanujan
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Data.Nat.Totient
public import Mathlib.Algebra.Squarefree.Basic

/-!
# The Type I representation of the Heath-Brown approximant

Source: [KMTT] `hb-def`, L750–L757; `bounds`, L865–L866; `lhb`, L853–L856 (arXiv:2409.10510v2,
[KMTT] TeX; proof L874–L880):

* `hbIndex Q = {q : ℕ | 1 ≤ q < Q}`, so `Λ_{HB,Q} = blockWeight (hbIndex Q)` (the
  `PrimeCarleson.blockWeight`; KMTT's `c_q` is the `ramanujanSum`);
* `truncDivisor n Q = #{ℓ ∣ n : ℓ < Q}` (the truncated divisor function `τ(n, Q)`);
* `typeIWeight Q ℓ = (μ(ℓ) ℓ / φ(ℓ)) ∑_{r < Q/ℓ, (ℓ, r) = 1} μ²(r) / φ(r)` (the weights `λ_ℓ`);
* `blockWeight_hbIndex_eq`: `Λ_{HB,Q}(n) = ∑_{ℓ ∣ n, ℓ < Q} λ_ℓ` for every integer `n ≥ 1`
  (`c_q(n) = ∑_{ℓ ∣ (q, n)} ℓ μ(q / ℓ)`, write `q = ℓ r`, and
  `μ(ℓ r) μ(r) = μ(ℓ) μ²(r) 1_{(ℓ, r) = 1}`, `φ(ℓ r) = φ(ℓ) φ(r)` for `(ℓ, r) = 1`).
-/

@[expose] public noncomputable section

open PrimeCarleson ArithmeticFunction
open scoped ArithmeticFunction.Moebius

set_option autoImplicit false

namespace PrimeCarleson.Proof.KMTT

/-- The index set `{q ∈ ℕ : 1 ≤ q < Q}` of KMTT's Heath-Brown approximant
`Λ_{HB,Q}(n) = ∑_{1 ≤ q < Q} μ(q)/φ(q) c_q(n)` (KMTT L750-L757, `hb-def`):
`Λ_{HB,Q} = blockWeight (hbIndex Q)`. -/
def hbIndex (Q : ℝ) : Finset ℕ := Finset.Ico 1 ⌈Q⌉₊

/-- Membership in `hbIndex Q`: `1 ≤ q < Q`. -/
theorem mem_hbIndex {Q : ℝ} {q : ℕ} : q ∈ hbIndex Q ↔ 1 ≤ q ∧ (q : ℝ) < Q := by
  unfold hbIndex
  rw [Finset.mem_Ico, Nat.lt_ceil]

/-- The truncated divisor function `τ(n, Q) = #{ℓ : ℓ ∣ n, ℓ < Q}` (KMTT L865-L866). -/
def truncDivisor (n : ℕ) (Q : ℝ) : ℕ := (n.divisors.filter fun ℓ : ℕ => (ℓ : ℝ) < Q).card

/-- The Type I weights `λ_ℓ = (μ(ℓ) ℓ / φ(ℓ)) ∑_{r < Q/ℓ, (ℓ, r) = 1} μ²(r) / φ(r)`
(KMTT L879-L880). -/
def typeIWeight (Q : ℝ) (ℓ : ℕ) : ℝ :=
  (μ ℓ : ℝ) * ℓ / (Nat.totient ℓ : ℝ) *
    ∑ r ∈ (Finset.Icc 1 ⌈Q⌉₊).filter (fun r : ℕ => Nat.Coprime ℓ r ∧ (r : ℝ) < Q / ℓ),
      (μ r : ℝ) ^ 2 / (Nat.totient r : ℝ)

/-- Reindexing the multiples `q = f r` of `f` below `Q`. -/
theorem sum_hbIndex_multiples (Q : ℝ) {f : ℕ} (hf : 0 < f) {M : Type*} [AddCommMonoid M]
    (G : ℕ → M) :
    ∑ q ∈ (hbIndex Q).filter (fun q : ℕ => f ∣ q), G q =
      ∑ r ∈ (Finset.Icc 1 ⌈Q⌉₊).filter (fun r : ℕ => (r : ℝ) < Q / f), G (f * r) := by
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have himg : (hbIndex Q).filter (fun q : ℕ => f ∣ q) =
      ((Finset.Icc 1 ⌈Q⌉₊).filter (fun r : ℕ => (r : ℝ) < Q / f)).image (fun r => f * r) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_image, mem_hbIndex, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hq1, hqQ⟩, r, rfl⟩
      have hr1 : 1 ≤ r := by
        rcases Nat.eq_zero_or_pos r with h | h
        · subst h; simp at hq1
        · exact h
      push_cast at hqQ
      have hrfr : (r : ℝ) ≤ f * r := by nlinarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
      have hrc : r ≤ ⌈Q⌉₊ := by
        have : (r : ℝ) ≤ ⌈Q⌉₊ := (hrfr.trans_lt hqQ).le.trans (Nat.le_ceil Q)
        exact_mod_cast this
      refine ⟨r, ⟨⟨hr1, hrc⟩, ?_⟩, rfl⟩
      · rw [lt_div_iff₀ hf']; linarith
    · rintro ⟨r, ⟨⟨hr1, hr2⟩, hrQ⟩, rfl⟩
      rw [lt_div_iff₀ hf'] at hrQ
      refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
      · exact Nat.mul_pos hf hr1
      · push_cast; linarith
  rw [himg, Finset.sum_image]
  intro a _ b _ h
  exact Nat.eq_of_mul_eq_mul_left hf h

/-- The summand after `q = ℓ r`:
`μ(ℓ r)/φ(ℓ r) · ℓ μ(r) = 1_{(ℓ,r)=1} (μ(ℓ) ℓ/φ(ℓ)) (μ²(r)/φ(r))`. -/
theorem moebius_totient_term {f r : ℕ} (hf : 0 < f) (hr : 0 < r) :
    (μ (f * r) : ℝ) / (Nat.totient (f * r) : ℝ) * ((f : ℝ) * (μ r : ℝ)) =
      if Nat.Coprime f r then
        (μ f : ℝ) * f / (Nat.totient f : ℝ) * ((μ r : ℝ) ^ 2 / (Nat.totient r : ℝ)) else 0 := by
  split_ifs with h
  · have h1 : (μ (f * r) : ℝ) = (μ f : ℝ) * (μ r : ℝ) := by
      have := isMultiplicative_moebius.map_mul_of_coprime h
      exact_mod_cast this
    have h2 : (Nat.totient (f * r) : ℝ) = (Nat.totient f : ℝ) * (Nat.totient r : ℝ) := by
      exact_mod_cast Nat.totient_mul h
    have hf0 : (Nat.totient f : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hf).ne'
    have hr0 : (Nat.totient r : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hr).ne'
    rw [h1, h2]
    field_simp
  · have : ¬ Squarefree (f * r) := fun hsq => h (Nat.squarefree_mul_iff.mp hsq).1
    rw [moebius_eq_zero_of_not_squarefree this]
    simp

/-- Real form of the Type I identity: `∑_{q < Q} μ(q)/φ(q) ∑_{ℓ ∣ (q, n)} ℓ μ(q/ℓ)
  = ∑_{ℓ ∣ n, ℓ < Q} λ_ℓ`. -/
theorem sum_hbIndex_divisors_eq (Q : ℝ) {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ hbIndex Q, ∑ f ∈ q.divisors.filter (fun f : ℕ => f ∣ n),
        (μ q : ℝ) / (Nat.totient q : ℝ) * ((f : ℝ) * (μ (q / f) : ℝ)) =
      ∑ ℓ ∈ n.divisors.filter (fun l : ℕ => (l : ℝ) < Q), typeIWeight Q ℓ := by
  rw [Finset.sum_comm' (t' := n.divisors.filter (fun l : ℕ => (l : ℝ) < Q))
    (s' := fun f => (hbIndex Q).filter (fun q : ℕ => f ∣ q))]
  · refine Finset.sum_congr rfl fun f hf => ?_
    have hfpos : 0 < f := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hf).1
    rw [sum_hbIndex_multiples Q hfpos]
    have h1 : ∀ r ∈ (Finset.Icc 1 ⌈Q⌉₊).filter (fun r : ℕ => (r : ℝ) < Q / f),
        (μ (f * r) : ℝ) / (Nat.totient (f * r) : ℝ) * ((f : ℝ) * (μ (f * r / f) : ℝ)) =
          if Nat.Coprime f r then
            (μ f : ℝ) * f / (Nat.totient f : ℝ) * ((μ r : ℝ) ^ 2 / (Nat.totient r : ℝ))
          else 0 := by
      intro r hr
      have hr1 : 0 < r := by
        have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
        omega
      rw [Nat.mul_div_cancel_left _ hfpos]
      exact moebius_totient_term hfpos hr1
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, ← Finset.mul_sum, typeIWeight,
      Finset.filter_filter]
    congr 2
    ext r
    simp only [Finset.mem_filter]
    tauto
  · intro q f
    simp only [Finset.mem_filter, Nat.mem_divisors, mem_hbIndex]
    constructor
    · rintro ⟨⟨hq1, hqQ⟩, ⟨hfq, hq0⟩, hfn⟩
      refine ⟨⟨⟨hq1, hqQ⟩, hfq⟩, ⟨hfn, hn.ne'⟩, ?_⟩
      have : f ≤ q := Nat.le_of_dvd (by omega) hfq
      calc (f : ℝ) ≤ q := by exact_mod_cast this
        _ < Q := hqQ
    · rintro ⟨⟨⟨hq1, hqQ⟩, hfq⟩, ⟨hfn, -⟩, -⟩
      exact ⟨⟨hq1, hqQ⟩, ⟨hfq, by omega⟩, hfn⟩

/-- The Type I representation (KMTT `lhb`): `Λ_{HB,Q}(n) = ∑_{ℓ ∣ n, ℓ < Q} λ_ℓ` for `n ≥ 1`. -/
theorem blockWeight_hbIndex_eq (Q : ℝ) {n : ℕ} (hn : 0 < n) :
    blockWeight (hbIndex Q) (n : ℤ) =
      ∑ ℓ ∈ n.divisors.filter (fun l : ℕ => (l : ℝ) < Q), (typeIWeight Q ℓ : ℂ) := by
  have h1 : ∀ q ∈ hbIndex Q, ((((μ q : ℤ) : ℝ) / (Nat.totient q : ℝ) : ℝ) : ℂ) *
        ramanujanSum q n =
      ((∑ f ∈ q.divisors.filter (fun f : ℕ => f ∣ n),
        (μ q : ℝ) / (Nat.totient q : ℝ) * ((f : ℝ) * (μ (q / f) : ℝ)) : ℝ) : ℂ) := by
    intro q _
    rw [Goal0.ramanujanSum_eq_sum_divisors]
    simp only [Int.natCast_dvd_natCast]
    push_cast
    rw [Finset.mul_sum]
  unfold blockWeight
  push_cast at h1 ⊢
  rw [Finset.sum_congr rfl h1]
  have := sum_hbIndex_divisors_eq Q hn
  exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this

end PrimeCarleson.Proof.KMTT

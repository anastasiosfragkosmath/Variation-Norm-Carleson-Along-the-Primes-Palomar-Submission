module

public import PrimeCarleson.Proof.Goal0.Greedy
public import PrimeCarleson.Proof.Goal0.Divisors
public import PrimeCarleson.Proof.Goal0.InverseMd
public import PrimeCarleson.Proof.Goal0.AtomBound

/-!
# The bound for one period

Proposition `p:goal0` (`sources/Variational_Carleson.tex` L2471–L2817; Source: main paper
`c:invMB`, L2457–L2466; main paper `p:goal0`, L2545–L2550), by the route formalized here: the
abstract energy decrement (`le_of_inverse_theorem`) applied in `EuclideanSpace ℂ (Fin N)`,
`N = lcm B`, to `S v = ‖M_B v‖`. Its inputs are

* subadditivity and homogeneity of `S` (`periodicBlockMax_add_le`, `periodicBlockMax_smul`);
* the trivial bound `S ≤ β ‖·‖` with `β = ∑_{q ∈ B} τ(q)/φ(q)`, from the pointwise bound of `M_B`
  by the `M_d` (`l2_periodicBlockMax_le_sum`) and `‖M_d f‖ ≤ ‖f‖` (`l2_fiberMax_le`);
* the inverse theorem: if `S v > X ‖v‖` and `β η ≤ X`, some `M_d` with `d ∣ q ∈ B` has
  `‖M_d v‖ ≥ η ‖v‖`, and the atom of `exists_atom_inner_eq` realises it;
* the bound `σ` for `M_B` on atoms (`l2_periodicBlockMax_atom_le`), which needs `(d, N/d) = 1`,
  true since `N` is squarefree.
-/

@[expose] public noncomputable section

open Finset
open scoped InnerProductSpace ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Goal0

/-- `‖M_B f‖ ≤ (X + σ √(3/η³)) ‖f‖` over one period, given `1/φ(q) ≤ M` on `B`, the atom bound
`τ(d) M ∑_{r ∣ d} τ(r) ≤ σ` for `d ∣ q ∈ B`, and `β η ≤ X` with `β = ∑_{q ∈ B} τ(q)/φ(q)`. -/
theorem l2_periodicBlockMax_le_of_bounds {B : Finset ℕ} (hBsq : ∀ q ∈ B, Squarefree q)
    (hB0 : ∀ q ∈ B, 0 < q) {X σ η M : ℝ} (hX : 0 ≤ X) (hσ0 : 0 ≤ σ) (hη : 0 < η)
    (hη1 : η ≤ 1) (hM0 : 0 ≤ M) (hM : ∀ q ∈ B, ((q.totient : ℝ))⁻¹ ≤ M)
    (hσ : ∀ q ∈ B, ∀ d ∈ q.divisors,
      d.divisors.card * M * ∑ r ∈ d.divisors, (r.divisors.card : ℝ) ≤ σ)
    (hβ : (∑ q ∈ B, ((q.totient : ℝ))⁻¹ * q.divisors.card) * η ≤ X)
    {f : ℤ → ℂ} (hf : Function.Periodic f ((B.lcm id : ℕ) : ℤ)) :
    l2 (B.lcm id) (periodicBlockMax B f) ≤
      (X + σ * √(3 / η ^ 3)) * l2 (B.lcm id) (fun x => ‖f x‖) := by
  obtain ⟨N, hNdef⟩ : ∃ N, N = B.lcm id := ⟨_, rfl⟩
  rw [← hNdef] at hf ⊢
  have hNpos : 0 < N := by
    rw [hNdef]
    refine Nat.pos_of_ne_zero fun h0 => ?_
    obtain ⟨q, hq, hq0⟩ := Finset.lcm_eq_zero_iff.1 h0
    exact (hB0 q hq).ne' hq0
  have : NeZero N := ⟨hNpos.ne'⟩
  have hqN : ∀ q ∈ B, q ∣ N := fun q hq => hNdef ▸ Finset.dvd_lcm hq
  have hNsq : Squarefree N := hNdef ▸ squarefree_lcm_of_forall hBsq
  have hdN : ∀ q ∈ B, ∀ d ∈ q.divisors, d ∣ N := fun q hq d hd =>
    (Nat.dvd_of_mem_divisors hd).trans (hqN q hq)
  -- the functional `S v = ‖M_B v‖` on one period
  let S : EuclideanSpace ℂ (Fin N) → ℝ := fun v => l2 N (periodicBlockMax B (toFun v))
  set β : ℝ := ∑ q ∈ B, ((q.totient : ℝ))⁻¹ * q.divisors.card with hβdef
  -- `S v ≤ β c` once every `‖M_d v‖ ≤ c`
  have hsum_le : ∀ (v : EuclideanSpace ℂ (Fin N)) (c : ℝ),
      (∀ q ∈ B, ∀ d ∈ q.divisors, l2 N (fiberMax N d (toFun v)) ≤ c) → S v ≤ β * c := by
    intro v c hc
    have h1 := l2_periodicBlockMax_le_sum hB0 (toFun v)
    rw [← hNdef] at h1
    refine h1.trans ?_
    rw [hβdef, sum_mul]
    refine sum_le_sum fun q hq => ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Nat.cast_nonneg _))
    calc ∑ d ∈ q.divisors, l2 N (fiberMax N d (toFun v)) ≤ ∑ _d ∈ q.divisors, c :=
          sum_le_sum fun d hd => hc q hq d hd
      _ = q.divisors.card * c := by rw [sum_const, nsmul_eq_mul]
  have hS0 : S 0 = 0 := by
    change l2 N (periodicBlockMax B (toFun 0)) = 0
    have : periodicBlockMax B (toFun (0 : EuclideanSpace ℂ (Fin N))) = fun _ => 0 := by
      funext x
      rw [toFun_zero, show (0 : ℤ → ℂ) = (0 : ℂ) • (0 : ℤ → ℂ) by simp,
        periodicBlockMax_smul, norm_zero, zero_mul]
    rw [this, l2_zero]
  have hadd : ∀ v w, S (v + w) ≤ S v + S w := by
    intro v w
    change l2 N (periodicBlockMax B (toFun (v + w))) ≤ _
    rw [toFun_add]
    calc l2 N (periodicBlockMax B (toFun v + toFun w))
        ≤ l2 N (fun x => periodicBlockMax B (toFun v) x + periodicBlockMax B (toFun w) x) :=
          l2_mono (periodicBlockMax_nonneg B _) (periodicBlockMax_add_le B _ _)
      _ ≤ S v + S w := l2_add_le N _ _
  have hsmul : ∀ (c : ℂ) v, S (c • v) ≤ ‖c‖ * S v := by
    intro c v
    change l2 N (periodicBlockMax B (toFun (c • v))) ≤ _
    rw [toFun_smul]
    have : periodicBlockMax B (c • toFun v) = fun x => ‖c‖ * periodicBlockMax B (toFun v) x :=
      funext (periodicBlockMax_smul B c _)
    rw [this, l2_const_mul N (norm_nonneg c)]
  have hfib : ∀ (v : EuclideanSpace ℂ (Fin N)), ∀ q ∈ B, ∀ d ∈ q.divisors,
      l2 N (fiberMax N d (toFun v)) ≤ ‖v‖ := by
    intro v q hq d hd
    rw [norm_eq_l2]
    exact l2_fiberMax_le (Nat.pos_of_mem_divisors hd) (hdN q hq d hd) (toFun_periodic v)
  have htriv : ∀ v, S v ≤ X / η * ‖v‖ := by
    intro v
    have hβX : β ≤ X / η := (le_div_iff₀ hη).2 hβ
    exact (hsum_le v ‖v‖ (hfib v)).trans (mul_le_mul_of_nonneg_right hβX (norm_nonneg v))
  have hinv : ∀ v, X * ‖v‖ < S v →
      ∃ Φ : EuclideanSpace ℂ (Fin N), ‖Φ‖ = 1 ∧ S Φ ≤ σ ∧ η * ‖v‖ ≤ ‖⟪Φ, v⟫_ℂ‖ := by
    intro v hv
    have hv0 : 0 < ‖v‖ := by
      refine (norm_nonneg v).lt_of_ne fun h0 => ?_
      rw [← h0, mul_zero, norm_eq_zero.1 h0.symm, hS0] at hv
      exact lt_irrefl 0 hv
    obtain ⟨q, hq, d, hd, hηd⟩ : ∃ q ∈ B, ∃ d ∈ q.divisors,
        η * ‖v‖ ≤ l2 N (fiberMax N d (toFun v)) := by
      by_contra hcon
      push Not at hcon
      have h1 := hsum_le v (η * ‖v‖) fun q hq d hd => (hcon q hq d hd).le
      have h2 : β * (η * ‖v‖) ≤ X * ‖v‖ := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hβ (norm_nonneg v)
      linarith
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hdN' := hdN q hq d hd
    have hpos : 0 < l2 N (fiberMax N d (toFun v)) := lt_of_lt_of_le (mul_pos hη hv0) hηd
    obtain ⟨h, ϑ, hnorm1, hinner⟩ := exists_atom_inner_eq hd0 hdN' (toFun_periodic v) hpos
    have hper := atom_periodic hdN' h ϑ
    refine ⟨ofFun (atom N d h ϑ), ?_, ?_, ?_⟩
    · rw [norm_eq_l2, toFun_ofFun hper, hnorm1]
    · change l2 N (periodicBlockMax B (toFun (ofFun (atom N d h ϑ)))) ≤ σ
      rw [toFun_ofFun hper]
      have hcop : d.Coprime (N / d) := coprime_div_of_squarefree hNsq hdN'
      have key := l2_periodicBlockMax_atom_le hB0 hd0 (hNdef ▸ hdN') (hNdef ▸ hcop) hM0 hM h ϑ
      rw [← hNdef, hnorm1, mul_one] at key
      exact key.trans (hσ q hq d hd)
    · rw [inner_eq_sum, toFun_ofFun hper, hinner, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (l2_nonneg _ _)]
      exact hηd
  have key := le_of_inverse_theorem S hX hσ0 hη hη1 hadd hsmul htriv hinv (ofFun (N := N) f)
  have hS : S (ofFun (N := N) f) = l2 N (periodicBlockMax B f) := by
    change l2 N (periodicBlockMax B (toFun (ofFun f))) = _
    rw [toFun_ofFun hf]
  rwa [hS, norm_eq_l2, toFun_ofFun hf] at key

end PrimeCarleson.Proof.Goal0

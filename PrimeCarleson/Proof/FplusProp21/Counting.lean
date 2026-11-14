module

public import PrimeCarleson.Proof.FplusProp21.Cube
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.ModEq

/-!
# Counting the numerators: the per-prime count and the Chinese remainder theorem

The counting estimate `(counting-possible-numerators)` of [F+] Proposition 2.1
([F+] TeX L794–L839 and L1046–L1049). The steps, with their
sources:

* [F+] L833–L839, clause (i) (`card_eq_zero_or_four_le_of_mem_faceSol`): the support `S_p` of a
  solution of the six face congruences mod `p` is empty or has at least four vertices;
* [F+] L1048–L1049 (`card_faceSol_le`): the number of residue tuples in `{1, …, p-1}^{S}` (zero off
  `S`) solving the face congruences is `0` if `1 ≤ |S| ≤ 3`, at most `p - 1` if `|S| = 4` and at
  most `(p-1)^{|S|-4}` if `|S| ≥ 5`; the values on the set `T` of Lemma `l:algorithm` determine the
  solution (`eq_of_mem_faceSol_of_eqOn`, the propagation algorithm of [F+] L914–L932);
* [F+] `cube-faces-linear-form-3`, L818–L827, and the Chinese remainder theorem
  (`card_filter_numerators_le`): for squarefree `q_ω` with `r = lcm(q_ω)`, the numerator tuples
  `(a_ω)` whose signed face sums `∑ ± a_ω / q_ω` are integers inject, through
  `a_ω ↦ a_ω (r / q_ω) mod p`, into the product over `p ∣ r` of the per-prime solution sets with
  support `S_p = {ω : p ∣ q_ω}`;
* [F+] `counting-possible-numerators`, L804–L809 (`card_filter_numerators_le_prod`): the number
  `Δ_q` of such numerator tuples is at most `∏_{p ∣ r} N(|S_p|, p)` with `N(n, p) = 0` for `n ≤ 3`,
  `p - 1` for `n = 4` and `(p-1)^{n-4}` for `n ≥ 5` (`|S_p| = v_p(∏ q_ω)` for squarefree `q_ω`).

The face congruences are written in the integer form `r ∣ ∑_{ω_i = j} (-1)^{|ω|} a_ω (r/q_ω)`
(the face sums of `a_ω / q_ω` times `r`); the passage from the linear forms `L_0, …, L_3` to
these six face sums is in `PrimeCarleson.Proof.FplusProp21.Expansion`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.FplusProp21

open Finset

/-- The signed face sum `∑_{ω_i = j} (-1)^{|ω|} b_ω`. -/
def faceSum (b : Cube → ℤ) (i : Fin 3) (j : Fin 2) : ℤ :=
  ∑ ω ∈ univ.filter (fun ω : Cube => ω i = j), cubeSign ω * b ω

/-- The residue tuples `b ∈ {0, …, p-1}^{Cube}`, nonzero exactly on `S`, solving the six face
congruences `p ∣ ∑_{ω_i = j} (-1)^{|ω|} b_ω` ([F+] (cube-faces-linear-form-3)). -/
def faceSol (p : ℕ) (S : Finset Cube) : Finset (Cube → ℕ) :=
  (Fintype.piFinset fun _ : Cube => range p).filter
    (fun b => (∀ ω, b ω ≠ 0 ↔ ω ∈ S) ∧ ∀ i j, (p : ℤ) ∣ faceSum (fun ω => (b ω : ℤ)) i j)

/-- The per-prime bound `N(n, p)`: `0` for `n ≤ 3`, `p - 1` for `n = 4`, `(p-1)^{n-4}` for
`n ≥ 5`. -/
def perPrimeBound (p n : ℕ) : ℕ := if n ≤ 3 then 0 else if n = 4 then p - 1 else (p - 1) ^ (n - 4)

/-- Membership in the per-prime solution set. -/
theorem mem_faceSol {p : ℕ} {S : Finset Cube} {b : Cube → ℕ} :
    b ∈ faceSol p S ↔ (∀ ω, b ω < p) ∧ (∀ ω, b ω ≠ 0 ↔ ω ∈ S) ∧
      ∀ i j, (p : ℤ) ∣ faceSum (fun ω => (b ω : ℤ)) i j := by
  simp [faceSol, Fintype.mem_piFinset]

/-- Dividing a signed term: `p ∣ ±x → p ∣ x`. -/
theorem dvd_of_dvd_cubeSign_mul {p x : ℤ} (ω : Cube) (h : p ∣ cubeSign ω * x) : p ∣ x := by
  rcases cubeSign_eq_one_or ω with hs | hs
  · simpa [hs] using h
  · simpa [hs] using h

/-- Two residues `< p` congruent mod `p` are equal. -/
theorem eq_of_lt_of_dvd_sub {p x y : ℕ} (hx : x < p) (hy : y < p) (h : (p : ℤ) ∣ (x : ℤ) - y) :
    x = y := by
  have h0 := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
  omega

/-- **Marking argument, per prime** (Source: [F+] L833–L836, clause (i)): the support of a solution
of the face congruences mod `p` meets every face in `0` or at least `2` vertices, hence is empty or
has at least four vertices. -/
theorem card_eq_zero_or_four_le_of_mem_faceSol {p : ℕ} {S : Finset Cube} {b : Cube → ℕ}
    (hb : b ∈ faceSol p S) : S.card = 0 ∨ 4 ≤ S.card := by
  classical
  rw [mem_faceSol] at hb
  obtain ⟨hlt, hsupp, hface⟩ := hb
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨i, j, hij⟩ := exists_card_filter_eq_one S (by omega) (by omega)
  obtain ⟨ω, hω⟩ := Finset.card_eq_one.1 hij
  have hωmem : ω ∈ S.filter (fun ν => ν i = j) := by rw [hω]; exact mem_singleton_self ω
  rw [mem_filter] at hωmem
  have hsum : faceSum (fun ν => (b ν : ℤ)) i j = cubeSign ω * b ω := by
    unfold faceSum
    refine sum_eq_single_of_mem ω (mem_filter.2 ⟨mem_univ _, hωmem.2⟩) fun ν hν hνω => ?_
    have hνS : ν ∉ S := by
      intro hνS
      have : ν ∈ S.filter (fun ν => ν i = j) := mem_filter.2 ⟨hνS, (mem_filter.1 hν).2⟩
      rw [hω, mem_singleton] at this
      exact hνω this
    have : b ν = 0 := by
      by_contra h0
      exact hνS ((hsupp ν).1 h0)
    simp [this]
  have h1 := hface i j
  rw [hsum] at h1
  have h2 := dvd_of_dvd_cubeSign_mul ω h1
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le _) (hlt ω)
  have h3 : b ω = 0 := eq_of_lt_of_dvd_sub (hlt ω) hp (by simpa using h2)
  exact (hsupp ω).2 hωmem.1 h3

/-- **One round of propagation** (Source: [F+] L914–L932, the propagation algorithm): two solutions
agreeing on the green set `G` agree on the next green set. On a face through `ω` whose other marked
vertices are green, the face congruence determines `b_ω`. -/
theorem eqOn_propStep {p : ℕ} {S G : Finset Cube} {b b' : Cube → ℕ} (hb : b ∈ faceSol p S)
    (hb' : b' ∈ faceSol p S) (hG : ∀ ω ∈ G, b ω = b' ω) : ∀ ω ∈ propStep S G, b ω = b' ω := by
  classical
  rw [mem_faceSol] at hb hb'
  obtain ⟨hlt, hsupp, hface⟩ := hb
  obtain ⟨hlt', hsupp', hface'⟩ := hb'
  intro ω hω
  simp only [propStep, mem_union, mem_filter] at hω
  rcases hω with hω | ⟨hωS, i, hi⟩
  · exact hG ω hω
  have hd := dvd_sub (hface i (ω i)) (hface' i (ω i))
  have hsum : faceSum (fun ν => (b ν : ℤ)) i (ω i) - faceSum (fun ν => (b' ν : ℤ)) i (ω i) =
      cubeSign ω * ((b ω : ℤ) - b' ω) := by
    unfold faceSum
    rw [← sum_sub_distrib,
      sum_eq_single_of_mem (s := univ.filter (fun ν : Cube => ν i = ω i)) ω (by simp)]
    · ring
    intro ν hν hνω
    by_cases hνS : ν ∈ S
    · have : ν ∈ G := hi (mem_erase.2 ⟨hνω, mem_filter.2 ⟨hνS, (mem_filter.1 hν).2⟩⟩)
      simp [hG ν this]
    · have h0 : b ν = 0 := by
        by_contra h0
        exact hνS ((hsupp ν).1 h0)
      have h0' : b' ν = 0 := by
        by_contra h0
        exact hνS ((hsupp' ν).1 h0)
      simp [h0, h0']
  rw [hsum] at hd
  exact eq_of_lt_of_dvd_sub (hlt ω) (hlt' ω) (dvd_of_dvd_cubeSign_mul ω hd)

/-- Agreement propagates through any number of rounds. -/
theorem eqOn_iterate_propStep {p : ℕ} {S G : Finset Cube} {b b' : Cube → ℕ}
    (hb : b ∈ faceSol p S) (hb' : b' ∈ faceSol p S) (hG : ∀ ω ∈ G, b ω = b' ω) (n : ℕ) :
    ∀ ω ∈ (propStep S)^[n] G, b ω = b' ω := by
  induction n with
  | zero => exact hG
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact eqOn_propStep hb hb' ih

/-- If the algorithm colours `S` from `T`, a solution is determined by its values on `T`. -/
theorem eq_of_mem_faceSol_of_eqOn {p : ℕ} {S T : Finset Cube} (hST : S ⊆ propClosure S T)
    {b b' : Cube → ℕ} (hb : b ∈ faceSol p S) (hb' : b' ∈ faceSol p S)
    (hT : ∀ ω ∈ T, b ω = b' ω) : b = b' := by
  funext ω
  by_cases hω : ω ∈ S
  · exact eqOn_iterate_propStep hb hb' hT 4 ω (hST hω)
  · have h0 : b ω = 0 := by
      by_contra h0
      exact hω (((mem_faceSol.1 hb).2.1 ω).1 h0)
    have h0' : b' ω = 0 := by
      by_contra h0
      exact hω (((mem_faceSol.1 hb').2.1 ω).1 h0)
    rw [h0, h0']

/-- The count from a determining set: `#(solutions) ≤ (p-1)^{|T|}` when the algorithm colours
`S` from `T ⊆ S` ([F+] L1048-L1049). -/
theorem card_faceSol_le_pow {p : ℕ} {S T : Finset Cube} (hTS : T ⊆ S)
    (hST : S ⊆ propClosure S T) : (faceSol p S).card ≤ (p - 1) ^ T.card := by
  classical
  set target : Finset (Cube → ℕ) :=
    Fintype.piFinset fun ω => if ω ∈ T then Icc 1 (p - 1) else {0} with htarget
  have hmaps : Set.MapsTo (fun b : Cube → ℕ => fun ω => if ω ∈ T then b ω else 0)
      (faceSol p S : Set (Cube → ℕ)) (target : Set (Cube → ℕ)) := by
    intro b hb
    rw [mem_coe, mem_faceSol] at hb
    rw [mem_coe, htarget, Fintype.mem_piFinset]
    intro ω
    by_cases hω : ω ∈ T
    · simp only [hω, ite_true, mem_Icc]
      have h1 := hb.1 ω
      have h2 : b ω ≠ 0 := (hb.2.1 ω).2 (hTS hω)
      omega
    · simp [hω]
  have hinj : Set.InjOn (fun b : Cube → ℕ => fun ω => if ω ∈ T then b ω else 0)
      (faceSol p S : Set (Cube → ℕ)) := by
    intro b hb b' hb' hbb'
    refine eq_of_mem_faceSol_of_eqOn hST hb hb' fun ω hω => ?_
    have := congrFun hbb' ω
    simpa [hω] using this
  calc (faceSol p S).card ≤ target.card := card_le_card_of_injOn _ hmaps hinj
    _ = (p - 1) ^ T.card := by
      rw [htarget, Fintype.card_piFinset]
      have : ∀ ω : Cube, (if ω ∈ T then Icc 1 (p - 1) else ({0} : Finset ℕ)).card =
          if ω ∈ T then p - 1 else 1 := by
        intro ω
        split_ifs <;> simp
      simp_rw [this]
      rw [prod_ite_mem, univ_inter, prod_const]

/-- **Per-prime count** (Source: [F+] L1048–L1049): for a nonempty marked set `S`, the number of
residue tuples in `{1, …, p-1}^S` solving the six face congruences mod `p` is `0` if `|S| ≤ 3`, at
most `p - 1` if `|S| = 4` and at most `(p-1)^{|S|-4}` if `|S| ≥ 5`. -/
theorem card_faceSol_le {p : ℕ} {S : Finset Cube} (hS : S.Nonempty) :
    (faceSol p S).card ≤ perPrimeBound p S.card := by
  classical
  have hempty : (∀ b ∈ faceSol p S, False) → (faceSol p S).card ≤ perPrimeBound p S.card := by
    intro h
    have : faceSol p S = ∅ := eq_empty_iff_forall_notMem.2 h
    rw [this, card_empty]
    exact Nat.zero_le _
  rcases Nat.lt_or_ge p 2 with hp | hp
  · -- `p ≤ 1`: no residue is nonzero
    refine hempty fun b hb => ?_
    obtain ⟨ω, hω⟩ := hS
    rw [mem_faceSol] at hb
    have h1 := hb.1 ω
    have h2 := (hb.2.1 ω).2 hω
    omega
  rcases Nat.lt_or_ge S.card 4 with h4 | h4
  · -- no solution
    refine hempty fun b hb => ?_
    rcases card_eq_zero_or_four_le_of_mem_faceSol hb with h | h
    · exact hS.ne_empty (card_eq_zero.1 h)
    · omega
  · obtain ⟨T, hTS, hTc, hST⟩ := exists_subset_propClosure S h4
    refine (card_faceSol_le_pow hTS hST).trans ?_
    have hp1 : 0 < p - 1 := by omega
    have h3 : ¬ S.card ≤ 3 := by omega
    unfold perPrimeBound
    simp only [h3, ↓reduceIte]
    by_cases h : S.card = 4
    · simp only [h, ↓reduceIte] at hTc ⊢
      calc (p - 1) ^ T.card ≤ (p - 1) ^ 1 := Nat.pow_le_pow_right hp1 hTc
        _ = p - 1 := pow_one _
    · simp only [h, ↓reduceIte] at hTc ⊢
      exact Nat.pow_le_pow_right hp1 hTc

/-! ### The Chinese remainder theorem step -/

/-- The numerator tuples of a denominator tuple `q`: `1 ≤ a_ω ≤ q_ω` with `(a_ω, q_ω) = 1`. -/
def numerators (q : Cube → ℕ) : Finset (Cube → ℕ) :=
  Fintype.piFinset fun ω => (Icc 1 (q ω)).filter (fun a => Nat.Coprime a (q ω))

/-- `r = lcm_ω q_ω`. -/
def cubeLcm (q : Cube → ℕ) : ℕ := univ.lcm q

/-- The marked vertices `S_p = {ω : p ∣ q_ω}` of a prime `p`. -/
def primeSupport (q : Cube → ℕ) (p : ℕ) : Finset Cube := univ.filter (fun ω => p ∣ q ω)

/-- The scaled numerators `a_ω (r / q_ω)`, so that `a_ω / q_ω = a_ω (r / q_ω) / r`. -/
def scaledNum (q a : Cube → ℕ) (ω : Cube) : ℕ := a ω * (cubeLcm q / q ω)

/-- The six signed face sums of the fractions `a_ω / q_ω` are integers, written with the
common denominator `r = lcm(q_ω)` ([F+] (cube-faces-linear-form-2)). -/
def FaceIntegral (q a : Cube → ℕ) : Prop :=
  ∀ i j, (cubeLcm q : ℤ) ∣ faceSum (fun ω => (scaledNum q a ω : ℤ)) i j

/-- `FaceIntegral` is decidable (finitely many integer divisibilities). -/
instance (q a : Cube → ℕ) : Decidable (FaceIntegral q a) := by
  unfold FaceIntegral
  infer_instance

/-- Membership in the numerator tuples. -/
theorem mem_numerators {q a : Cube → ℕ} :
    a ∈ numerators q ↔ ∀ ω, 1 ≤ a ω ∧ a ω ≤ q ω ∧ Nat.Coprime (a ω) (q ω) := by
  simp [numerators, Fintype.mem_piFinset, and_assoc]

/-- `q_ω ∣ lcm(q)`. -/
theorem dvd_cubeLcm (q : Cube → ℕ) (ω : Cube) : q ω ∣ cubeLcm q :=
  Finset.dvd_lcm (mem_univ ω)

/-- `lcm(q) ≠ 0` for nonzero `q_ω`. -/
theorem cubeLcm_ne_zero {q : Cube → ℕ} (hq : ∀ ω, q ω ≠ 0) : cubeLcm q ≠ 0 := by
  rw [cubeLcm, Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨ω, -, h⟩
  exact hq ω h

/-- The lcm of squarefree numbers is squarefree. -/
theorem squarefree_cubeLcm {q : Cube → ℕ} (hq : ∀ ω, Squarefree (q ω)) :
    Squarefree (cubeLcm q) := by
  have hne : ∀ ω ∈ (univ : Finset Cube), q ω ≠ 0 := fun ω' _ => (hq ω').ne_zero
  rw [Nat.squarefree_iff_factorization_le_one (cubeLcm_ne_zero fun ω => (hq ω).ne_zero)]
  intro p
  rw [cubeLcm, Finset.factorization_lcm hne]
  exact Finset.sup_le fun ω' _ => (hq ω').natFactorization_le_one p

/-- `lcm(q) ∣ ∏ q_ω`. -/
theorem cubeLcm_dvd_prod (q : Cube → ℕ) : cubeLcm q ∣ ∏ ω, q ω :=
  Finset.lcm_dvd_iff.2 fun _ hω => dvd_prod_of_mem q hω

/-- Every prime factor of `r = lcm(q_ω)` divides some `q_ω`, so `S_p` is nonempty. -/
theorem primeSupport_nonempty {q : Cube → ℕ} {p : ℕ} (hp : p ∈ (cubeLcm q).primeFactors) :
    (primeSupport q p).Nonempty := by
  rw [Nat.mem_primeFactors] at hp
  obtain ⟨ω, -, h⟩ :=
    (Prime.dvd_finsetProd_iff hp.1.prime q).1 (hp.2.1.trans (cubeLcm_dvd_prod q))
  exact ⟨ω, mem_filter.2 ⟨mem_univ _, h⟩⟩

/-- For `p ∣ q_ω`, `p ∤ r / q_ω` (`r` is squarefree). -/
theorem not_dvd_cubeLcm_div {q : Cube → ℕ} (hq : ∀ ω, Squarefree (q ω)) {p : ℕ}
    (hp : p.Prime) {ω : Cube} (hpq : p ∣ q ω) : ¬ p ∣ cubeLcm q / q ω := by
  intro h
  have hsq := squarefree_cubeLcm hq
  have : p * p ∣ cubeLcm q := by
    rw [← Nat.mul_div_cancel' (dvd_cubeLcm q ω)]
    exact Nat.mul_dvd_mul hpq h
  exact (Nat.squarefree_iff_prime_squarefree.1 hsq) p hp this

/-- For `p ∣ r` and `p ∤ q_ω`, `p ∣ r / q_ω`. -/
theorem dvd_cubeLcm_div {q : Cube → ℕ} {p : ℕ} (hp : p.Prime) (hpr : p ∣ cubeLcm q) {ω : Cube}
    (hpq : ¬ p ∣ q ω) : p ∣ cubeLcm q / q ω := by
  rw [← Nat.mul_div_cancel' (dvd_cubeLcm q ω)] at hpr
  rcases (Nat.Prime.dvd_mul hp).1 hpr with h | h
  · exact absurd h hpq
  · exact h

/-- A face sum of reduced residues: `∑ ± (A_ω mod p) = ∑ ± A_ω - p ∑ ± ⌊A_ω / p⌋`. -/
theorem faceSum_mod (A : Cube → ℕ) (p : ℕ) (i : Fin 3) (j : Fin 2) :
    faceSum (fun ω => ((A ω % p : ℕ) : ℤ)) i j =
      faceSum (fun ω => (A ω : ℤ)) i j - p * faceSum (fun ω => ((A ω / p : ℕ) : ℤ)) i j := by
  unfold faceSum
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun ω _ => ?_
  dsimp only
  have h := Nat.mod_add_div (A ω) p
  have h' : ((A ω % p : ℕ) : ℤ) = (A ω : ℤ) - p * ((A ω / p : ℕ) : ℤ) := by
    have : ((A ω % p : ℕ) : ℤ) + p * ((A ω / p : ℕ) : ℤ) = (A ω : ℤ) := by exact_mod_cast h
    linarith
  rw [h']
  ring

/-- The residues `a_ω (r / q_ω) mod p` of an integral numerator tuple solve the face congruences
mod `p`, with support exactly `S_p` ([F+] (cube-faces-linear-form-3)). -/
theorem residues_mem_faceSol {q a : Cube → ℕ} (hq : ∀ ω, Squarefree (q ω))
    (ha : a ∈ numerators q) (hint : FaceIntegral q a) {p : ℕ}
    (hp : p ∈ (cubeLcm q).primeFactors) :
    (fun ω => scaledNum q a ω % p) ∈ faceSol p (primeSupport q p) := by
  rw [Nat.mem_primeFactors] at hp
  obtain ⟨hpp, hpr, -⟩ := hp
  rw [mem_numerators] at ha
  rw [mem_faceSol]
  refine ⟨fun ω => Nat.mod_lt _ hpp.pos, fun ω => ?_, fun i j => ?_⟩
  · simp only [primeSupport, mem_filter, mem_univ, true_and, ne_eq, ← Nat.dvd_iff_mod_eq_zero,
      scaledNum]
    constructor
    · intro h
      by_contra hpq
      exact h (Dvd.dvd.mul_left (dvd_cubeLcm_div hpp hpr hpq) _)
    · intro hpq h
      rcases (Nat.Prime.dvd_mul hpp).1 h with h1 | h1
      · have := Nat.Coprime.coprime_dvd_left h1 (ha ω).2.2
        exact hpp.ne_one (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm
          (Nat.Coprime.coprime_dvd_left hpq this.symm)) dvd_rfl)
      · exact not_dvd_cubeLcm_div hq hpp hpq h1
  · rw [faceSum_mod]
    refine dvd_sub ((Int.natCast_dvd_natCast.2 hpr).trans (hint i j)) (dvd_mul_right _ _)

/-- **Chinese remainder step** (Source: [F+] `cube-faces-linear-form-3`, L818–L827, and the Chinese
remainder theorem): for squarefree `q_ω`, the integral numerator tuples inject into the product over
the primes `p ∣ r` of the per-prime solution sets. -/
theorem card_filter_numerators_le (q : Cube → ℕ) (hq : ∀ ω, Squarefree (q ω)) :
    ((numerators q).filter (FaceIntegral q)).card ≤
      ∏ p ∈ (cubeLcm q).primeFactors, (faceSol p (primeSupport q p)).card := by
  classical
  rw [← card_pi]
  refine card_le_card_of_injOn
    (fun a : Cube → ℕ => fun p (_ : p ∈ (cubeLcm q).primeFactors) => fun ω => scaledNum q a ω % p)
    (fun a ha => ?_) (fun a ha a' ha' h => ?_)
  · rw [mem_coe, mem_filter] at ha
    rw [mem_coe, mem_pi]
    exact fun p hp => residues_mem_faceSol hq ha.1 ha.2 hp
  · rw [mem_coe, mem_filter, mem_numerators] at ha ha'
    funext ω
    obtain ⟨ha1, ha2, ha3⟩ := ha.1 ω
    obtain ⟨ha1', ha2', ha3'⟩ := ha'.1 ω
    have hqω : q ω ≠ 0 := (hq ω).ne_zero
    -- `p ∣ a'_ω - a_ω` for every prime `p ∣ q_ω`
    have hp : ∀ p ∈ (q ω).primeFactors, p ∣ ((a' ω : ℤ) - a ω).natAbs := by
      intro p hp
      have hp' := hp
      rw [Nat.mem_primeFactors] at hp'
      have hpr : p ∈ (cubeLcm q).primeFactors := by
        rw [Nat.mem_primeFactors]
        exact ⟨hp'.1, hp'.2.1.trans (dvd_cubeLcm q ω),
          cubeLcm_ne_zero fun ω => (hq ω).ne_zero⟩
      have h1 := congrFun (congrFun (congrFun h p) hpr) ω
      simp only [scaledNum] at h1
      have hcop : p.gcd (cubeLcm q / q ω) = 1 :=
        (Nat.Prime.coprime_iff_not_dvd hp'.1).2 (not_dvd_cubeLcm_div hq hp'.1 hp'.2.1)
      have h2 : Nat.ModEq p (a ω) (a' ω) := Nat.ModEq.cancel_right_of_coprime hcop h1
      exact Int.natCast_dvd.1 (Nat.modEq_iff_dvd.1 h2)
    have hq' : q ω ∣ ((a' ω : ℤ) - a ω).natAbs := by
      have := Finset.prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) hp
      rwa [Nat.prod_primeFactors_of_squarefree (hq ω)] at this
    have h0 := Int.eq_zero_of_abs_lt_dvd (Int.natCast_dvd.2 hq')
      (by rw [abs_lt]; constructor <;> omega)
    omega

/-- **Counting the numerators** (Source: [F+] `counting-possible-numerators`, L804–L809): for
squarefree `q_ω`, the number `Δ_q` of numerator tuples with integral face sums is at most
`∏_{p ∣ r} N(|S_p|, p)`, i.e. `0` if some `v_p(R) ≤ 3` and otherwise
`∏_{v_p(R) = 4} (p - 1) ∏_{v_p(R) ≥ 5} (p - 1)^{v_p(R) - 4}`, where `R = ∏ q_ω` and
`v_p(R) = |S_p|`. -/
theorem card_filter_numerators_le_prod (q : Cube → ℕ) (hq : ∀ ω, Squarefree (q ω)) :
    ((numerators q).filter (FaceIntegral q)).card ≤
      ∏ p ∈ (cubeLcm q).primeFactors, perPrimeBound p (primeSupport q p).card :=
  (card_filter_numerators_le q hq).trans
    (prod_le_prod fun _ hp => card_faceSol_le (primeSupport_nonempty hp))

end PrimeCarleson.Proof.FplusProp21

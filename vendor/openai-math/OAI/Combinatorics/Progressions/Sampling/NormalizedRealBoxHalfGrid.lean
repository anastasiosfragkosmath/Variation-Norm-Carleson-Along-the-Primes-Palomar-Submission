/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Sampling/NormalizedRealBoxHalfGrid.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
@[expose] public section

namespace OAI

section

namespace Erdos3

noncomputable def uniformIntervalGrid (B : ℝ) (N : ℕ) (k : Fin (N + 1)) : ℝ :=
  -B + (2 * B / N) * k

theorem uniformIntervalGrid_mem {B : ℝ} (hB : 0 ≤ B) {N : ℕ} (hN : 0 < N)
    (k : Fin (N + 1)) : |uniformIntervalGrid B N k| ≤ B := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : (k : ℝ) ≤ N := by exact_mod_cast Nat.le_of_lt_succ k.isLt
  have hstep : 0 ≤ 2 * B / N := by positivity
  have htop : (2 * B / N) * N = 2 * B := div_mul_cancel₀ _ hNr.ne'
  have hle := mul_le_mul_of_nonneg_left hk hstep
  apply abs_le.mpr
  dsimp [uniformIntervalGrid]
  constructor
  · have := mul_nonneg hstep (Nat.cast_nonneg k.val)
    linarith
  · linarith

theorem exists_uniformIntervalGrid_approx {B : ℝ} (hB : 0 < B) {N : ℕ} (hN : 0 < N)
    (x : ℝ) (hx : |x| ≤ B) :
    ∃ k : Fin (N + 1), |x - uniformIntervalGrid B N k| ≤ 2 * B / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let δ : ℝ := 2 * B / N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδN : δ * N = 2 * B := div_mul_cancel₀ _ hNr.ne'
  let q : ℝ := (x + B) / δ
  have hq0 : 0 ≤ q := div_nonneg (by linarith [(abs_le.mp hx).1]) hδ.le
  have hqN : q ≤ N := by
    apply (div_le_iff₀ hδ).mpr
    linarith [(abs_le.mp hx).2]
  let k : Fin (N + 1) := ⟨⌊q⌋₊, Nat.lt_succ_of_le (Nat.floor_le_of_le hqN)⟩
  refine ⟨k, ?_⟩
  have hq : δ * q = x + B := by dsimp [q]; field_simp
  have heq : x - uniformIntervalGrid B N k = δ * (q - ⌊q⌋₊) := by
    change x - (-B + δ * (⌊q⌋₊ : ℝ)) = _
    rw [mul_sub, hq]
    ring
  rw [heq, abs_mul, abs_of_pos hδ]
  exact (mul_le_mul_of_nonneg_left (Nat.abs_sub_floor_le hq0) hδ.le).trans_eq (mul_one δ)

noncomputable def uniformBoxGrid {ι : Type*} (B : ℝ) (N : ℕ) (k : ι → Fin (N + 1)) : ι → ℝ :=
  fun i => uniformIntervalGrid B N (k i)

theorem uniformBoxGrid_mem {ι : Type*} {B : ℝ} (hB : 0 ≤ B) {N : ℕ} (hN : 0 < N)
    (k : ι → Fin (N + 1)) (i : ι) : |uniformBoxGrid B N k i| ≤ B :=
  uniformIntervalGrid_mem hB hN (k i)

theorem exists_uniformBoxGrid_approx {ι : Type*} [Fintype ι] {B : ℝ} (hB : 0 < B)
    {N : ℕ} (hN : 0 < N) (v : ι → ℝ) (hv : ∀ i, |v i| ≤ B) :
    ∃ k : ι → Fin (N + 1), dist v (uniformBoxGrid B N k) ≤ 2 * B / N := by
  classical
  choose k hk using fun i => exists_uniformIntervalGrid_approx hB hN (v i) (hv i)
  refine ⟨k, ?_⟩
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ 2 * B / N)).mpr
  intro i
  simpa only [Real.dist_eq, uniformBoxGrid] using hk i

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

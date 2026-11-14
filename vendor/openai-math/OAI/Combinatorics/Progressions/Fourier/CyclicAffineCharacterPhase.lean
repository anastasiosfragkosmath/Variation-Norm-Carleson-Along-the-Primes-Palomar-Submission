/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Fourier/CyclicAffineCharacterPhase.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Fourier.ExponentialBohrVolume
public import OAI.Combinatorics.Progressions.Fourier.RectangularGridCharacter
public import OAI.Combinatorics.Progressions.Lattices.IntegerAffineSubstitution
@[expose] public section

namespace OAI

section

namespace Erdos3.CircleFourier

theorem exists_real_character_phase {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ r : ℝ, character (r : Circle) = z := by
  let c : _root_.Circle := ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩
  obtain ⟨t, ht⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective c
  rw [AddCircle.homeomorphCircle_apply] at ht
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  exact ⟨r, congrArg (fun c : _root_.Circle => (c : ℂ)) ht⟩

end Erdos3.CircleFourier

namespace Erdos3.CyclicBohr

variable {N : ℕ} [NeZero N]

theorem exists_real_frequency_phase (r : ZMod N) :
    ∃ theta : ℝ, ∀ x : ZMod N,
      CircleFourier.character (((x.val : ℝ) * theta : ℝ) : CircleFourier.Circle) = character r x := by
  obtain ⟨theta, htheta⟩ := CircleFourier.exists_real_character_phase (norm_character r 1)
  refine ⟨theta, ?_⟩
  intro x
  have hphase : (((x.val : ℝ) * theta : ℝ) : CircleFourier.Circle) =
      x.val • (theta : CircleFourier.Circle) := by
    simpa only [nsmul_eq_mul] using
      (AddCircle.coe_nsmul (p := (1 : ℝ)) (n := x.val) (x := theta))
  rw [hphase, CircleFourier.character_nsmul, htheta]
  calc
    _ = character r (x.val • (1 : ZMod N)) := (AddChar.map_nsmul_eq_pow _ _ _).symm
    _ = character r x := by simp

end Erdos3.CyclicBohr

end

section

namespace Erdos3

open scoped BigOperators

theorem CircleFourier.character_affine_integer_combination
    {I : Type*} [Fintype I] (a t : ℝ) (b : I → ℝ) (x : I → ℤ) :
    character ((t * (a + ∑ i, (x i : ℝ) * b i) : ℝ) : Circle) =
      character ((t * a : ℝ) : Circle) *
        ∏ i, character ((t * b i : ℝ) : Circle) ^ (x i) := by
  classical
  have hcoe (v : I → ℝ) : ((∑ i, v i : ℝ) : Circle) = ∑ i, (v i : Circle) :=
    map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) v Finset.univ
  rw [mul_add, Finset.mul_sum, AddCircle.coe_add, character_add, hcoe, character_fintype_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [← character_zsmul, ← AddCircle.coe_zsmul]
  congr 1
  congr 1
  simp only [zsmul_eq_mul]
  ring

theorem exists_affine_cyclic_character_phase {I : Type*} [Fintype I]
    {N : ℕ} [NeZero N] (ξ : (I → ℤ) →+ ZMod N) (ξ₀ : ZMod N) :
    ∃ (a : ℝ) (b : I → ℝ), ∀ (x : I → ℤ) (n : ZMod N),
      CircleFourier.character
        (((n.val : ℝ) * (a + ∑ i, (x i : ℝ) * b i) : ℝ) : CircleFourier.Circle) =
          AddChar.zmodAddEquiv (ξ₀ + ξ x) n := by
  classical
  obtain ⟨a, ha⟩ := CyclicBohr.exists_real_frequency_phase ξ₀
  choose b hb using fun i => CyclicBohr.exists_real_frequency_phase (ξ (Pi.single i 1))
  simp only [CyclicBohr.character] at ha hb
  refine ⟨a, b, ?_⟩
  intro x n
  have hx : ξ x = ∑ i, (x i) • ξ (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ' x]
    rw [map_sum]
    simp only [map_zsmul]
  rw [CircleFourier.character_affine_integer_combination, ha n, hx]
  simp only [map_add, map_sum, map_zsmul, AddChar.add_apply, AddChar.sum_apply,
    AddChar.zsmul_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [hb i n]

end Erdos3

end

end OAI

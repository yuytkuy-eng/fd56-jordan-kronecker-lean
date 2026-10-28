/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ThreeOutputTwoGenericFrame
import FD56.Hilbert.GenericSLFromKroneckerGL
import FD56.Hilbert.MinimalDegreeFrameBound

/-! The three-output residue-two scalar frame closes the exact SL profile
as soon as the GL pencil has two pure Kronecker blocks. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem generic_three_two_sl_uniform_of_pure_gl
    (q : ℕ) (i₀ : Fin (3*q+2)) (gs : List ℕ) (hlen : gs.length=2)
    (hGL : HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K (Fin (3*q+2)) (Fin 3))
      (genericAffineRows K (Fin (3*q+2)) (Fin 3))) gs)
    (hminGL : HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin (3*q+2)) (Fin 3))
      (genericAffineRows K (Fin (3*q+2)) (Fin 3))) gs) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (3*q+2)) (Fin 3))
      (genericAffineRows K (Fin (3*q+2)) (Fin 3)) i₀)
      (List.replicate 3 (threeTwoFrameDegree q)) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (3*q+2)) (Fin 3))
      (genericAffineRows K (Fin (3*q+2)) (Fin 3)) i₀)
      (List.replicate 3 (threeTwoFrameDegree q)) := by
  obtain ⟨xs,hl,hs,hmin,_⟩ := generic_sl_exists_kronecker_of_gl_kronecker
    (K:=K) (by norm_num) i₀ gs hGL hminGL
  have hxslen : xs.length=3 := by omega
  have hc := kronecker_decomposition_dimension _ _ hGL
  rw [nat_list_affine_sum,hlen] at hc
  simp only [SLInput,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,one_mul] at hc
  have hsum : xs.sum=3*threeTwoFrameDegree q := by
    have he : 2*xs.sum=3*(3*q^2+7*q+2) := by nlinarith
    unfold threeTwoFrameDegree
    omega
  obtain ⟨Z,hAZ,hZ,hinj⟩ := generic_three_two_sl_kernel_frame (K:=K) q i₀
  have hfinal := minimal_degrees_uniform_of_full_frame_at_point _ xs hmin
    3 (threeTwoFrameDegree q) Z hxslen hsum hAZ hZ 0 hinj
  exact ⟨hfinal,generic_sl_kronecker_of_gl_kronecker (K:=K) (by norm_num)
    i₀ gs hGL hminGL _ hfinal⟩

end FD56

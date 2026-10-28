/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FourteenThreeSLStructure
import FD56.Hilbert.CorankOneObservabilityDegrees

/-! The base (14,3) GL profile and SL dimension budget on plain finite indices. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]

theorem generic_fourteen_three_base_alpha_degrees :
    HasMinimalKernelDegrees (observabilityMatrix
      (genericAffineSquare K (Fin 14) (Fin 3)) (genericAffineRows K (Fin 14) (Fin 3)) 4)
      [15,15] := by
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  apply le_antisymm
  · have h := generic_observability_kernel_le_field_witness (RingHom.id K)
      fourteenThreeM fourteenThreeP fourteenThree_M_degree fourteenThree_P_degree 4 d
    rw [(hasMinimalKernelDegrees_iff_hilbert _ _).mp (fourteenThree_alpha_degrees (K:=K))] at h
    exact h
  · have h := prescribed_matrix_kernel_lower
      (observabilityMatrix (genericAffineSquare K (Fin 14) (Fin 3))
        (genericAffineRows K (Fin 14) (Fin 3)) 4)
      (fun ij => ij.1.val+1)
      (fun i j => (observability_polynomial_degree_top _ _ 4
        (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _) i j).1)
      (by norm_num) d
    norm_num [Fintype.sum_prod_type,Fin.sum_univ_succ] at h
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    omega

theorem generic_fourteen_three_base_gl_minimal_degrees :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin 14) (Fin 3)) (genericAffineRows K (Fin 14) (Fin 3)))
      [59,59] := by
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse
    (K:=K) (n:=Fin 14) (m:=Fin 3) 4 (by norm_num)
  have h := generic_observability_gl_minimal_degrees_of_auxiliary_profiles
    (K:=K) (n:=Fin 14) (m:=Fin 3) 3 (by norm_num) (by norm_num)
    [15,15] [40] generic_fourteen_three_base_alpha_degrees (by
      intro r B
      have hb := generic_corank_one_all_depths_beta_degrees 4 (by norm_num)
        (by norm_num) B R hR
      simpa [Fin.sum_univ_succ] using hb)
  simpa [degreeConvolution] using h

theorem generic_fourteen_three_base_gl_kronecker :
    HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K (Fin 14) (Fin 3)) (genericAffineRows K (Fin 14) (Fin 3)))
      [59,59] := by
  apply glKirillovMatrix_kronecker _ _ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
    generic_fourteen_three_base_gl_minimal_degrees
  norm_num [SLInput]

theorem generic_fourteen_three_base_sl_kronecker_structure (i₀ : Fin 14) :
    ∃ xs : List ℕ, xs.length=3 ∧ xs.sum=117 ∧
      HasMinimalKernelDegrees (slEquationMatrix
        (genericAffineSquare K (Fin 14) (Fin 3)) (genericAffineRows K (Fin 14) (Fin 3)) i₀) xs ∧
      HasKroneckerDecomposition (slKirillovMatrix
        (genericAffineSquare K (Fin 14) (Fin 3)) (genericAffineRows K (Fin 14) (Fin 3)) i₀) xs := by
  obtain ⟨xs,hl,hs,hmin,hcanon⟩ := generic_sl_exists_kronecker_of_gl_kronecker (K:=K)
    (by norm_num) i₀ [59,59] generic_fourteen_three_base_gl_kronecker
    generic_fourteen_three_base_gl_minimal_degrees
  refine ⟨xs,by simpa using hl,?_,hmin,hcanon⟩
  norm_num at hs
  omega

end FD56

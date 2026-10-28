/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthFourFourteenThreeWitness
import FD56.Hilbert.CorankOneRepeatedBeta
import FD56.Hilbert.GenericDepthTwoAlpha
import FD56.Hilbert.GenericObservabilityGLTransfer
import FD56.Hilbert.GenericObservabilityKronecker

/-! A complete GL Kronecker family at state/output ratio fourteen to three. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K t : Type*} [Field K] [CharZero K] [Fintype t] [DecidableEq t]

theorem generic_fourteen_three_repeated_alpha_hilbert (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters (Fin 14 × t) (Fin 3 × t)))
      (polynomialKernelAtDegree (observabilityMatrix
        (genericAffineSquare K (Fin 14 × t) (Fin 3 × t))
        (genericAffineRows K (Fin 14 × t) (Fin 3 × t)) 4) d)=
      (2*Fintype.card t)*(d+1-15) := by
  let M := fun _ : t => fourteenThreeM (K := K)
  let P := fun _ : t => fourteenThreeP (K := K)
  apply le_antisymm
  · have hh := generic_observability_kernel_le_field_witness (RingHom.id K)
      (Matrix.blockDiagonal M) (Matrix.blockDiagonal P)
      (blockDiagonal_degreeBound_one M (fun _ => fourteenThree_M_degree))
      (blockDiagonal_degreeBound_one P (fun _ => fourteenThree_P_degree)) 4 d
    rw [observability_blocks_kernel_finrank] at hh
    have hb := (hasMinimalKernelDegrees_iff_hilbert _ _).mp (fourteenThree_alpha_degrees (K := K)) d
    simp only [M,P,hb,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] at hh
    convert hh using 1 <;> ring
  · have hh := prescribed_matrix_kernel_lower
      (observabilityMatrix (genericAffineSquare K (Fin 14 × t) (Fin 3 × t))
        (genericAffineRows K (Fin 14 × t) (Fin 3 × t)) 4)
      (fun ij => ij.1.val+1)
      (fun i j => (observability_polynomial_degree_top _ _ 4
        (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _) i j).1)
      (by simp only [Fintype.card_prod,Fintype.card_fin]; omega) d
    have hs : (∑ ij : Fin 4 × (Fin 3 × t), (ij.1.val+1))=30*Fintype.card t := by
      simp [Fintype.sum_prod_type,Fin.sum_univ_succ]
      omega
    have hr : Fintype.card (Fin 14 × t)-Fintype.card (Fin 4 × (Fin 3 × t))=2*Fintype.card t := by
      simp only [Fintype.card_prod,Fintype.card_fin]
      omega
    rw [hs,hr] at hh
    have he : 2*Fintype.card t*(d+1-15)=2*Fintype.card t*(d+1)-30*Fintype.card t := by
      rw [Nat.mul_sub_left_distrib]
      congr 1
      ring
    rwa [he]

theorem generic_fourteen_three_repeated_alpha_degrees :
    HasMinimalKernelDegrees (observabilityMatrix
      (genericAffineSquare K (Fin 14 × t) (Fin 3 × t))
      (genericAffineRows K (Fin 14 × t) (Fin 3 × t)) 4)
      (List.replicate (2*Fintype.card t) 15) := by
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [generic_fourteen_three_repeated_alpha_hilbert]
  simp

variable [Nonempty t]

theorem generic_fourteen_three_repeated_gl_minimal_degrees :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin 14 × t) (Fin 3 × t))
      (genericAffineRows K (Fin 14 × t) (Fin 3 × t)))
      (List.replicate (2*Fintype.card t^2) 59) := by
  have ht : 0<Fintype.card t := Fintype.card_pos
  have hb : ∀ (r : ℕ) (B : Basis (Fin r)
      (AffineCoefficientField K (MatrixParameters (Fin 14 × t) (Fin 3 × t)))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K (Fin 14 × t) (Fin 3 × t))
        (genericAffineRows K (Fin 14 × t) (Fin 3 × t)) 4)))),
      HasMinimalKernelDegrees (genericAffineRows K (Fin 14 × t) (Fin 3 × t)*
        (genericAffineSquare K (Fin 14 × t) (Fin 3 × t))^4*
        polynomialKernelBasisMatrix _ B).transpose (List.replicate (Fintype.card t) 40) := by
    intro r B
    have h := generic_corank_one_repeated_beta_degrees (K := K) (n := Fin 14) (m := Fin 3)
      4 (by norm_num) (by norm_num) B
    simpa [Fin.sum_univ_succ] using h
  have h := generic_observability_gl_minimal_degrees_of_auxiliary_profiles 3
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega)
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega)
    _ _ (generic_fourteen_three_repeated_alpha_degrees (K := K) (t := t)) hb
  simp only [degreeConvolution,List.flatMap_replicate,List.map_replicate,
    List.flatten_replicate_replicate] at h
  convert h using 1 <;> congr 1 <;> ring

theorem generic_fourteen_three_repeated_gl_kronecker :
    HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K (Fin 14 × t) (Fin 3 × t))
      (genericAffineRows K (Fin 14 × t) (Fin 3 × t)))
      (List.replicate (2*Fintype.card t^2) 59) := by
  apply glKirillovMatrix_kronecker _ _ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
    generic_fourteen_three_repeated_gl_minimal_degrees
  simp only [SLInput,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,List.map_replicate,
    List.sum_replicate,smul_eq_mul]
  ring

end FD56

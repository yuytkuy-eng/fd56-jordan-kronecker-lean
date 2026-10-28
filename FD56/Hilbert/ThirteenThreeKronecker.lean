/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthFourThirteenThreeWitness
import FD56.Hilbert.GenericObservabilityBetaTests
import FD56.Hilbert.ObservabilityBetaBlockDimension
import FD56.Hilbert.CorankOneRepeatedAlpha
import FD56.Hilbert.GenericObservabilityGLTransfer
import FD56.Hilbert.MixedGLKronecker

/-! Exact canonical GL blocks for the characteristic-zero thirteen/three family. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K t : Type*} [Field K] [CharZero K] [Fintype t] [DecidableEq t] [Nonempty t]

theorem generic_thirteen_three_repeated_beta_degrees
    {r : Type*} [Fintype r]
    (B : Basis r (AffineCoefficientField K (MatrixParameters (Fin 13 × t) (Fin 3 × t)))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K (Fin 13 × t) (Fin 3 × t))
        (genericAffineRows K (Fin 13 × t) (Fin 3 × t)) 4)))) :
    HasMinimalKernelDegrees
      (genericAffineRows K (Fin 13 × t) (Fin 3 × t) *
        (genericAffineSquare K (Fin 13 × t) (Fin 3 × t))^4 *
        polynomialKernelBasisMatrix (observabilityMatrix
          (genericAffineSquare K (Fin 13 × t) (Fin 3 × t))
          (genericAffineRows K (Fin 13 × t) (Fin 3 × t)) 4) B).transpose
      (List.replicate (Fintype.card t) 17 ++ List.replicate (Fintype.card t) 18) := by
  let M := fun _ : t => thirteenThreeQ4M (K:=K)
  let P := fun _ : t => thirteenThreeQ4P (K:=K)
  have hM : DegreeBound (blockDiagonal M) 1 :=
    blockDiagonal_degreeBound_one M (fun _ => thirteenThreeQ4_M_degree)
  have hP : DegreeBound (blockDiagonal P) 1 :=
    blockDiagonal_degreeBound_one P (fun _ => thirteenThreeQ4_P_degree)
  have ht : 0<Fintype.card t := Fintype.card_pos
  have hz : Module.finrank (AffineCoefficientField K (MatrixParameters (Fin 13 × t) (Fin 3 × t)))
      (boundedObservabilityBetaKernel 4
        (genericAffineSquare K (Fin 13 × t) (Fin 3 × t))
        (genericAffineRows K (Fin 13 × t) (Fin 3 × t)) 16)=0 := by
    have hh := generic_observability_beta_kernel_le_field_witness 4
      (RingHom.id K) (blockDiagonal M) (blockDiagonal P) hM hP 16
    rw [observability_beta_blocks_finrank] at hh
    simp only [M,P,thirteenThreeQ4_beta_kernel_zero,Finset.sum_const_zero] at hh
    exact Nat.eq_zero_of_le_zero hh
  have hc : Module.finrank (AffineCoefficientField K (MatrixParameters (Fin 13 × t) (Fin 3 × t)))
      (boundedObservabilityBetaKernel 4
        (genericAffineSquare K (Fin 13 × t) (Fin 3 × t))
        (genericAffineRows K (Fin 13 × t) (Fin 3 × t)) 17)≤Fintype.card t := by
    have hh := generic_observability_beta_kernel_le_field_witness 4
      (RingHom.id K) (blockDiagonal M) (blockDiagonal P) hM hP 17
    rw [observability_beta_blocks_finrank] at hh
    apply hh.trans
    calc
      _ ≤ ∑ _ : t, 1 := Finset.sum_le_sum (fun _ _ => thirteenThreeQ4_beta_kernel_seventeen_le)
      _ = Fintype.card t := by simp
  have hh := generic_observability_beta_degrees_of_budget_tests
    4 17 (Fintype.card t) (Fintype.card t)
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega)
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega)
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega)
    B (by decide)
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega)
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega) hz hc
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [(hasMinimalKernelDegrees_iff_hilbert _ _).mp hh d,
    balancedDegreeList_hilbert _ _ d (by omega)]
  simpa only [List.map_append,List.map_replicate,List.sum_append,List.sum_replicate,
    smul_eq_mul,Nat.reduceAdd] using
    (adjacent_degree_hilbert (Fintype.card t) (Fintype.card t) 17 d).symm

omit [CharZero K] in
theorem generic_thirteen_three_repeated_alpha_degrees :
    HasMinimalKernelDegrees (observabilityMatrix
      (genericAffineSquare K (Fin 13 × t) (Fin 3 × t))
      (genericAffineRows K (Fin 13 × t) (Fin 3 × t)) 4)
      (List.replicate (Fintype.card t) 30) := by
  simpa [Fin.sum_univ_succ] using
    (generic_corank_one_repeated_alpha_degrees (K:=K) (n:=Fin 13) (m:=Fin 3)
      (t:=t) 4 (by norm_num))

theorem generic_thirteen_three_repeated_gl_minimal_degrees :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin 13 × t) (Fin 3 × t))
      (genericAffineRows K (Fin 13 × t) (Fin 3 × t)))
      (List.replicate (Fintype.card t^2) 51 ++ List.replicate (Fintype.card t^2) 52) := by
  have ht : 0<Fintype.card t := Fintype.card_pos
  have h := generic_observability_gl_minimal_degrees_of_auxiliary_profiles 3
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega)
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega)
    _ _ (generic_thirteen_three_repeated_alpha_degrees (K:=K) (t:=t))
    (fun _ B => generic_thirteen_three_repeated_beta_degrees B)
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [(hasMinimalKernelDegrees_iff_hilbert _ _).mp h d]
  simp only [degreeConvolution,List.map_flatMap,List.map_map,List.map_replicate,
    List.map_append,List.sum_append,List.sum_replicate,nat_sum_flatMap,smul_eq_mul,
    Function.comp_def,Nat.reduceAdd]
  ring

theorem generic_thirteen_three_repeated_gl_kronecker :
    HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K (Fin 13 × t) (Fin 3 × t))
      (genericAffineRows K (Fin 13 × t) (Fin 3 × t)))
      (List.replicate (Fintype.card t^2) 51 ++ List.replicate (Fintype.card t^2) 52) := by
  apply glKirillovMatrix_kronecker _ _ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
    generic_thirteen_three_repeated_gl_minimal_degrees
  simp only [SLInput,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,
    List.map_append,List.map_replicate,List.sum_append,List.sum_replicate,smul_eq_mul]
  ring

end FD56

/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeSevenTwoWitness
import FD56.Hilbert.DepthThreeGL

/-! The generic seven-state, two-row GL pencil in characteristic zero. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]

theorem generic_seven_two_beta_degrees
    (B : Basis (Fin 1) (AffineCoefficientField K (MatrixParameters (Fin 7) (Fin 2)))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K (Fin 7) (Fin 2)) (genericAffineRows K (Fin 7) (Fin 2)) 3)))) :
    HasMinimalKernelDegrees
      (genericAffineRows K (Fin 7) (Fin 2) * (genericAffineSquare K (Fin 7) (Fin 2))^3 *
        polynomialKernelBasisMatrix (observabilityMatrix
          (genericAffineSquare K (Fin 7) (Fin 2)) (genericAffineRows K (Fin 7) (Fin 2)) 3) B).transpose
      [16] := by
  have hh := generic_depth_three_beta_degrees_of_single_field_witness
    (RingHom.id K) (sevenTwoM (K := K)) sevenTwoP sevenTwo_M_degree sevenTwo_P_degree
    (by norm_num : 3*Fintype.card (Fin 2)<Fintype.card (Fin 7))
    (by norm_num : Fintype.card (Fin 7)<4*Fintype.card (Fin 2))
    B 16 (by decide) (by norm_num)
    (by rw [observability_beta_coefficient_kernel_finrank 3 _ _
          sevenTwo_M_degree sevenTwo_P_degree]; exact sevenTwo_beta_kernel_zero)
  simpa [balancedDegreeList] using hh

theorem generic_seven_two_gl_minimal_degrees :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin 7) (Fin 2)) (genericAffineRows K (Fin 7) (Fin 2))) [31] := by
  obtain ⟨r,Bv,a,hV,hVL,hperm⟩ := generic_depth_three_alpha_minimal_degrees
    (K := K) (m := Fin 2) (n := Fin 7) (by norm_num)
  have hp : (List.ofFn a).Perm [12] := by simpa [balancedDegreeList] using hperm
  have hr : r=1 := by simpa using hp.length_eq
  subst r
  have ha (i : Fin 1) : a i=12 := by
    have hh := hp.mem_iff.mp (List.mem_ofFn.mpr ⟨i,rfl⟩)
    simpa using hh
  obtain ⟨s,Bt,b,hT,hTL,hpermT⟩ := generic_seven_two_beta_degrees Bv
  have hs : s=1 := by simpa using hpermT.length_eq
  subst s
  have hb (i : Fin 1) : b i=16 := by
    have hh := hpermT.mem_iff.mp (List.mem_ofFn.mpr ⟨i,rfl⟩)
    simpa using hh
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [generic_depth_three_gl_kernel_hilbert_of_bases (by norm_num) (by norm_num)
    Bv Bt a b hV hT hVL hTL d]
  simp [ha,hb]

end FD56

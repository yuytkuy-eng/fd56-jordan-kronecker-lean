/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.TenThreeSLStructure

/-! The base (10,3) GL profile and the SL dimension budget on plain finite indices. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]

theorem generic_ten_three_base_gl_minimal_degrees :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin 10) (Fin 3)) (genericAffineRows K (Fin 10) (Fin 3)))
      [32,32] := by
  have hAlpha : HasMinimalKernelDegrees (observabilityMatrix
      (genericAffineSquare K (Fin 10) (Fin 3)) (genericAffineRows K (Fin 10) (Fin 3)) 3)
      [18] := by
    simpa [balancedDegreeList] using generic_depth_three_alpha_minimal_degrees
      (K:=K) (n:=Fin 10) (m:=Fin 3) (by norm_num)
  obtain ⟨r,Bv,a,hV,hVL,hperm⟩ := hAlpha
  have hr : r=Fintype.card (Fin 10)-3*Fintype.card (Fin 3) := by
    simpa using hperm.length_eq
  subst r
  have ha (i : Fin (Fintype.card (Fin 10)-3*Fintype.card (Fin 3))) : a i=18 := by
    have h := hperm.mem_iff.mp (List.mem_ofFn.mpr ⟨i,rfl⟩)
    simpa using h
  have hBeta : HasMinimalKernelDegrees
      (genericAffineRows K (Fin 10) (Fin 3)*(genericAffineSquare K (Fin 10) (Fin 3))^3*
        polynomialKernelBasisMatrix _ Bv).transpose [11,11] := by
    have h := generic_depth_three_beta_degrees_of_single_field_witness
      (RingHom.id K) tenThreeM tenThreeP tenThree_M_degree tenThree_P_degree
      (by norm_num) (by norm_num) Bv 11 (by decide) (by norm_num) (by
        rw [observability_beta_coefficient_kernel_finrank 3 _ _ tenThree_M_degree tenThree_P_degree]
        exact tenThree_beta_kernel_zero)
    simpa [balancedDegreeList] using h
  obtain ⟨s,Bt,b,hT,hTL,hpermT⟩ := hBeta
  have hs : s=2 := by simpa using hpermT.length_eq
  subst s
  have hb (i : Fin 2) : b i=11 := by
    have h := hpermT.mem_iff.mp (List.mem_ofFn.mpr ⟨i,rfl⟩)
    simpa using h
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [generic_depth_three_gl_kernel_hilbert_of_bases (by norm_num) (by norm_num)
    Bv Bt a b hV hT hVL hTL d]
  simp [ha,hb,Fin.sum_univ_succ] <;> omega

theorem generic_ten_three_base_gl_kronecker :
    HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K (Fin 10) (Fin 3)) (genericAffineRows K (Fin 10) (Fin 3)))
      [32,32] := by
  apply glKirillovMatrix_kronecker _ _ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
    generic_ten_three_base_gl_minimal_degrees
  norm_num [SLInput]

theorem generic_ten_three_base_sl_kronecker_structure (i₀ : Fin 10) :
    ∃ xs : List ℕ, xs.length=3 ∧ xs.sum=63 ∧
      HasMinimalKernelDegrees (slEquationMatrix
        (genericAffineSquare K (Fin 10) (Fin 3)) (genericAffineRows K (Fin 10) (Fin 3)) i₀) xs ∧
      HasKroneckerDecomposition (slKirillovMatrix
        (genericAffineSquare K (Fin 10) (Fin 3)) (genericAffineRows K (Fin 10) (Fin 3)) i₀) xs := by
  obtain ⟨xs,hl,hs,hmin,hcanon⟩ := generic_sl_exists_kronecker_of_gl_kronecker (K:=K)
    (by norm_num) i₀ [32,32] generic_ten_three_base_gl_kronecker
    generic_ten_three_base_gl_minimal_degrees
  refine ⟨xs,by simpa using hl,?_,hmin,hcanon⟩
  norm_num at hs
  omega

end FD56

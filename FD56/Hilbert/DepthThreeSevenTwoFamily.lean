/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeSevenTwo
import FD56.Hilbert.ObservabilityBetaBlocks

/-! Repeated seven-state witnesses for an infinite third-depth family. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K t : Type*} [Field K] [CharZero K] [Fintype t] [DecidableEq t]

omit [CharZero K] [Fintype t] in
theorem sevenTwo_repeated_M_degree :
    DegreeBound (blockDiagonal (fun _ : t => sevenTwoM (K := K))) 1 := by
  intro i j
  rw [Matrix.blockDiagonal_apply]
  split_ifs
  · exact sevenTwo_M_degree i.1 j.1
  · simp

omit [CharZero K] [Fintype t] in
theorem sevenTwo_repeated_P_degree :
    DegreeBound (blockDiagonal (fun _ : t => sevenTwoP (K := K))) 1 := by
  intro i j
  rw [Matrix.blockDiagonal_apply]
  split_ifs
  · exact sevenTwo_P_degree i.1 j.1
  · simp

set_option synthInstance.maxHeartbeats 400000 in
theorem sevenTwo_repeated_beta_zero :
    Module.finrank K (boundedObservabilityBetaKernel 3
      (blockDiagonal (fun _ : t => sevenTwoM (K := K)))
      (blockDiagonal (fun _ : t => sevenTwoP (K := K))) 15)=0 := by
  have hbase : boundedObservabilityBetaKernel 3 (sevenTwoM (K := K)) sevenTwoP 15=⊥ :=
    Submodule.finrank_eq_zero.mp (sevenTwo_beta_kernel_zero (K := K))
  rw [observability_beta_blocks_eq_bot _ _ 3 15 (fun _ => hbase),finrank_bot]

theorem generic_seven_two_repeated_beta_degrees [Nonempty t]
    (B : Basis (Fin (Fintype.card (Fin 7 × t)-3*Fintype.card (Fin 2 × t)))
      (AffineCoefficientField K (MatrixParameters (Fin 7 × t) (Fin 2 × t)))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K (Fin 7 × t) (Fin 2 × t))
        (genericAffineRows K (Fin 7 × t) (Fin 2 × t)) 3)))) :
    HasMinimalKernelDegrees
      (genericAffineRows K (Fin 7 × t) (Fin 2 × t) *
        (genericAffineSquare K (Fin 7 × t) (Fin 2 × t))^3 *
        polynomialKernelBasisMatrix (observabilityMatrix
          (genericAffineSquare K (Fin 7 × t) (Fin 2 × t))
          (genericAffineRows K (Fin 7 × t) (Fin 2 × t)) 3) B).transpose
      (List.replicate (Fintype.card t) 16) := by
  have ht : 0<Fintype.card t := Fintype.card_pos
  have hr : Fintype.card (Fin 7 × t)-3*Fintype.card (Fin 2 × t)=Fintype.card t := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    omega
  have hs : Fintype.card (Fin 2 × t)-(Fintype.card (Fin 7 × t)-3*Fintype.card (Fin 2 × t))=
      Fintype.card t := by rw [hr]; simp only [Fintype.card_prod,Fintype.card_fin]; omega
  have hc : 6*Fintype.card (Fin 2 × t)+4*(Fintype.card (Fin 7 × t)-3*Fintype.card (Fin 2 × t))=
      16*Fintype.card t := by rw [hr]; simp only [Fintype.card_prod,Fintype.card_fin]; omega
  have hh := generic_depth_three_beta_degrees_of_single_field_witness
    (RingHom.id K) (blockDiagonal (fun _ : t => sevenTwoM (K := K)))
    (blockDiagonal (fun _ : t => sevenTwoP (K := K)))
    sevenTwo_repeated_M_degree sevenTwo_repeated_P_degree
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega)
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega)
    B 16 (by decide) (by rw [hs,hc])
    (by rw [observability_beta_coefficient_kernel_finrank 3 _ _
          sevenTwo_repeated_M_degree sevenTwo_repeated_P_degree]; exact sevenTwo_repeated_beta_zero)
  rw [hc,hs] at hh
  simpa [balancedDegreeList,Nat.ne_of_gt ht] using hh

theorem generic_seven_two_repeated_gl_minimal_degrees [Nonempty t] :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin 7 × t) (Fin 2 × t))
      (genericAffineRows K (Fin 7 × t) (Fin 2 × t)))
      (List.replicate ((Fintype.card t)^2) 31) := by
  have ht : 0<Fintype.card t := Fintype.card_pos
  have hrshape : Fintype.card (Fin 7 × t)-3*Fintype.card (Fin 2 × t)=Fintype.card t := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    omega
  have halpha : balancedDegreeList (6*Fintype.card (Fin 2 × t))
      (Fintype.card (Fin 7 × t)-3*Fintype.card (Fin 2 × t)) =
      List.replicate (Fintype.card t) 12 := by
    rw [hrshape]
    simp only [Fintype.card_prod,Fintype.card_fin]
    rw [show 6*(2*Fintype.card t)=12*Fintype.card t by ring]
    simp [balancedDegreeList,Nat.ne_of_gt ht]
  obtain ⟨r,Bv,a,hV,hVL,hperm⟩ := generic_depth_three_alpha_minimal_degrees
    (K := K) (m := Fin 2 × t) (n := Fin 7 × t)
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega)
  have hr : r=Fintype.card (Fin 7 × t)-3*Fintype.card (Fin 2 × t) := by
    have hh := hperm.length_eq
    rw [halpha,List.length_ofFn,List.length_replicate] at hh
    omega
  subst r
  rw [halpha] at hperm
  have ha (i) : a i=12 := by
    have hh := hperm.mem_iff.mp (List.mem_ofFn.mpr ⟨i,rfl⟩)
    have := (List.mem_replicate.mp hh).2
    omega
  obtain ⟨s,Bt,b,hT,hTL,hpermT⟩ := generic_seven_two_repeated_beta_degrees Bv
  have hs : s=Fintype.card t := by simpa using hpermT.length_eq
  have hb (i) : b i=16 := by
    have hh := hpermT.mem_iff.mp (List.mem_ofFn.mpr ⟨i,rfl⟩)
    have := (List.mem_replicate.mp hh).2
    omega
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [generic_depth_three_gl_kernel_hilbert_of_bases
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega)
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega)
    Bv Bt a b hV hT hVL hTL d]
  simp [ha,hb,hrshape,hs,pow_two]
  omega

end FD56

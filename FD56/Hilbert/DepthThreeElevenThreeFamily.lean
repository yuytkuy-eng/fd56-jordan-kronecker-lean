/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeElevenThreeWitness
import FD56.Hilbert.DepthThreeGL
import FD56.Hilbert.ObservabilityBetaBlocks

/-! Repeated eleven-state witnesses for an infinite third-depth family. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K t : Type*} [Field K] [CharZero K] [Fintype t] [DecidableEq t]

omit [CharZero K] [Fintype t] in
theorem elevenThree_repeated_M_degree :
    DegreeBound (blockDiagonal (fun _ : t => elevenThreeM (K := K))) 1 := by
  intro i j
  rw [Matrix.blockDiagonal_apply]
  split_ifs
  · exact elevenThree_M_degree i.1 j.1
  · simp

omit [CharZero K] [Fintype t] in
theorem elevenThree_repeated_P_degree :
    DegreeBound (blockDiagonal (fun _ : t => elevenThreeP (K := K))) 1 := by
  intro i j
  rw [Matrix.blockDiagonal_apply]
  split_ifs
  · exact elevenThree_P_degree i.1 j.1
  · simp

set_option synthInstance.maxHeartbeats 400000 in
theorem elevenThree_repeated_beta_zero :
    Module.finrank K (boundedObservabilityBetaKernel 3
      (blockDiagonal (fun _ : t => elevenThreeM (K := K)))
      (blockDiagonal (fun _ : t => elevenThreeP (K := K))) 25)=0 := by
  have hbase : boundedObservabilityBetaKernel 3 (elevenThreeM (K := K)) elevenThreeP 25=⊥ :=
    Submodule.finrank_eq_zero.mp (elevenThree_beta_kernel_zero (K := K))
  rw [observability_beta_blocks_eq_bot _ _ 3 25 (fun _ => hbase),finrank_bot]

theorem generic_eleven_three_repeated_beta_degrees [Nonempty t]
    (B : Basis (Fin (Fintype.card (Fin 11 × t)-3*Fintype.card (Fin 3 × t)))
      (AffineCoefficientField K (MatrixParameters (Fin 11 × t) (Fin 3 × t)))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K (Fin 11 × t) (Fin 3 × t))
        (genericAffineRows K (Fin 11 × t) (Fin 3 × t)) 3)))) :
    HasMinimalKernelDegrees
      (genericAffineRows K (Fin 11 × t) (Fin 3 × t) *
        (genericAffineSquare K (Fin 11 × t) (Fin 3 × t))^3 *
        polynomialKernelBasisMatrix (observabilityMatrix
          (genericAffineSquare K (Fin 11 × t) (Fin 3 × t))
          (genericAffineRows K (Fin 11 × t) (Fin 3 × t)) 3) B).transpose
      (List.replicate (Fintype.card t) 26) := by
  have ht : 0<Fintype.card t := Fintype.card_pos
  have hr : Fintype.card (Fin 11 × t)-3*Fintype.card (Fin 3 × t)=2*Fintype.card t := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    omega
  have hs : Fintype.card (Fin 3 × t)-(Fintype.card (Fin 11 × t)-3*Fintype.card (Fin 3 × t))=
      Fintype.card t := by rw [hr]; simp only [Fintype.card_prod,Fintype.card_fin]; omega
  have hc : 6*Fintype.card (Fin 3 × t)+4*(Fintype.card (Fin 11 × t)-3*Fintype.card (Fin 3 × t))=
      26*Fintype.card t := by rw [hr]; simp only [Fintype.card_prod,Fintype.card_fin]; omega
  have hh := generic_depth_three_beta_degrees_of_single_field_witness
    (RingHom.id K) (blockDiagonal (fun _ : t => elevenThreeM (K := K)))
    (blockDiagonal (fun _ : t => elevenThreeP (K := K)))
    elevenThree_repeated_M_degree elevenThree_repeated_P_degree
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega)
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega)
    B 26 (by decide) (by rw [hs,hc])
    (by rw [observability_beta_coefficient_kernel_finrank 3 _ _
          elevenThree_repeated_M_degree elevenThree_repeated_P_degree]; exact elevenThree_repeated_beta_zero)
  rw [hc,hs] at hh
  simpa [balancedDegreeList,Nat.ne_of_gt ht] using hh

theorem generic_eleven_three_repeated_gl_minimal_degrees [Nonempty t] :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin 11 × t) (Fin 3 × t))
      (genericAffineRows K (Fin 11 × t) (Fin 3 × t)))
      (List.replicate (2*(Fintype.card t)^2) 38) := by
  have ht : 0<Fintype.card t := Fintype.card_pos
  have hrshape : Fintype.card (Fin 11 × t)-3*Fintype.card (Fin 3 × t)=2*Fintype.card t := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    omega
  have halpha : balancedDegreeList (6*Fintype.card (Fin 3 × t))
      (Fintype.card (Fin 11 × t)-3*Fintype.card (Fin 3 × t)) =
      List.replicate (2*Fintype.card t) 9 := by
    rw [hrshape]
    simp only [Fintype.card_prod,Fintype.card_fin]
    rw [show 6*(3*Fintype.card t)=9*(2*Fintype.card t) by ring]
    simp [balancedDegreeList,Nat.ne_of_gt ht]
  obtain ⟨r,Bv,a,hV,hVL,hperm⟩ := generic_depth_three_alpha_minimal_degrees
    (K := K) (m := Fin 3 × t) (n := Fin 11 × t)
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega)
  have hr : r=Fintype.card (Fin 11 × t)-3*Fintype.card (Fin 3 × t) := by
    have hh := hperm.length_eq
    rw [halpha,List.length_ofFn,List.length_replicate] at hh
    omega
  subst r
  rw [halpha] at hperm
  have ha (i) : a i=9 := by
    have hh := hperm.mem_iff.mp (List.mem_ofFn.mpr ⟨i,rfl⟩)
    have := (List.mem_replicate.mp hh).2
    omega
  obtain ⟨s,Bt,b,hT,hTL,hpermT⟩ := generic_eleven_three_repeated_beta_degrees Bv
  have hs : s=Fintype.card t := by simpa using hpermT.length_eq
  have hb (i) : b i=26 := by
    have hh := hpermT.mem_iff.mp (List.mem_ofFn.mpr ⟨i,rfl⟩)
    have := (List.mem_replicate.mp hh).2
    omega
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [generic_depth_three_gl_kernel_hilbert_of_bases
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega)
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega)
    Bv Bt a b hV hT hVL hTL d]
  simp only [ha,hb,Nat.reduceAdd,Finset.sum_const,Finset.card_univ,
    Fintype.card_prod,Fintype.card_fin,List.map_replicate,List.sum_replicate,smul_eq_mul]
  rw [show 11*Fintype.card t-3*(3*Fintype.card t)=2*Fintype.card t by omega,hs]
  ring

end FD56

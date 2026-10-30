/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericInteriorDegreeBalance
import FD56.Hilbert.InteriorFullGradients

/-! Every full minor in the six-output middle remainder has one common
three-column representation. Its three degree bounds are equal. This does
not assert faithful specialization or determine the SL minimal indices. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000

variable {K : Type*} [Field K]

theorem generic_six_output_triple_representation (q : ℕ) (hq : 0<q) :
    ∃ (G : Matrix (Fin 6) (Fin 3)
        (AffineCoefficientField K (MatrixParameters (Fin (6*q+3)) (Fin 6)))[X])
      (c : AffineCoefficientField K (MatrixParameters (Fin (6*q+3)) (Fin 6))),
      c≠0 ∧ (∀ i j, (G i j).natDegree≤(q+1)^2) ∧
      Function.Injective G.mulVec ∧
      ∀ row : Fin 3 → Fin 6,
        interiorFullMinor 3 3 q (genericAffineSquare K (Fin (6*q+3)) (Fin 6))
          (genericAffineRows K (Fin (6*q+3)) (Fin 6)) row=
          C c*pluckerMinorVector G row := by
  classical
  let F := AffineCoefficientField K (MatrixParameters (Fin (6*q+3)) (Fin 6))
  let M := genericAffineSquare K (Fin (6*q+3)) (Fin 6)
  let P := genericAffineRows K (Fin (6*q+3)) (Fin 6)
  let O := observabilityMatrix M P q
  have hlo : q*Fintype.card (Fin 6)<Fintype.card (Fin (6*q+3)) := by
    simp only [Fintype.card_fin]; omega
  have hhi : Fintype.card (Fin (6*q+3))<(q+1)*Fintype.card (Fin 6) := by
    simp only [Fintype.card_fin]; omega
  obtain ⟨k,B,e,hV,hlead,_,_⟩ := polynomial_kernel_has_minimal_basis O
  have hmin : HasMinimalKernelDegrees O (List.ofFn e) :=
    ⟨k,B,e,hV,hlead,List.Perm.refl _⟩
  have hk := (generic_observability_kernel_degree_budget (K:=K) q hlo _ hmin).1
  simp only [List.length_ofFn,Fintype.card_fin] at hk
  have hk' : k=3 := by omega
  subst k
  let V := polynomialKernelBasisMatrix O B
  let G := P*M^q*V
  let d : Fin 3 → ℕ := fun j => e j+q+1
  let W := (∑ j, e j)+(q+1)*3
  have hbudget := (generic_observability_kernel_degree_budget (K:=K) q hlo _ hmin).2
  simp only [List.sum_ofFn,Fintype.card_fin] at hbudget
  have hweight : 2*W=6*q*(q+1)+6*(q+1) := by
    dsimp [W]
    nlinarith
  have hW : W=3*(q+1)^2 := by nlinarith [hweight]
  have hsum : (∑ j, d j)=W := by
    simp only [d,W,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul]
    ring
  have hdegree := (generic_terminal_kernel_degree_and_leading q hhi.le B e hV hlead).1
  change ∀ i j, (G i j).natDegree≤d j at hdegree
  obtain ⟨LG,hLG⟩ := generic_terminal_kernel_left_inverse q (by simp : 2≤Fintype.card (Fin 6))
    hlo hhi B
  change LG*G=1 at hLG
  have hGinj : Function.Injective G.mulVec := by
    intro x y h
    have hh := congrArg LG.mulVec h
    simpa only [Matrix.mulVec_mulVec,hLG,Matrix.one_mulVec] using hh
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse (K:=K) q hlo
  obtain ⟨c,hc,hfull⟩ := interiorFullMinor_common_scalar 3 3 q M P R hR B
  have hselected : genericInteriorMinorVector (K:=K) 3 3 q=
      fun z => C c*pluckerMinorVector G (interiorTerminalRow 3 3 z) := by
    funext z
    have hh := hfull (interiorTerminalRow 3 3 z)
    simpa only [interiorFullMinor,interiorFullRow_selected] using hh
  have hlower := generic_interior_minor_derivation_rank_lower_of_weight (K:=K)
    3 3 q hq W (by nlinarith [hweight])
  have hbal : ∀ i j, d i≤d j+1 := by
    apply polynomial_derivation_selected_plucker_degrees_balanced (K:=K)
      (interiorTerminalRow 3 3) c G d hdegree hGinj (by simp)
    rw [←hselected]
    simpa only [Fintype.card_fin,hsum] using hlower
  have hd : ∀ j, d j=(q+1)^2 := by
    have h01 := hbal 0 1
    have h02 := hbal 0 2
    have h10 := hbal 1 0
    have h12 := hbal 1 2
    have h20 := hbal 2 0
    have h21 := hbal 2 1
    rw [hW] at hsum
    have hsum' : d 0+d 1+d 2=3*(q+1)^2 := by
      simpa [Fin.sum_univ_succ,add_assoc] using hsum
    intro j
    have hj : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases hj with rfl|rfl|rfl <;> omega
  refine ⟨G,c,hc,?_,hGinj,hfull⟩
  intro i j
  simpa only [hd j] using hdegree i j

theorem generic_six_output_triple_minor_realization (q : ℕ) (hq : 0<q) :
    ∃ G : Matrix (Fin 6) (Fin 3)
        (AffineCoefficientField K (MatrixParameters (Fin (6*q+3)) (Fin 6)))[X],
      (∀ i j, (G i j).natDegree≤(q+1)^2) ∧
      ∀ row : Fin 3 → Fin 6,
        interiorFullMinor 3 3 q (genericAffineSquare K (Fin (6*q+3)) (Fin 6))
          (genericAffineRows K (Fin (6*q+3)) (Fin 6)) row=
          pluckerMinorVector G row := by
  obtain ⟨G,c,_,hdegree,_,hminor⟩ := generic_six_output_triple_representation (K:=K) q hq
  let H := fun i j => if j=(0 : Fin 3) then C c*G i j else G i j
  refine ⟨H,?_,?_⟩
  · intro i j
    by_cases hj : j=0
    · simpa only [H,hj,if_pos] using (natDegree_C_mul_le c (G i 0)).trans (hdegree i 0)
    · simpa only [H,hj,if_false] using hdegree i j
  · intro row
    rw [hminor]
    simp only [pluckerMinorVector,Matrix.det_fin_three,Matrix.submatrix_apply,
      id_eq,H,Fin.reduceEq,if_true,if_false]
    ring

end FD56

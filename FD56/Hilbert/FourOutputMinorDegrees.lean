/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FourOutputMinorOutputAction
import FD56.Hilbert.ResidueOneAllDepthFrame

/-! Exact row weight and uniform degree bounds for the six four-output
observability minors and their actual SL kernel gradients. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false

theorem four_output_interior_row_weight (q : ℕ) :
    (∑ k : Fin (4*q+2), (interiorLevel 2 2 q k+1))=2*(q+1)^2 := by
  simp only [interiorLevel]
  rw [Fin.sum_univ_add]
  simp only [Fin.coe_castAdd,Fin.coe_natAdd]
  have ht (i : Fin 2) : (4*q+i.val)/4=q := by omega
  simp_rw [ht]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  have hp := residueOne_prefix_row_weight 4 q
  norm_num only [Nat.reduceAdd] at *
  nlinarith

theorem fourOutputInteriorMinors_degree {K : Type*} [Field K] (q : ℕ)
    (M : Matrix (Fin (4*q+2)) (Fin (4*q+2)) K[X])
    (P : Matrix (Fin 4) (Fin (4*q+2)) K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) :
    ∀ i, (fourOutputInteriorMinors q M P i).natDegree≤2*(q+1)^2 := by
  intro i
  have he : (∑ k : Fin (4*q+2), (interiorLevel 2 2 q k+1))=2*(q+1)^2-1+1 := by
    rw [four_output_interior_row_weight]
    have hp : 0<(q+1)^2 := pow_pos (by omega) _
    omega
  have h := (observability_adjugate_solution_degree M P hM hP
    (interiorLevel 2 2 q) (fourOutputInteriorRow q i) (2*(q+1)^2-1) he).2.2
  rw [four_output_selected_matrix_fromRows] at h
  change (fourOutputInteriorMinors q M P i).natDegree≤_ at h
  have hp : 0<(q+1)^2 := pow_pos (by omega) _
  omega

theorem fourOutputScalarLiftMatrix_degree {K : Type*} [Field K] (q : ℕ)
    (M : Matrix (Fin (4*q+2)) (Fin (4*q+2)) K[X])
    (P : Matrix (Fin 4) (Fin (4*q+2)) K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) :
    DegreeBound (fourOutputScalarLiftMatrix q M P) (2*(q+1)^2-1) := by
  intro k i
  have he : (∑ k : Fin (4*q+2), (interiorLevel 2 2 q k+1))=2*(q+1)^2-1+1 := by
    rw [four_output_interior_row_weight]
    have hp : 0<(q+1)^2 := pow_pos (by omega) _
    omega
  obtain ⟨hX,hU,_⟩ := observability_adjugate_solution_degree M P hM hP
    (interiorLevel 2 2 q) (fourOutputInteriorRow q i) (2*(q+1)^2-1) he
  rcases k with ab|ab
  · exact hX ab.1 ab.2
  · exact hU ab.1 ab.2

theorem generic_four_output_minors_degree {K : Type*} [Field K] (q : ℕ) :
    ∀ i, (genericFourOutputInteriorMinors (K:=K) q i).natDegree≤2*(q+1)^2 :=
  fourOutputInteriorMinors_degree q _ _ (genericAffineSquare_degree K _ _)
    (genericAffineRows_degree K _ _)

theorem generic_four_output_scalar_lift_degree {K : Type*} [Field K] (q : ℕ) :
    DegreeBound (fourOutputScalarLiftMatrix q
      (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
      (genericAffineRows K (Fin (4*q+2)) (Fin 4))) (2*(q+1)^2-1) :=
  fourOutputScalarLiftMatrix_degree q _ _ (genericAffineSquare_degree K _ _)
    (genericAffineRows_degree K _ _)

theorem four_output_first_minor_eq_base {R : Type*} [CommRing R] (q : ℕ)
    (M : Matrix (Fin (4*q+2)) (Fin (4*q+2)) R)
    (P : Matrix (Fin 4) (Fin (4*q+2)) R) :
    fourOutputInteriorMinors q M P 0=
      (observabilitySelectedMatrix M P (interiorLevel 2 2 q) (interiorBaseRow 2 2 q)).det := by
  have hrows : fourOutputPluckerRows 0=interiorTerminalRow 2 2 none := by
    funext a
    fin_cases a <;> rfl
  change ((Matrix.fromRows (observabilityMatrix M P q)
    ((P*M^q).submatrix (fourOutputPluckerRows 0) id)).submatrix (interiorPrefixEquiv 2 2 q) id).det=_
  rw [hrows]
  exact congrArg Matrix.det (interior_selected_matrix_fromRows 2 2 q M P none).symm

private theorem four_output_universal_base_det_ne_zero {K : Type*} [Field K] (q : ℕ) :
    (observabilitySelectedMatrix (universalSquare K (Fin (4*q+2)) (Fin 4))
      (universalRows K (Fin (4*q+2)) (Fin 4))
      (interiorLevel 2 2 q) (interiorBaseRow 2 2 q)).det≠0 := by
  intro hzero
  let φ := matrixSpecialization (interiorShiftM (R:=K) 2 2 q) (interiorShiftP 2 2 q)
  have h := congrArg φ hzero
  rw [RingHom.map_det,RingHom.mapMatrix_apply,observabilitySelectedMatrix_map] at h
  dsimp only [φ] at h
  rw [(universal_pair_specialization (interiorShiftM (R:=K) 2 2 q)
    (interiorShiftP 2 2 q)).1,
    (universal_pair_specialization (interiorShiftM (R:=K) 2 2 q)
    (interiorShiftP 2 2 q)).2,interior_shift_selected_base,Matrix.det_one,map_zero] at h
  exact one_ne_zero h

theorem generic_four_output_first_minor_degree {K : Type*} [Field K] (q : ℕ) :
    (genericFourOutputInteriorMinors (K:=K) q 0).natDegree=2*(q+1)^2 := by
  let M := genericAffineSquare K (Fin (4*q+2)) (Fin 4)
  let P := genericAffineRows K (Fin (4*q+2)) (Fin 4)
  let level := interiorLevel 2 2 q
  let row := interiorBaseRow 2 2 q
  let A := observabilitySelectedMatrix M P level row
  have hM := genericAffineSquare_degree K (Fin (4*q+2)) (Fin 4)
  have hP := genericAffineRows_degree K (Fin (4*q+2)) (Fin 4)
  have htop (k j : Fin (4*q+2)) :
      (A k j).natDegree≤level k+1 ∧
      (A k j).coeff (level k+1)=
        observabilitySelectedMatrix (matrixCoeff M 1) (matrixCoeff P 1) level row k j := by
    exact observability_polynomial_degree_top M P (level k+1) hM hP
      (⟨level k,by omega⟩,row k) j
  have hrowtop : (fun k j => (A k j).coeff (level k+1))=
      observabilitySelectedMatrix (matrixCoeff M 1) (matrixCoeff P 1) level row := by
    funext k j
    exact (htop k j).2
  have hnonzero : (observabilitySelectedMatrix (matrixCoeff M 1) (matrixCoeff P 1) level row).det≠0 := by
    dsimp only [M,P]
    rw [(genericAffine_leading_pair K (Fin (4*q+2)) (Fin 4)).1,
      (genericAffine_leading_pair K (Fin (4*q+2)) (Fin 4)).2,
      ← observabilitySelectedMatrix_map,← RingHom.mapMatrix_apply,← RingHom.map_det]
    exact (map_ne_zero_iff _ (affineLeadingParameterMap_injective K _)).mpr
      (four_output_universal_base_det_ne_zero (K:=K) q)
  have hdegree := polynomial_det_natDegree_eq_row_sum A (fun k => level k+1)
    (fun k j => (htop k j).1) (by rw [hrowtop]; exact hnonzero)
  rw [four_output_interior_row_weight q] at hdegree
  change (fourOutputInteriorMinors q M P 0).natDegree=_
  rw [four_output_first_minor_eq_base]
  exact hdegree

theorem generic_four_output_first_minor_ne_zero {K : Type*} [Field K] (q : ℕ) :
    genericFourOutputInteriorMinors (K:=K) q 0≠0 := by
  intro h
  have hd := generic_four_output_first_minor_degree (K:=K) q
  rw [h,Polynomial.natDegree_zero] at hd
  have hp : 0<(q+1)^2 := pow_pos (by omega) _
  omega

end FD56

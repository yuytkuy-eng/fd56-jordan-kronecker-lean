/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericDepthTwoAlpha
import FD56.Hilbert.DepthTwoGenericStack
import FD56.Hilbert.DepthTwoAuxiliaryLift

/-! Basis and right-inverse data for the actual generic stack consisting of P and PM. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

def depthTwoIndexEquiv (m : Type*) : m ⊕ m ≃ Fin 2 × m where
  toFun := Sum.elim (fun x => (0,x)) (fun x => (1,x))
  invFun z := if z.1=0 then Sum.inl z.2 else Sum.inr z.2
  left_inv z := by cases z <;> simp
  right_inv z := by rcases z with ⟨i,x⟩; fin_cases i <;> rfl

variable {K L m n : Type*} [Field K] [Field L]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [Fintype m] [DecidableEq m] in
theorem depthTwoStack_eq_observability (M : Matrix n n K[X]) (P : Matrix m n K[X]) :
    depthTwoStack P (P*M) =
      (observabilityMatrix M P 2).submatrix (depthTwoIndexEquiv m) (Equiv.refl n) := by
  funext i x
  cases i <;> simp [depthTwoStack,observabilityMatrix,depthTwoIndexEquiv]

theorem generic_actual_depth_two_stack_hilbert
    (hmn : 2*Fintype.card m < Fintype.card n) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (depthTwoStack (genericAffineRows K n m)
        (genericAffineRows K n m*genericAffineSquare K n m)) d) =
      (Fintype.card n-2*Fintype.card m)*(d+1)-3*Fintype.card m := by
  rw [depthTwoStack_eq_observability,reindex_kernel_hilbert,
    generic_depth_two_alpha_hilbert hmn d]

theorem generic_actual_depth_two_stack_minimal_degrees
    (hmn : 2*Fintype.card m < Fintype.card n) :
    HasMinimalKernelDegrees (depthTwoStack (genericAffineRows K n m)
      (genericAffineRows K n m*genericAffineSquare K n m))
      (balancedDegreeList (3*Fintype.card m) (Fintype.card n-2*Fintype.card m)) := by
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [generic_actual_depth_two_stack_hilbert hmn d,
    balancedDegreeList_hilbert _ _ d (by omega)]

theorem generic_actual_depth_two_stack_right_inverse
    (hmn : 2*Fintype.card m < Fintype.card n) :
    ∃ R : Matrix n (m ⊕ m) (AffineCoefficientField K (MatrixParameters n m))[X],
      DegreeBound R (3*Fintype.card m) ∧
      depthTwoStack (genericAffineRows K n m)
        (genericAffineRows K n m*genericAffineSquare K n m)*R=1 := by
  let O := depthTwoStack (genericAffineRows K n m)
    (genericAffineRows K n m*genericAffineSquare K n m)
  have hO : ∀ i j, (O i j).natDegree ≤ depthTwoRowDegree i :=
    depthTwo_stack_degree _ _ (genericAffineRows_degree K n m)
      (degreeBound_mul (genericAffineRows_degree K n m) (genericAffineSquare_degree K n m))
  apply weighted_right_inverse_of_coefficient_surjective O depthTwoRowDegree
    (3*Fintype.card m) hO
  apply column_coefficient_surjective_of_kernel_hilbert O.transpose depthTwoRowDegree
    (3*Fintype.card m) (fun j i => hO i j)
    (by simp only [Fintype.card_sum]; omega)
  · rw [genericDepthTwoStack_sum_degree]
    simp only [Fintype.card_sum]
    have hr : 1 ≤ Fintype.card n-(Fintype.card m+Fintype.card m) := by omega
    nlinarith
  · rw [Matrix.transpose_transpose, generic_actual_depth_two_stack_hilbert hmn,
      genericDepthTwoStack_sum_degree]
    simp only [Fintype.card_sum,two_mul]

def depthTwoRowLeadingMatrix {R : Type*} [CommRing R]
    (M : Matrix n n R[X]) (P : Matrix m n R[X]) : Matrix n (m ⊕ m) R :=
  fun x => Sum.elim (fun i => (P i x).coeff 1) (fun i => ((P*M) i x).coeff 2)

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
theorem depthTwoRowLeadingMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    (M : Matrix n n R[X]) (P : Matrix m n R[X]) (φ : R →+* S) :
    depthTwoRowLeadingMatrix (M.map (Polynomial.mapRingHom φ)) (P.map (Polynomial.mapRingHom φ)) =
      (depthTwoRowLeadingMatrix M P).map φ := by
  funext x i
  cases i with
  | inl i => simp [depthTwoRowLeadingMatrix,Polynomial.coe_mapRingHom,Polynomial.coeff_map]
  | inr i =>
    change (((P.map (Polynomial.mapRingHom φ))*(M.map (Polynomial.mapRingHom φ))) i x).coeff 2 = _
    rw [← Matrix.map_mul]
    simp [depthTwoRowLeadingMatrix,Polynomial.coe_mapRingHom,Polynomial.coeff_map]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
theorem depthTwoRowLeadingMatrix_eq (M : Matrix n n K[X]) (P : Matrix m n K[X]) :
    depthTwoRowLeadingMatrix M P =
      (show Matrix n (m ⊕ m) K from fun x i =>
        (depthTwoStack P (P*M) i x).coeff (depthTwoRowDegree i)) := by
  funext x i
  cases i <;> rfl

theorem generic_actual_depth_two_leading_of_field_witness
    (σ : K →+* L) (M : Matrix n n L[X]) (P : Matrix m n L[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hi : Function.Injective (depthTwoRowLeadingMatrix M P).mulVec) :
    Function.Injective (depthTwoRowLeadingMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m)).mulVec := by
  let ψ := affinePairFieldSpecialization σ M P
  let φ := algebraMap (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K)
    (AffineCoefficientField K (MatrixParameters n m))
  let A := depthTwoRowLeadingMatrix (universalAffineSquare K n m) (universalAffineRows K n m)
  have he : A.map ψ = depthTwoRowLeadingMatrix M P := by
    dsimp only [A,ψ]
    rw [← depthTwoRowLeadingMatrix_map,universalAffineSquare_field_specialization σ M P hM,
      universalAffineRows_field_specialization σ M P hP]
  have hg : A.map φ = depthTwoRowLeadingMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) := by
    dsimp only [A,φ]
    rw [← depthTwoRowLeadingMatrix_map,universalAffineSquare_generic,universalAffineRows_generic]
  rw [← hg]
  exact matrix_injective_of_field_specialization ψ φ (IsFractionRing.injective _ _) A
    (by rw [he]; exact hi)

theorem generic_actual_depth_two_stack_leading_injective
    (hmn : 2*Fintype.card m < Fintype.card n) :
    Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack (genericAffineRows K n m)
        (genericAffineRows K n m*genericAffineSquare K n m) i x).coeff (depthTwoRowDegree i))) := by
  let O := genericDepthTwoStack K n m
  let P := O.submatrix Sum.inl id
  let Q := O.submatrix Sum.inr id
  have hO : depthTwoStack P Q = O := by funext i x; cases i <;> rfl
  have hP : DegreeBound P 1 := fun i j => genericPrescribedMatrix_degree depthTwoRowDegree (Sum.inl i) j
  have hQ : DegreeBound Q 2 := fun i j => genericPrescribedMatrix_degree depthTwoRowDegree (Sum.inr i) j
  obtain ⟨M,hM,hPM⟩ := depthTwo_affine_preimage_of_coefficient_surjective P Q hP hQ
    (genericDepthTwoStack_first_coefficient_surjective hmn)
  let σ : K →+* DepthTwoStackField K n m :=
    (algebraMap (MvPolynomial (PrescribedMatrixParameters n (depthTwoRowDegree (m := m))) K) _).comp
      MvPolynomial.C
  have hi : Function.Injective (depthTwoRowLeadingMatrix M P).mulVec := by
    rw [depthTwoRowLeadingMatrix_eq,hPM,hO]
    exact genericDepthTwoStack_row_leading_injective hmn.le
  have hh := generic_actual_depth_two_leading_of_field_witness σ M P hM hP hi
  rw [depthTwoRowLeadingMatrix_eq] at hh
  exact hh

end FD56

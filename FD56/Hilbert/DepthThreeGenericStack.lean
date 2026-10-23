/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthTwoGenericStack

/-! A jointly generic three-row stack and its two-row prefix. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option maxHeartbeats 800000

def depthThreeRowDegree {m : Type*} : (m ⊕ m) ⊕ m → ℕ :=
  Sum.elim depthTwoRowDegree (fun _ => 3)

abbrev DepthThreeStackField (K n m : Type*) [Field K] :=
  PrescribedMatrixField K n (depthThreeRowDegree (m := m))

def genericDepthThreeStack (K n m : Type*) [Field K] :
    Matrix ((m ⊕ m) ⊕ m) n (DepthThreeStackField K n m)[X] :=
  genericPrescribedMatrix K n depthThreeRowDegree

def genericDepthThreePrefix (K n m : Type*) [Field K] :
    Matrix (m ⊕ m) n (DepthThreeStackField K n m)[X] :=
  (genericDepthThreeStack K n m).submatrix Sum.inl id

variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
theorem genericDepthThreeStack_sum_degree :
    ∑ i : (m ⊕ m) ⊕ m, depthThreeRowDegree i = 6*Fintype.card m := by
  simp [depthThreeRowDegree,depthTwoRowDegree,Fintype.sum_sum_type]
  omega

theorem genericDepthThreeStack_hilbert
    (hmn : 3*Fintype.card m < Fintype.card n) (d : ℕ) :
    Module.finrank (DepthThreeStackField K n m)
      (polynomialKernelAtDegree (genericDepthThreeStack K n m) d) =
      (Fintype.card n-3*Fintype.card m)*(d+1)-6*Fintype.card m := by
  have hh := generic_prescribed_kernel_hilbert (K := K) (n := n)
    (depthThreeRowDegree (m := m)) (by simp only [Fintype.card_sum]; omega) d
  simpa only [genericDepthThreeStack,Fintype.card_sum,genericDepthThreeStack_sum_degree,
    show Fintype.card m+Fintype.card m+Fintype.card m=3*Fintype.card m by omega] using hh

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
theorem genericDepthThreePrefix_degree (i : m ⊕ m) (x : n) :
    (genericDepthThreePrefix K n m i x).natDegree ≤ depthTwoRowDegree i :=
  genericPrescribedMatrix_degree depthThreeRowDegree (Sum.inl i) x

theorem genericDepthThreePrefix_hilbert
    (hmn : 2*Fintype.card m < Fintype.card n) (d : ℕ) :
    Module.finrank (DepthThreeStackField K n m)
      (polynomialKernelAtDegree (genericDepthThreePrefix K n m) d) =
      (Fintype.card n-2*Fintype.card m)*(d+1)-3*Fintype.card m := by
  let f : m ⊕ m ↪ (m ⊕ m) ⊕ m := ⟨Sum.inl,Sum.inl_injective⟩
  have hh := generic_prescribed_submatrix_kernel_hilbert (K := K) (n := n)
    (depthThreeRowDegree (m := m)) f (by simp only [Fintype.card_sum]; omega) d
  change Module.finrank (DepthThreeStackField K n m)
    (polynomialKernelAtDegree (genericDepthThreePrefix K n m) d) =
    (Fintype.card n-Fintype.card (m ⊕ m))*(d+1)-∑ i,depthTwoRowDegree i at hh
  simpa only [Fintype.card_sum,genericDepthTwoStack_sum_degree,two_mul] using hh

theorem genericDepthThreePrefix_minimal_degrees
    (hmn : 2*Fintype.card m < Fintype.card n) :
    HasMinimalKernelDegrees (genericDepthThreePrefix K n m)
      (balancedDegreeList (3*Fintype.card m) (Fintype.card n-2*Fintype.card m)) := by
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [genericDepthThreePrefix_hilbert hmn d,balancedDegreeList_hilbert _ _ d (by omega)]

theorem genericDepthThreePrefix_right_inverse
    (hmn : 2*Fintype.card m < Fintype.card n) :
    ∃ R : Matrix n (m ⊕ m) (DepthThreeStackField K n m)[X],
      DegreeBound R (3*Fintype.card m) ∧ genericDepthThreePrefix K n m*R=1 := by
  apply weighted_right_inverse_of_coefficient_surjective
    (genericDepthThreePrefix K n m) depthTwoRowDegree
    (3*Fintype.card m) (genericDepthThreePrefix_degree (K := K))
  apply column_coefficient_surjective_of_kernel_hilbert
    (genericDepthThreePrefix K n m).transpose depthTwoRowDegree (3*Fintype.card m)
    (fun j i => genericDepthThreePrefix_degree i j) (by simp only [Fintype.card_sum]; omega)
  · rw [genericDepthTwoStack_sum_degree]
    simp only [Fintype.card_sum]
    have hr : 1 ≤ Fintype.card n-(Fintype.card m+Fintype.card m) := by omega
    nlinarith
  · rw [Matrix.transpose_transpose,genericDepthThreePrefix_hilbert hmn,
      genericDepthTwoStack_sum_degree]
    simp only [Fintype.card_sum,two_mul]

theorem genericDepthThreePrefix_row_leading_injective
    (hmn : 3*Fintype.card m ≤ Fintype.card n) :
    Function.Injective (Matrix.mulVec (fun x i =>
      (genericDepthThreePrefix K n m i x).coeff (depthTwoRowDegree i))) := by
  let A : Matrix n ((m ⊕ m) ⊕ m) (DepthThreeStackField K n m) :=
    fun x i => (genericDepthThreeStack K n m i x).coeff (depthThreeRowDegree i)
  have hA : Function.Injective A.mulVec :=
    generic_prescribed_row_leading_injective depthThreeRowDegree
      (by simp only [Fintype.card_sum]; omega)
  intro z w h
  have hh : A *ᵥ Sum.elim z (fun _ => 0) = A *ᵥ Sum.elim w (fun _ => 0) := by
    funext x
    simpa only [A,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
      mul_zero,Finset.sum_const_zero,add_zero,depthThreeRowDegree,
      genericDepthThreePrefix,Matrix.submatrix_apply,id_eq] using congrFun h x
  have he := hA hh
  funext i
  exact congrFun he (Sum.inl i)

theorem genericDepthThreePrefix_first_coefficient_surjective
    (hmn : 2*Fintype.card m < Fintype.card n) :
    Function.Surjective (weightedCoefficientMatrix
      ((genericDepthThreePrefix K n m).submatrix Sum.inl id)
      (fun _ => 1) (fun _ => 2)).mulVec := by
  let P := (genericDepthThreePrefix K n m).submatrix Sum.inl id
  let f : m ↪ (m ⊕ m) ⊕ m := ⟨fun i => Sum.inl (Sum.inl i),
    fun _ _ h => Sum.inl_injective (Sum.inl_injective h)⟩
  have hP : DegreeBound P 1 := fun i j => genericDepthThreePrefix_degree (Sum.inl i) j
  apply column_coefficient_surjective_of_kernel_hilbert P.transpose (fun _ => 1) 1
    (fun j i => hP i j) (by omega)
  · simp
    omega
  · have hh := generic_prescribed_submatrix_kernel_hilbert (K := K) (n := n)
      (depthThreeRowDegree (m := m)) f (by omega) 1
    simpa [P,genericDepthThreePrefix,genericDepthThreeStack,f,depthThreeRowDegree,
      depthTwoRowDegree] using hh

theorem genericDepthThreePrefix_column_coefficient_surjective
    (hmn : 2*Fintype.card m < Fintype.card n)
    {k : ℕ} (a : Fin k → ℕ)
    (ha : (List.ofFn a).Perm
      (balancedDegreeList (3*Fintype.card m) (Fintype.card n-2*Fintype.card m)))
    (j : Fin k) :
    Function.Surjective (weightedCoefficientMatrix (genericDepthThreePrefix K n m)
      (fun _ => a j+1) (fun i => a j+1+depthTwoRowDegree i)).mulVec := by
  apply column_coefficient_surjective_of_kernel_hilbert
    (genericDepthThreePrefix K n m).transpose depthTwoRowDegree (a j+1)
    (fun y i => genericDepthThreePrefix_degree i y) (by simp only [Fintype.card_sum]; omega)
  · rw [genericDepthTwoStack_sum_degree]
    simp only [Fintype.card_sum,← two_mul]
    let S := 3*Fintype.card m
    let r := Fintype.card n-2*Fintype.card m
    have hr : 0 < r := by dsimp [r]; omega
    have hj := ha.mem_iff.mp (List.mem_ofFn.mpr ⟨j,rfl⟩)
    have hlow : S/r ≤ a j := by
      simp only [balancedDegreeList,List.mem_append,List.mem_replicate] at hj
      rcases hj with ⟨_,h⟩ | ⟨_,h⟩ <;> dsimp [S,r] <;> omega
    have hmod := Nat.mod_lt S hr
    have hdiv := Nat.mod_add_div S r
    have hmul := Nat.mul_le_mul_left r hlow
    change S ≤ r*(a j+1+1)
    nlinarith
  · rw [Matrix.transpose_transpose,genericDepthThreePrefix_hilbert hmn,
      genericDepthTwoStack_sum_degree]
    simp only [Fintype.card_sum,two_mul]

theorem genericDepthThreePrefix_basis_data
    (hmn : 2*Fintype.card m < Fintype.card n) :
    ∃ (B : Basis (Fin (Fintype.card n-2*Fintype.card m))
        (DepthThreeStackField K n m)[X]
        (LinearMap.ker (Matrix.toLin' (genericDepthThreePrefix K n m))))
      (a : Fin (Fintype.card n-2*Fintype.card m) → ℕ),
      (∀ x j, (polynomialKernelBasisMatrix (genericDepthThreePrefix K n m) B x j).natDegree ≤ a j) ∧
      Function.Injective (Matrix.mulVec (fun x j =>
        (polynomialKernelBasisMatrix (genericDepthThreePrefix K n m) B x j).coeff (a j))) ∧
      (List.ofFn a).Perm
        (balancedDegreeList (3*Fintype.card m) (Fintype.card n-2*Fintype.card m)) ∧
      (∑ j, a j) = 3*Fintype.card m ∧
      Fintype.card m + ∑ j, (a j+2) = 2*Fintype.card n := by
  obtain ⟨k,B,a,hV,hlead,ha⟩ := genericDepthThreePrefix_minimal_degrees (K := K) hmn
  obtain ⟨hk,hsum,_⟩ := balancedDegreeList_ofFn_properties a _ _ (by omega) ha
  subst k
  refine ⟨B,a,hV,hlead,ha,hsum,?_⟩
  simp only [Finset.sum_add_distrib,hsum,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul]
  omega

end FD56

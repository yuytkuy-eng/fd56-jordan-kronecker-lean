/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthTwoRowLifting
import FD56.Hilbert.DepthTwoAffineLift
import FD56.Hilbert.GenericPrescribedMatrix
import FD56.Hilbert.BalancedDegrees

/-! Independent linear and quadratic rows provide the depth-two stack data. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

omit [Fintype m] [DecidableEq n] in
theorem weighted_right_inverse_of_coefficient_surjective
    (P : Matrix m n K[X]) (e : m → ℕ) (d : ℕ)
    (hP : ∀ i j, (P i j).natDegree ≤ e i)
    (hs : Function.Surjective
      (weightedCoefficientMatrix P (fun _ => d) (fun i => d+e i)).mulVec) :
    ∃ R : Matrix n m K[X], DegreeBound R d ∧ P*R = 1 := by
  classical
  have hlift (j : m) : ∃ v : n → K[X], (∀ x, (v x).natDegree ≤ d) ∧
      P *ᵥ v = fun i => if i=j then 1 else 0 := by
    apply weighted_coefficient_surjective_lift P (fun _ => d) (fun i => d+e i)
      (fun i x => by have := hP i x; dsimp; omega) hs
    intro i
    split_ifs <;> simp
  choose v hv he using hlift
  refine ⟨fun x j => v j x,fun x j => hv j x,?_⟩
  funext i j
  simpa only [Matrix.mul_apply,Matrix.mulVec,dotProduct,Matrix.one_apply] using congrFun (he j) i

theorem generic_prescribed_row_leading_injective (e : m → ℕ)
    (hmn : Fintype.card m ≤ Fintype.card n) :
    Function.Injective (Matrix.mulVec (fun x i =>
      (genericPrescribedMatrix K n e i x).coeff (e i))) := by
  classical
  let f : m ↪ n := (Function.Embedding.nonempty_of_card_le hmn).some
  let W : Matrix m n K[X] := fun i x => Polynomial.monomial (e i) (if f i=x then 1 else 0)
  have hW : ∀ i x, (W i x).natDegree ≤ e i := by
    intro i x
    exact Polynomial.natDegree_monomial_le (if f i=x then (1 : K) else 0)
  let ψ := prescribedMatrixSpecialization e (RingHom.id K) W
  let φ := algebraMap (MvPolynomial (PrescribedMatrixParameters n e) K) (PrescribedMatrixField K n e)
  let A : Matrix n m (MvPolynomial (PrescribedMatrixParameters n e) K) :=
    fun x i => (universalPrescribedMatrix K n e i x).coeff (e i)
  have hAe : A.map ψ = (show Matrix n m K from fun x i => (W i x).coeff (e i)) := by
    have hh := universalPrescribedMatrix_specialization e (RingHom.id K) W hW
    funext x i
    have h := congrArg (fun P : Matrix m n K[X] => (P i x).coeff (e i)) hh
    simpa only [A,Matrix.map_apply,Polynomial.coe_mapRingHom,Polynomial.coeff_map] using h
  have hAg : A.map φ = (show Matrix n m (PrescribedMatrixField K n e) from
      fun x i => (genericPrescribedMatrix K n e i x).coeff (e i)) := by
    funext x i
    simp only [A,φ,Matrix.map_apply,genericPrescribedMatrix,
      Polynomial.coe_mapRingHom,Polynomial.coeff_map]
  have hAi : Function.Injective (A.map ψ).mulVec := by
    rw [hAe]
    intro z w h
    funext i
    have hh := congrFun h (f i)
    simpa [Matrix.mulVec,dotProduct,W,f.injective.eq_iff] using hh
  have hi := matrix_injective_of_field_specialization ψ φ (IsFractionRing.injective _ _) A hAi
  rw [hAg] at hi
  exact hi

abbrev DepthTwoStackField (K n m : Type*) [Field K] :=
  PrescribedMatrixField K n (depthTwoRowDegree (m := m))

def genericDepthTwoStack (K n m : Type*) [Field K] :
    Matrix (m ⊕ m) n (DepthTwoStackField K n m)[X] :=
  genericPrescribedMatrix K n depthTwoRowDegree

omit [DecidableEq m] in
theorem genericDepthTwoStack_sum_degree :
    ∑ i : m ⊕ m, depthTwoRowDegree i = 3*Fintype.card m := by
  simp [depthTwoRowDegree,Fintype.sum_sum_type]
  omega

theorem genericDepthTwoStack_minimal_degrees
    (hmn : 2*Fintype.card m < Fintype.card n) :
    HasMinimalKernelDegrees (genericDepthTwoStack K n m)
      (balancedDegreeList (3*Fintype.card m) (Fintype.card n-2*Fintype.card m)) := by
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [balancedDegreeList_hilbert _ _ d (by omega)]
  have h := generic_prescribed_kernel_hilbert (K := K) (n := n)
    (depthTwoRowDegree (m := m)) (by simpa only [Fintype.card_sum,← two_mul] using hmn) d
  simpa only [genericDepthTwoStack,Fintype.card_sum,genericDepthTwoStack_sum_degree,
    two_mul] using h

theorem genericDepthTwoStack_right_inverse
    (hmn : 2*Fintype.card m < Fintype.card n) :
    ∃ R : Matrix n (m ⊕ m) (DepthTwoStackField K n m)[X],
      DegreeBound R (3*Fintype.card m) ∧ genericDepthTwoStack K n m*R = 1 := by
  apply weighted_right_inverse_of_coefficient_surjective
    (genericDepthTwoStack K n m) depthTwoRowDegree
    (3*Fintype.card m) (genericPrescribedMatrix_degree depthTwoRowDegree)
  apply generic_prescribed_coefficient_surjective depthTwoRowDegree
    (by simpa only [Fintype.card_sum,← two_mul] using hmn)
  rw [genericDepthTwoStack_sum_degree]
  simp only [Fintype.card_sum]
  have hr : 1 ≤ Fintype.card n-(Fintype.card m+Fintype.card m) := by omega
  nlinarith

theorem genericDepthTwoStack_row_leading_injective
    (hmn : 2*Fintype.card m ≤ Fintype.card n) :
    Function.Injective (Matrix.mulVec (fun x i =>
      (genericDepthTwoStack K n m i x).coeff (depthTwoRowDegree i))) :=
  generic_prescribed_row_leading_injective _
    (by simpa only [Fintype.card_sum,← two_mul] using hmn)

theorem genericDepthTwoStack_first_coefficient_surjective
    (hmn : 2*Fintype.card m < Fintype.card n) :
    Function.Surjective (weightedCoefficientMatrix
      ((genericDepthTwoStack K n m).submatrix Sum.inl id)
      (fun _ => 1) (fun _ => 2)).mulVec := by
  let P := (genericDepthTwoStack K n m).submatrix Sum.inl id
  let f : m ↪ m ⊕ m := ⟨Sum.inl,Sum.inl_injective⟩
  have hP : DegreeBound P 1 := fun i j => genericPrescribedMatrix_degree _ (Sum.inl i) j
  apply column_coefficient_surjective_of_kernel_hilbert P.transpose (fun _ => 1) 1
    (fun j i => hP i j) (by omega)
  · simp
    omega
  · have h := generic_prescribed_submatrix_kernel_hilbert (K := K) (n := n)
      (depthTwoRowDegree (m := m)) f (by omega) 1
    simpa [P,genericDepthTwoStack,f,depthTwoRowDegree] using h

theorem genericDepthTwoStack_column_coefficient_surjective
    (hmn : 2*Fintype.card m < Fintype.card n)
    {k : ℕ} (a : Fin k → ℕ)
    (ha : (List.ofFn a).Perm
      (balancedDegreeList (3*Fintype.card m) (Fintype.card n-2*Fintype.card m)))
    (j : Fin k) :
    Function.Surjective (weightedCoefficientMatrix (genericDepthTwoStack K n m)
      (fun _ => a j+1) (fun i => a j+1+depthTwoRowDegree i)).mulVec := by
  apply generic_prescribed_coefficient_surjective depthTwoRowDegree
    (by simpa only [Fintype.card_sum,← two_mul] using hmn)
  rw [genericDepthTwoStack_sum_degree]
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

theorem genericDepthTwoStack_basis_data
    (hmn : 2*Fintype.card m < Fintype.card n) :
    ∃ (B : Basis (Fin (Fintype.card n-2*Fintype.card m))
        (DepthTwoStackField K n m)[X]
        (LinearMap.ker (Matrix.toLin' (genericDepthTwoStack K n m))))
      (a : Fin (Fintype.card n-2*Fintype.card m) → ℕ),
      (∀ x j, (polynomialKernelBasisMatrix (genericDepthTwoStack K n m) B x j).natDegree ≤ a j) ∧
      Function.Injective (Matrix.mulVec (fun x j =>
        (polynomialKernelBasisMatrix (genericDepthTwoStack K n m) B x j).coeff (a j))) ∧
      (List.ofFn a).Perm
        (balancedDegreeList (3*Fintype.card m) (Fintype.card n-2*Fintype.card m)) ∧
      (∑ j, a j) = 3*Fintype.card m ∧
      Fintype.card m + ∑ j, (a j+2) = 2*Fintype.card n := by
  obtain ⟨k,B,a,hV,hlead,ha⟩ := genericDepthTwoStack_minimal_degrees (K := K) hmn
  obtain ⟨hk,hsum,_⟩ := balancedDegreeList_ofFn_properties a _ _ (by omega) ha
  subst k
  refine ⟨B,a,hV,hlead,ha,hsum,?_⟩
  simp only [Finset.sum_add_distrib, hsum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  omega

theorem depthTwo_balanced_affine_coefficient_surjective
    (P Q : Matrix m n K[X])
    {k : ℕ} (B : Basis (Fin k) K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P Q))))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P Q * R = 1)
    (hP : DegreeBound P 1) (hQ : DegreeBound Q 2)
    (hlead : Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P Q i x).coeff (depthTwoRowDegree i))))
    (hmn : 2*Fintype.card m < Fintype.card n) (a : Fin k → ℕ)
    (hV : ∀ x j, (polynomialKernelBasisMatrix (depthTwoStack P Q) B x j).natDegree ≤ a j)
    (ha : (List.ofFn a).Perm
      (balancedDegreeList (3*Fintype.card m) (Fintype.card n-2*Fintype.card m))) :
    Function.Surjective (weightedCoefficientMatrix
      (polynomialKernelBasisMatrix (depthTwoStack P Q) B).transpose
      (fun _ => 1) (fun j => a j+1)).mulVec := by
  obtain ⟨hk,hsum,_⟩ := balancedDegreeList_ofFn_properties a _ _ (by omega) ha
  apply depthTwo_affine_coefficient_surjective P Q B R hR hP hQ hlead a hV
  simp only [Finset.sum_add_distrib, hsum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, hk]
  omega

end FD56

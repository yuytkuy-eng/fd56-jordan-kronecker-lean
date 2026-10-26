/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.RegularPoleSeparation
import FD56.Hilbert.PairedCouplingCongruence

/-! A constant shear removes the coupling between the trace hyperplane and
the simple regular summands at distinct poles. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {R n r : Type*} [CommRing R] [Fintype n] [DecidableEq n]

def allOnesMatrix (n : Type*) (R : Type*) [One R] : Matrix n n R := fun _ _ => 1

omit [DecidableEq n] in
theorem transpose_mul_allOnes_zero (E : Matrix n r R) (hE : ∀ j, ∑ i, E i j=0) :
    E.transpose*allOnesMatrix n R=0 := by
  ext i j
  simpa [Matrix.mul_apply,allOnesMatrix] using hE i

theorem doublePoleCross_shear (D C : Matrix n n R) :
    (lowerBlockShift (-C.transpose)).transpose * Matrix.fromBlocks D 1 0 D *
        (lowerBlockShift C.transpose).transpose =
      Matrix.fromBlocks D (1+D*C-C*D) 0 D := by
  simp only [lowerBlockShift,Matrix.fromBlocks_transpose,Matrix.transpose_one,
    Matrix.transpose_zero,Matrix.transpose_neg,Matrix.transpose_transpose,
    Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,
    Matrix.one_mul,Matrix.mul_one,Matrix.neg_mul,Matrix.mul_neg]
  abel_nf

def skewCrossMatrix {p q : Type*} (A : Matrix p q R) : Matrix (p ⊕ q) (p ⊕ q) R :=
  Matrix.fromBlocks 0 A (-A.transpose) 0

omit [DecidableEq n] in
theorem skewCross_pairedCoordinateChange (Q S A : Matrix n n R) :
    (pairedCoordinateChange Q S).transpose * skewCrossMatrix A * pairedCoordinateChange Q S =
      skewCrossMatrix (Q.transpose*A*S.transpose) := by
  simp only [pairedCoordinateChange,skewCrossMatrix,Matrix.fromBlocks_transpose,
    Matrix.transpose_zero,Matrix.transpose_transpose,Matrix.fromBlocks_multiply,
    Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,Matrix.mul_neg,Matrix.neg_mul,
    Matrix.transpose_mul,neg_zero]
  simp only [Matrix.mul_assoc]

def doublePoleAlternatingShear (C : Matrix n n R) :
    Matrix ((n ⊕ n) ⊕ (n ⊕ n)) ((n ⊕ n) ⊕ (n ⊕ n)) R :=
  pairedCoordinateChange (lowerBlockShift (-C.transpose)) (lowerBlockShift C.transpose)

theorem doublePoleAlternatingShear_inverse (C : Matrix n n R) :
    doublePoleAlternatingShear C*doublePoleAlternatingShear (-C)=1 := by
  have h : lowerBlockShift (-C.transpose)*lowerBlockShift C.transpose=1 := by
    simpa only [neg_neg] using lowerBlockShift_inverse (-C.transpose)
  simpa only [doublePoleAlternatingShear,Matrix.transpose_neg,neg_neg] using
    pairedCoordinateChange_inverse (lowerBlockShift (-C.transpose)) (lowerBlockShift C.transpose) h

theorem doublePoleAlternatingShear_congruence (D C : Matrix n n R) :
    (doublePoleAlternatingShear C).transpose * skewCrossMatrix (Matrix.fromBlocks D 1 0 D) *
        doublePoleAlternatingShear C = skewCrossMatrix (Matrix.fromBlocks D (1+D*C-C*D) 0 D) := by
  rw [doublePoleAlternatingShear,skewCross_pairedCoordinateChange,doublePoleCross_shear]

omit [Fintype n] in
theorem doublePoleAlternatingShear_map {L : Type*} [CommRing L] (f : R →+* L) (C : Matrix n n R) :
    (doublePoleAlternatingShear C).map f = doublePoleAlternatingShear (C.map f) := by
  ext i j
  rcases i with (i|i) | (i|i) <;> rcases j with (j|j) | (j|j) <;>
    simp [doublePoleAlternatingShear,pairedCoordinateChange,lowerBlockShift,Matrix.one_apply]

theorem doublePoleAlternatingShear_trace_coordinate (C : Matrix n n R)
    (v : ((n ⊕ n) ⊕ (n ⊕ n)) → R) (i : n) :
    (doublePoleAlternatingShear C *ᵥ v) (.inl (.inl i)) = v (.inl (.inl i)) := by
  simp [doublePoleAlternatingShear,pairedCoordinateChange,lowerBlockShift,Matrix.fromBlocks_mulVec]

theorem skewCross_restrict_first (E : Matrix n r R) (A : Matrix n n R) :
    (Matrix.fromBlocks E 0 0 (1 : Matrix n n R)).transpose * skewCrossMatrix A *
        Matrix.fromBlocks E 0 0 (1 : Matrix n n R) = skewCrossMatrix (E.transpose*A) := by
  simp only [skewCrossMatrix,Matrix.fromBlocks_transpose,Matrix.transpose_zero,
    Matrix.transpose_one,Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,
    zero_add,add_zero,Matrix.mul_one,Matrix.one_mul,Matrix.mul_neg,Matrix.neg_mul,
    Matrix.transpose_mul,Matrix.transpose_transpose,neg_zero]

variable {K : Type*} [Field K]

def distinctPoleCorrection (lam : n → K) : Matrix n n K :=
  fun i j => if i=j then 0 else (lam j-lam i)⁻¹

omit [Fintype n] in
theorem distinctPoleCorrection_entry (lam : n → K) (hlam : Function.Injective lam) (i j : n) :
    (if i=j then 1 else 0)+(lam j-lam i)*distinctPoleCorrection lam i j=1 := by
  by_cases hij : i=j
  · simp [distinctPoleCorrection,hij]
  · have hdiff : lam j-lam i≠0 := sub_ne_zero.mpr (hlam.ne (Ne.symm hij))
    simp [distinctPoleCorrection,hij,hdiff]

theorem distinctPoleCorrection_polynomial (lam : n → K) (hlam : Function.Injective lam) :
    (1 : Matrix n n K[X]) + regularPoleDiagonal lam*(distinctPoleCorrection lam).map C -
      (distinctPoleCorrection lam).map C*regularPoleDiagonal lam = allOnesMatrix n K[X] := by
  funext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,regularPoleDiagonal,Matrix.diagonal_mul,
    Matrix.mul_diagonal,Matrix.map_apply,allOnesMatrix]
  have h := congrArg (C : K →+* K[X]) (distinctPoleCorrection_entry lam hlam i j)
  simp only [map_add,map_mul,map_sub,map_one] at h
  have hi : C (if i=j then (1:K) else 0) = (1 : Matrix n n K[X]) i j := by
    by_cases hij : i=j <;> simp [Matrix.one_apply,hij]
  rw [hi] at h
  linear_combination h

theorem distinctPole_double_cross_shear (lam : n → K) (hlam : Function.Injective lam) :
    (lowerBlockShift (-((distinctPoleCorrection lam).map C).transpose)).transpose *
        Matrix.fromBlocks (regularPoleDiagonal lam) 1 0 (regularPoleDiagonal lam) *
        (lowerBlockShift ((distinctPoleCorrection lam).map C).transpose).transpose =
      Matrix.fromBlocks (regularPoleDiagonal lam) (allOnesMatrix n K[X]) 0 (regularPoleDiagonal lam) := by
  rw [doublePoleCross_shear,distinctPoleCorrection_polynomial lam hlam]

theorem distinctPole_alternating_constant_shear (lam : n → K) (hlam : Function.Injective lam) :
    ∃ T S : Matrix ((n ⊕ n) ⊕ (n ⊕ n)) ((n ⊕ n) ⊕ (n ⊕ n)) K,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose *
          skewCrossMatrix (Matrix.fromBlocks (regularPoleDiagonal lam) 1 0 (regularPoleDiagonal lam)) *
          T.map C =
        skewCrossMatrix (Matrix.fromBlocks (regularPoleDiagonal lam) (allOnesMatrix n K[X])
          0 (regularPoleDiagonal lam)) ∧
      (∀ (v : ((n ⊕ n) ⊕ (n ⊕ n)) → K) i, (T*ᵥv) (.inl (.inl i))=v (.inl (.inl i))) := by
  let Z := distinctPoleCorrection lam
  refine ⟨doublePoleAlternatingShear Z,doublePoleAlternatingShear (-Z),
    doublePoleAlternatingShear_inverse Z,?_,?_,doublePoleAlternatingShear_trace_coordinate Z⟩
  · simpa only [neg_neg] using doublePoleAlternatingShear_inverse (-Z)
  · rw [doublePoleAlternatingShear_map,doublePoleAlternatingShear_congruence,
      distinctPoleCorrection_polynomial lam hlam]

theorem distinctPole_hyperplane_cross
    (lam : n → K) (E : Matrix n r K) (hE : ∀ j, ∑ i, E i j=0) :
    (Matrix.fromBlocks (E.map C) 0 0 (1 : Matrix n n K[X])).transpose *
        Matrix.fromBlocks (regularPoleDiagonal lam) (allOnesMatrix n K[X]) 0 (regularPoleDiagonal lam) =
      Matrix.fromBlocks ((E.map C).transpose*regularPoleDiagonal lam) 0 0 (regularPoleDiagonal lam) := by
  have hE' : ∀ j, ∑ i, (E.map C) i j=0 := by
    intro j
    simpa only [map_sum,map_zero] using congrArg (C : K →+* K[X]) (hE j)
  simp only [Matrix.fromBlocks_transpose,Matrix.transpose_zero,Matrix.transpose_one,
    Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,
    Matrix.one_mul,transpose_mul_allOnes_zero _ hE']

end FD56

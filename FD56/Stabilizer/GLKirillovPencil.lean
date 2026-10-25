/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GLMatrix
import FD56.Hilbert.MinimalProfile
import FD56.Stabilizer.Kirillov

/-! The GL equation matrix becomes the alternating Kirillov pencil by a constant row permutation. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

/-- Match equation outputs with the trace-dual coordinates of the GL semidirect product. -/
def glTraceDualIndexEquiv (n m : Type*) : SLInput n m ≃ ((m × n) ⊕ (n × n)) where
  toFun := Sum.elim (fun ij => Sum.inr (ij.2, ij.1)) (fun ij => Sum.inl (ij.2, ij.1))
  invFun := Sum.elim (fun ij => Sum.inr (ij.2, ij.1)) (fun ij => Sum.inl (ij.2, ij.1))
  left_inv i := by cases i <;> rfl
  right_inv i := by cases i <;> rfl

variable {R n m : Type*} [CommRing R] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

/-- Our convention is `wᵀ H z = kirillov(z,w)`. -/
def glKirillovMatrix (M : Matrix n n R) (P : Matrix m n R) :
    Matrix (SLInput n m) (SLInput n m) R :=
  (glEquationMatrix M P).submatrix (glTraceDualIndexEquiv n m) id

theorem glKirillovMatrix_mulVec (M : Matrix n n R) (P : Matrix m n R)
    (z : SLInput n m → R) :
    glKirillovMatrix M P *ᵥ z =
      Sum.elim (fun ij => stabilizerResidual M P (matrixPairEquiv R R n m z) ij.2 ij.1)
        (fun ij => (P * (matrixPairEquiv R R n m z).1) ij.2 ij.1) := by
  funext i
  change (glEquationMatrix M P *ᵥ z) (glTraceDualIndexEquiv n m i) = _
  rw [← Matrix.toLin'_apply, glEquationMatrix, Matrix.toLin'_toMatrix']
  cases i <;> rfl

theorem glKirillovMatrix_pairing_equations (M : Matrix n n R) (P : Matrix m n R)
    (z w : SLInput n m → R) :
    w ⬝ᵥ (glKirillovMatrix M P *ᵥ z) =
      Matrix.trace (stabilizerResidual M P (matrixPairEquiv R R n m z) *
        (matrixPairEquiv R R n m w).1) +
      Matrix.trace ((P * (matrixPairEquiv R R n m z).1) *
        (matrixPairEquiv R R n m w).2) := by
  rw [glKirillovMatrix_mulVec]
  simp only [dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl,
    Sum.elim_inr, Matrix.trace, Matrix.diag, Matrix.mul_apply, matrixPairEquiv]
  congr 1 <;> rw [Finset.sum_comm] <;>
    apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> exact mul_comm _ _

/-- The pairing is alternating over every commutative ring, including characteristic two. -/
theorem glKirillovMatrix_alternating (M : Matrix n n R) (P : Matrix m n R)
    (z : SLInput n m → R) : z ⬝ᵥ (glKirillovMatrix M P *ᵥ z) = 0 := by
  rw [glKirillovMatrix_pairing_equations]
  let X := (matrixPairEquiv R R n m z).1
  let U := (matrixPairEquiv R R n m z).2
  change Matrix.trace ((M * X - X * M - U * P) * X) + Matrix.trace ((P * X) * U) = 0
  simp only [Matrix.sub_mul, Matrix.trace_sub]
  rw [Matrix.trace_mul_cycle M X X, Matrix.trace_mul_cycle U P X,
    Matrix.trace_mul_cycle X U P]
  ring

theorem glKirillovMatrix_diag_zero (M : Matrix n n R) (P : Matrix m n R)
    (i : SLInput n m) : glKirillovMatrix M P i i = 0 := by
  simpa only [Matrix.mulVec_single_one, single_dotProduct, one_mul] using
    glKirillovMatrix_alternating M P (Pi.single i 1)

theorem glKirillovMatrix_skew (M : Matrix n n R) (P : Matrix m n R) :
    (glKirillovMatrix M P).transpose = -glKirillovMatrix M P := by
  have hpair (z w : SLInput n m → R) :
      z ⬝ᵥ (glKirillovMatrix M P *ᵥ w) + w ⬝ᵥ (glKirillovMatrix M P *ᵥ z) = 0 := by
    have h := glKirillovMatrix_alternating M P (z + w)
    simpa only [Matrix.mulVec_add, add_dotProduct, dotProduct_add,
      glKirillovMatrix_alternating, zero_add, add_zero, add_comm] using h
  ext i j
  have h := hpair (Pi.single j 1) (Pi.single i 1)
  simp only [Matrix.mulVec_single_one, single_dotProduct, one_mul] at h
  exact eq_neg_of_add_eq_zero_left h

theorem glKirillovMatrix_kernel_iff (M : Matrix n n R) (P : Matrix m n R)
    (z : SLInput n m → R) :
    glKirillovMatrix M P *ᵥ z = 0 ↔ glEquationMatrix M P *ᵥ z = 0 := by
  constructor
  · intro h
    funext i
    have hi := congrFun h ((glTraceDualIndexEquiv n m).symm i)
    change (glEquationMatrix M P *ᵥ z)
      (glTraceDualIndexEquiv n m ((glTraceDualIndexEquiv n m).symm i)) = 0 at hi
    simpa only [Equiv.apply_symm_apply] using hi
  · intro h
    funext i
    exact congrFun h (glTraceDualIndexEquiv n m i)

section Polynomial
variable {K : Type*} [Field K]

theorem glKirillovMatrix_pairing (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (z w : SLInput n m → K[X]) :
    w ⬝ᵥ (glKirillovMatrix M P *ᵥ z) =
      kirillov M P (matrixPairEquiv K[X] K[X] n m z).1
        (matrixPairEquiv K[X] K[X] n m z).2 (matrixPairEquiv K[X] K[X] n m w).1
        (matrixPairEquiv K[X] K[X] n m w).2 := by
  rw [glKirillovMatrix_pairing_equations, kirillov_equations]
  rfl

theorem glKirillovMatrix_coefficient_diag_zero (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (k : ℕ) (i : SLInput n m) :
    (glKirillovMatrix M P i i).coeff k = 0 := by
  rw [glKirillovMatrix_diag_zero, Polynomial.coeff_zero]

theorem glKirillovMatrix_coefficient_skew (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (k : ℕ) :
    Matrix.transpose (fun i j => (glKirillovMatrix M P i j).coeff k) =
      -(fun i j => (glKirillovMatrix M P i j).coeff k) := by
  ext i j
  have h := congrArg (fun A => (A i j).coeff k) (glKirillovMatrix_skew M P)
  simpa only [Matrix.transpose_apply, Matrix.neg_apply, Polynomial.coeff_neg] using h

theorem glKirillovMatrix_coefficient_alternating (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (k : ℕ) (z : SLInput n m → K) :
    z ⬝ᵥ ((fun i j => (glKirillovMatrix M P i j).coeff k) *ᵥ z) = 0 := by
  have h := congrArg (fun p : K[X] => p.coeff k)
    (glKirillovMatrix_alternating M P (fun i => Polynomial.C (z i)))
  simpa only [dotProduct, Matrix.mulVec, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_zero] using h

/-- The coordinate conversion preserves every polynomial entry degree bound. -/
theorem glKirillovMatrix_degreeBound (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (d : ℕ) (hM : DegreeBound M d) (hP : DegreeBound P d) :
    DegreeBound (glKirillovMatrix M P) d := by
  intro i j
  let z : SLInput n m → K[X] := Pi.single j 1
  let X := (matrixPairEquiv K[X] K[X] n m z).1
  let U := (matrixPairEquiv K[X] K[X] n m z).2
  have hz : ∀ k, (z k).natDegree ≤ 0 := by
    intro k
    by_cases hk : k = j <;> simp [z, hk, Pi.single_apply]
  have hX : DegreeBound X 0 := fun a b => hz (Sum.inl (a, b))
  have hU : DegreeBound U 0 := fun a b => hz (Sum.inr (a, b))
  have hMX : DegreeBound (M * X) d := by simpa using degreeBound_mul hM hX
  have hXM : DegreeBound (X * M) d := by simpa using degreeBound_mul hX hM
  have hUP : DegreeBound (U * P) d := by simpa using degreeBound_mul hU hP
  have hPX : DegreeBound (P * X) d := by simpa using degreeBound_mul hP hX
  have he := congrFun (glKirillovMatrix_mulVec M P z) i
  change (glKirillovMatrix M P *ᵥ Pi.single j 1) i = _ at he
  rw [Matrix.mulVec_single_one] at he
  simp only [Matrix.transpose_apply] at he
  rw [he]
  cases i with
  | inl ab => exact (degreeBound_sub (degreeBound_sub hMX hXM) hUP) ab.2 ab.1
  | inr ab => exact hPX ab.2 ab.1

theorem glKirillovMatrix_polynomialKernel (M : Matrix n n K[X])
    (P : Matrix m n K[X]) :
    LinearMap.ker (Matrix.toLin' (glKirillovMatrix M P)) =
      LinearMap.ker (Matrix.toLin' (glEquationMatrix M P)) := by
  ext z
  exact glKirillovMatrix_kernel_iff M P z

theorem glKirillovMatrix_polynomialKernelAtDegree (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (d : ℕ) :
    polynomialKernelAtDegree (glKirillovMatrix M P) d =
      polynomialKernelAtDegree (glEquationMatrix M P) d := by
  ext z
  exact glKirillovMatrix_kernel_iff M P (fun i => (z i).val)

theorem glKirillovMatrix_hasMinimalKernelDegrees_iff (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (degrees : List ℕ) :
    HasMinimalKernelDegrees (glKirillovMatrix M P) degrees ↔
      HasMinimalKernelDegrees (glEquationMatrix M P) degrees := by
  rw [hasMinimalKernelDegrees_iff_hilbert, hasMinimalKernelDegrees_iff_hilbert]
  apply forall_congr'
  intro d
  rw [glKirillovMatrix_polynomialKernelAtDegree M P d]

end Polynomial
end FD56

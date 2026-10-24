/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityGLNormalForm

/-! Exact polynomial parameter equations for GL stabilizers at arbitrary depth. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m r t : Type*} [Field K] [Fintype n] [Fintype m]
  [Fintype r] [Fintype t] [DecidableEq n] [DecidableEq m] [DecidableEq t]

omit [DecidableEq m] in
theorem gl_row_parameter_equations_iff
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (O : Matrix t n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' O)))
    (R : Matrix n t K[X]) (hR : O*R=1)
    (hPV : P*polynomialKernelBasisMatrix O B=0)
    (A : Matrix n t K[X]) (U : Matrix n m K[X]) :
    (P*(A*O)=0 ∧ M*(A*O)-(A*O)*M=U*P) ↔
      (P*A=0 ∧ A*(O*M*polynomialKernelBasisMatrix O B)=0 ∧
        M*A-A*(O*M*R)=U*(P*R)) := by
  let V := polynomialKernelBasisMatrix O B
  have hOV : O*V=0 := polynomialKernelBasisMatrix_mul O B
  have hPV' : P*V=0 := hPV
  have hP : P=(P*R)*O := row_factor_through_of_kernel_basis O B R hR P hPV
  constructor
  · rintro ⟨hPX,hcomm⟩
    have hPA : P*A=0 := by
      have he := congrArg (fun Y : Matrix m n K[X] => Y*R) hPX
      simpa only [Matrix.mul_assoc,hR,Matrix.mul_one,Matrix.zero_mul] using he
    have hAF : A*(O*M*V)=0 := by
      have he := congrArg (fun Y : Matrix n n K[X] => Y*V) hcomm
      simp only [Matrix.sub_mul,Matrix.mul_assoc,hOV,hPV',Matrix.mul_zero] at he
      simpa only [Matrix.mul_assoc] using (sub_eq_zero.mp he).symm
    refine ⟨hPA,hAF,?_⟩
    have he := congrArg (fun Y : Matrix n n K[X] => Y*R) hcomm
    simpa only [Matrix.sub_mul,Matrix.mul_assoc,hR,Matrix.mul_one] using he
  · rintro ⟨hPA,hAF,hred⟩
    have hAM : A*O*M=(A*O*M*R)*O :=
      row_factor_through_of_kernel_basis O B R hR (A*O*M)
        (by simpa only [Matrix.mul_assoc] using hAF)
    constructor
    · rw [← Matrix.mul_assoc,hPA,Matrix.zero_mul]
    · calc
        M*(A*O)-(A*O)*M=(M*A-A*(O*M*R))*O := by
          rw [Matrix.sub_mul]
          simpa only [Matrix.mul_assoc] using congrArg (fun Y => M*(A*O)-Y) hAM
        _ = (U*(P*R))*O := by rw [hred]
        _ = U*P := by rw [Matrix.mul_assoc,← hP]

theorem observability_first_rows_factor
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ) (hq : 0<q)
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q))))
    (R : Matrix n (Fin q × m) K[X]) (hR : observabilityMatrix M P q*R=1) :
    P=(P*R)*observabilityMatrix M P q := by
  apply row_factor_through_of_kernel_basis _ B R hR
  have he := polynomialKernelBasisMatrix_mul (observabilityMatrix M P q) B
  funext i j
  have hh := congrFun (congrFun he (⟨0,hq⟩,i)) j
  change ((P*(M^0 : Matrix n n K[X]))*polynomialKernelBasisMatrix (observabilityMatrix M P q) B) i j=0 at hh
  simpa using hh

theorem gl_observability_parameterization [DecidableEq r]
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ) (hq : 0<q)
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q))))
    (R : Matrix n (Fin q × m) K[X]) (hR : observabilityMatrix M P q*R=1)
    (hO : Function.Injective (observabilityMatrix M P (q+1)).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X]) :
    (P*X=0 ∧ M*X-X*M=U*P) ↔
      ∃ A : Matrix n (Fin q × m) K[X],
        X=A*observabilityMatrix M P q ∧ P*A=0 ∧
        A*(observabilityMatrix M P q*M*polynomialKernelBasisMatrix _ B)=0 ∧
        M*A-A*(observabilityMatrix M P q*M*R)=U*(P*R) := by
  have hPV : P*polynomialKernelBasisMatrix (observabilityMatrix M P q) B=0 := by
    have he := polynomialKernelBasisMatrix_mul (observabilityMatrix M P q) B
    funext i j
    have hh := congrFun (congrFun he (⟨0,hq⟩,i)) j
    change ((P*(M^0 : Matrix n n K[X]))*polynomialKernelBasisMatrix (observabilityMatrix M P q) B) i j=0 at hh
    simpa using hh
  constructor
  · rintro ⟨hPX,hcomm⟩
    have hX := gl_observability_row_factor M P q B R hR hO X U hPX hcomm
    refine ⟨X*R,hX,?_⟩
    apply (gl_row_parameter_equations_iff M P _ B R hR hPV (X*R) U).mp
    rw [← hX]
    exact ⟨hPX,hcomm⟩
  · rintro ⟨A,hX,hA⟩
    rw [hX]
    exact (gl_row_parameter_equations_iff M P _ B R hR hPV A U).mpr hA

theorem gl_observability_unique_parameterization [DecidableEq r]
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ) (hq : 0<q)
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q))))
    (R : Matrix n (Fin q × m) K[X]) (hR : observabilityMatrix M P q*R=1)
    (hO : Function.Injective (observabilityMatrix M P (q+1)).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X]) :
    (P*X=0 ∧ M*X-X*M=U*P) ↔
      ∃! A : Matrix n (Fin q × m) K[X],
        X=A*observabilityMatrix M P q ∧ P*A=0 ∧
        A*(observabilityMatrix M P q*M*polynomialKernelBasisMatrix _ B)=0 ∧
        M*A-A*(observabilityMatrix M P q*M*R)=U*(P*R) := by
  constructor
  · intro h
    obtain ⟨A,hA⟩ := (gl_observability_parameterization M P q hq B R hR hO X U).mp h
    refine ⟨A,hA,?_⟩
    intro A' hA'
    exact row_factor_unique_of_right_inverse _ R hR A' A (hA'.1.symm.trans hA.1)
  · intro h
    exact (gl_observability_parameterization M P q hq B R hR hO X U).mpr h.exists

theorem generic_gl_observability_parameterization [DecidableEq r]
    (q : ℕ) (hq : 0<q) (hmn : q*Fintype.card m≤Fintype.card n)
    (hnm : Fintype.card n≤(q+1)*Fintype.card m)
    (B : Basis r (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix (genericAffineSquare K n m)
        (genericAffineRows K n m) q))))
    (R : Matrix n (Fin q × m) (AffineCoefficientField K (MatrixParameters n m))[X])
    (hR : observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q*R=1)
    (X : Matrix n n (AffineCoefficientField K (MatrixParameters n m))[X])
    (U : Matrix n m (AffineCoefficientField K (MatrixParameters n m))[X]) :
    (genericAffineRows K n m*X=0 ∧
      genericAffineSquare K n m*X-X*genericAffineSquare K n m=U*genericAffineRows K n m) ↔
    ∃! A : Matrix n (Fin q × m) (AffineCoefficientField K (MatrixParameters n m))[X],
      X=A*observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q ∧
      genericAffineRows K n m*A=0 ∧
      A*(observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q*
        genericAffineSquare K n m*polynomialKernelBasisMatrix _ B)=0 ∧
      genericAffineSquare K n m*A-
        A*(observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q*
          genericAffineSquare K n m*R)=U*(genericAffineRows K n m*R) :=
  gl_observability_unique_parameterization _ _ q hq B R hR
    (generic_terminal_observability_injective q hmn hnm) X U

end FD56

/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericTerminalObservability
import FD56.Hilbert.BetaKernel

/-! The GL equation annihilates the preceding observability kernel at arbitrary depth. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m r : Type*} [Field K] [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

theorem gl_commutes_on_observability_kernel (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (X : Matrix n n K[X]) (U : Matrix n m K[X]) (V : Matrix n r K[X])
    (q : ℕ) (hcomm : M*X-X*M=U*P) (hV : ∀ j<q, P*M^j*V=0)
    (i : ℕ) (hi : i≤q) : M^i*X*V=X*M^i*V := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hstep : M*X*M^i*V=X*M*M^i*V := by
      have he := congrArg (fun Y : Matrix n n K[X] => Y*M^i*V) hcomm
      simp only [Matrix.sub_mul] at he
      have hz : U*P*M^i*V=0 := by rw [Matrix.mul_assoc,Matrix.mul_assoc,← Matrix.mul_assoc P (M^i) V,hV i (by omega),Matrix.mul_zero]
      rw [hz] at he
      exact sub_eq_zero.mp he
    calc
      M^(i+1)*X*V=M*(M^i*X*V) := by rw [pow_succ']; simp only [Matrix.mul_assoc]
      _ = M*(X*M^i*V) := by rw [ih (by omega)]
      _ = X*M^(i+1)*V := by rw [pow_succ']; simpa only [Matrix.mul_assoc] using hstep

theorem gl_annihilates_observability_kernel (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (X : Matrix n n K[X]) (U : Matrix n m K[X]) (V : Matrix n r K[X])
    (q : ℕ) (hPX : P*X=0) (hcomm : M*X-X*M=U*P)
    (hV : ∀ j<q, P*M^j*V=0)
    (hO : Function.Injective (observabilityMatrix M P (q+1)).mulVec) : X*V=0 := by
  have he : observabilityMatrix M P (q+1)*(X*V)=0 := by
    funext im j
    change ((P*M^im.1.val)*(X*V)) im.2 j=0
    have hz : (P*M^im.1.val)*(X*V)=0 := by
      calc
        (P*M^im.1.val)*(X*V)=P*(M^im.1.val*X*V) := by simp only [Matrix.mul_assoc]
        _ = P*(X*M^im.1.val*V) := by
          rw [gl_commutes_on_observability_kernel M P X U V q hcomm hV im.1.val (by have := im.1.isLt; omega)]
        _ = 0 := by rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hPX,Matrix.zero_mul,Matrix.zero_mul]
    exact congrFun (congrFun hz im.2) j
  exact matrix_left_mul_injective_of_mulVec _ hO (he.trans (Matrix.mul_zero _).symm)

theorem gl_observability_row_factor (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (q : ℕ) (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q))))
    (R : Matrix n (Fin q × m) K[X]) (hR : observabilityMatrix M P q*R=1)
    (hO : Function.Injective (observabilityMatrix M P (q+1)).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (hPX : P*X=0) (hcomm : M*X-X*M=U*P) :
    X=(X*R)*observabilityMatrix M P q := by
  let V := polynomialKernelBasisMatrix (observabilityMatrix M P q) B
  have hV (j : ℕ) (hj : j<q) : P*M^j*V=0 := by
    have he := polynomialKernelBasisMatrix_mul (observabilityMatrix M P q) B
    funext i k
    exact congrFun (congrFun he (⟨j,hj⟩,i)) k
  exact row_factor_through_of_kernel_basis _ B R hR X
    (gl_annihilates_observability_kernel M P X U V q hPX hcomm hV hO)

theorem observability_beta_relation {s : Type*}
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (q : ℕ) (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q))))
    (R : Matrix n (Fin q × m) K[X]) (hR : observabilityMatrix M P q*R=1)
    (T : Matrix s m K[X])
    (hT : T*(P*M^q*polynomialKernelBasisMatrix (observabilityMatrix M P q) B)=0) :
    T*P*M^q=(T*P*M^q*R)*observabilityMatrix M P q := by
  apply row_factor_through_of_kernel_basis _ B R hR
  simpa only [Matrix.mul_assoc] using hT

theorem generic_gl_observability_row_factor
    (q : ℕ) (hmn : q*Fintype.card m≤Fintype.card n)
    (hnm : Fintype.card n≤(q+1)*Fintype.card m)
    (B : Basis r (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix (genericAffineSquare K n m)
        (genericAffineRows K n m) q))))
    (R : Matrix n (Fin q × m) (AffineCoefficientField K (MatrixParameters n m))[X])
    (hR : observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q*R=1)
    (X : Matrix n n (AffineCoefficientField K (MatrixParameters n m))[X])
    (U : Matrix n m (AffineCoefficientField K (MatrixParameters n m))[X])
    (hPX : genericAffineRows K n m*X=0)
    (hcomm : genericAffineSquare K n m*X-X*genericAffineSquare K n m=U*genericAffineRows K n m) :
    X=(X*R)*observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q :=
  gl_observability_row_factor _ _ q B R hR
    (generic_terminal_observability_injective q hmn hnm) X U hPX hcomm

end FD56

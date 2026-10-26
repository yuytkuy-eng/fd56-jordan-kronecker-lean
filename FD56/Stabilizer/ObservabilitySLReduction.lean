/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ScalarObservability
import FD56.Hilbert.ObservabilityGLReduction
import FD56.Stabilizer.TraceAnnihilator

/-! Exact scalar parameter equations for the full SL radical at arbitrary depth. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m r t : Type*} [Field K] [Fintype n] [Fintype m]
  [Fintype r] [Fintype t] [DecidableEq n] [DecidableEq m] [DecidableEq t]

omit [DecidableEq m] in
theorem scalar_row_parameter_equations_iff
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (O : Matrix t n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' O)))
    (R : Matrix n t K[X]) (hR : O*R=1)
    (hPV : P*polynomialKernelBasisMatrix O B=0)
    (A : Matrix n t K[X]) (U : Matrix n m K[X]) (c : K[X]) :
    (P*(A*O)=0 ∧ M*(A*O)-(A*O)*M=U*P+c • 1) ↔
      (P*A=0 ∧ A*(O*M*polynomialKernelBasisMatrix O B)=(-c) •
        polynomialKernelBasisMatrix O B ∧
        M*A-A*(O*M*R)=U*(P*R)+c • R) := by
  let V := polynomialKernelBasisMatrix O B
  have hOV : O*V=0 := polynomialKernelBasisMatrix_mul O B
  have hPV' : P*V=0 := hPV
  constructor
  · rintro ⟨hPX,hcomm⟩
    have hPA : P*A=0 := by
      have he := congrArg (fun Y : Matrix m n K[X] => Y*R) hPX
      simpa only [Matrix.mul_assoc,hR,Matrix.mul_one,Matrix.zero_mul] using he
    have hAF : A*(O*M*V)=(-c) • V := by
      have he := congrArg (fun Y : Matrix n n K[X] => Y*V) hcomm
      simp only [Matrix.sub_mul,Matrix.add_mul,Matrix.smul_mul,Matrix.one_mul,
        Matrix.mul_assoc,hOV,hPV',Matrix.mul_zero,zero_sub,zero_add] at he
      simpa only [neg_smul,Matrix.mul_assoc] using neg_eq_iff_eq_neg.mp he
    refine ⟨hPA,hAF,?_⟩
    have he := congrArg (fun Y : Matrix n n K[X] => Y*R) hcomm
    simpa only [Matrix.sub_mul,Matrix.add_mul,Matrix.smul_mul,Matrix.one_mul,
      Matrix.mul_assoc,hR,Matrix.mul_one] using he
  · rintro ⟨hPA,hAF,hred⟩
    change A*(O*M*V)=(-c) • V at hAF
    simp only [Matrix.mul_assoc] at hAF hred
    let S := M*(A*O)-(A*O)*M-U*P-c • (1 : Matrix n n K[X])
    have hSV : S*V=0 := by
      dsimp only [S]
      simp only [Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.mul_assoc,
        hOV,hPV',Matrix.mul_zero,zero_sub,sub_zero]
      rw [hAF,neg_smul,neg_neg,sub_self]
    have hSR : S*R=0 := by
      dsimp only [S]
      simp only [Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.mul_assoc,
        hR,Matrix.mul_one]
      rw [hred]
      abel
    have hS : S=0 := by
      rw [row_factor_through_of_kernel_basis O B R hR S hSV,hSR,Matrix.zero_mul]
    refine ⟨?_,?_⟩
    · rw [← Matrix.mul_assoc,hPA,Matrix.zero_mul]
    · change M*(A*O)-(A*O)*M-U*P-c • 1=0 at hS
      have hh := sub_eq_zero.mp hS
      exact sub_eq_iff_eq_add.mp hh |>.trans (add_comm _ _)

theorem scalar_observability_row_factor [DecidableEq r]
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ)
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q))))
    (R : Matrix n (Fin q × m) K[X]) (hR : observabilityMatrix M P q*R=1)
    (hO : Function.Injective (observabilityMatrix M P (q+1)).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X]) (c : K[X])
    (hPX : P*X=0) (hcomm : M*X-X*M=U*P+c • 1) :
    X=(X*R)*observabilityMatrix M P q := by
  let V := polynomialKernelBasisMatrix (observabilityMatrix M P q) B
  have hV (j : ℕ) (hj : j<q) : P*M^j*V=0 := by
    have he := polynomialKernelBasisMatrix_mul (observabilityMatrix M P q) B
    funext i k
    exact congrFun (congrFun he (⟨j,hj⟩,i)) k
  exact row_factor_through_of_kernel_basis _ B R hR X
    (scalar_commutator_annihilates_observability_kernel M P X U c V q hPX hcomm hV hO)

theorem scalar_observability_unique_parameterization [DecidableEq r]
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ) (hq : 0<q)
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q))))
    (R : Matrix n (Fin q × m) K[X]) (hR : observabilityMatrix M P q*R=1)
    (hO : Function.Injective (observabilityMatrix M P (q+1)).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X]) (c : K[X]) :
    (P*X=0 ∧ M*X-X*M=U*P+c • 1) ↔
      ∃! A : Matrix n (Fin q × m) K[X],
        X=A*observabilityMatrix M P q ∧ P*A=0 ∧
        A*(observabilityMatrix M P q*M*polynomialKernelBasisMatrix _ B)=(-c) •
          polynomialKernelBasisMatrix _ B ∧
        M*A-A*(observabilityMatrix M P q*M*R)=U*(P*R)+c • R := by
  have hPV : P*polynomialKernelBasisMatrix (observabilityMatrix M P q) B=0 := by
    have he := polynomialKernelBasisMatrix_mul (observabilityMatrix M P q) B
    funext i j
    have hh := congrFun (congrFun he (⟨0,hq⟩,i)) j
    change ((P*(M^0 : Matrix n n K[X]))*polynomialKernelBasisMatrix
      (observabilityMatrix M P q) B) i j=0 at hh
    simpa using hh
  constructor
  · rintro ⟨hPX,hcomm⟩
    have hX := scalar_observability_row_factor M P q B R hR hO X U c hPX hcomm
    refine ⟨X*R,⟨hX,?_⟩,?_⟩
    · apply (scalar_row_parameter_equations_iff M P _ B R hR hPV (X*R) U c).mp
      rw [← hX]
      exact ⟨hPX,hcomm⟩
    · intro A hA
      exact row_factor_unique_of_right_inverse _ R hR A (X*R) (hA.1.symm.trans hX)
  · rintro ⟨A,hA,_⟩
    rw [hA.1]
    exact (scalar_row_parameter_equations_iff M P _ B R hR hPV A U c).mpr hA.2

theorem sl_observability_unique_parameterization [DecidableEq r] [Nonempty n]
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ) (hq : 0<q)
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q))))
    (R : Matrix n (Fin q × m) K[X]) (hR : observabilityMatrix M P q*R=1)
    (hO : Function.Injective (observabilityMatrix M P (q+1)).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X]) :
    SLRadical M P X U ↔ ∃ c : K[X],
      ∃! A : Matrix n (Fin q × m) K[X],
        X=A*observabilityMatrix M P q ∧ P*A=0 ∧
        A*(observabilityMatrix M P q*M*polynomialKernelBasisMatrix _ B)=(-c) •
          polynomialKernelBasisMatrix _ B ∧
        M*A-A*(observabilityMatrix M P q*M*R)=U*(P*R)+c • R := by
  rw [slRadical_iff_equations]
  constructor
  · rintro ⟨_,hPX,c,hcomm⟩
    exact ⟨c,(scalar_observability_unique_parameterization M P q hq B R hR hO X U c).mp
      ⟨hPX,hcomm⟩⟩
  · rintro ⟨c,hc⟩
    obtain ⟨hPX,hcomm⟩ :=
      (scalar_observability_unique_parameterization M P q hq B R hR hO X U c).mpr hc
    exact ⟨observable_scalar_commutator_trace_zero M P X U c hPX hcomm (q+1) hO,
      hPX,c,hcomm⟩

theorem generic_sl_observability_parameterization [DecidableEq r] [Nonempty n]
    (q : ℕ) (hq : 0<q) (hmn : q*Fintype.card m≤Fintype.card n)
    (hnm : Fintype.card n≤(q+1)*Fintype.card m)
    (B : Basis r (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix (genericAffineSquare K n m)
        (genericAffineRows K n m) q))))
    (R : Matrix n (Fin q × m) (AffineCoefficientField K (MatrixParameters n m))[X])
    (hR : observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q*R=1)
    (X : Matrix n n (AffineCoefficientField K (MatrixParameters n m))[X])
    (U : Matrix n m (AffineCoefficientField K (MatrixParameters n m))[X]) :
    SLRadical (genericAffineSquare K n m) (genericAffineRows K n m) X U ↔
      ∃ c : (AffineCoefficientField K (MatrixParameters n m))[X],
      ∃! A : Matrix n (Fin q × m) (AffineCoefficientField K (MatrixParameters n m))[X],
        X=A*observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q ∧
        genericAffineRows K n m*A=0 ∧
        A*(observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q*
          genericAffineSquare K n m*polynomialKernelBasisMatrix _ B)=(-c) •
          polynomialKernelBasisMatrix _ B ∧
        genericAffineSquare K n m*A-
          A*(observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q*
            genericAffineSquare K n m*R)=U*(genericAffineRows K n m*R)+c • R :=
  sl_observability_unique_parameterization _ _ q hq B R hR
    (generic_terminal_observability_injective q hmn hnm) X U

end FD56

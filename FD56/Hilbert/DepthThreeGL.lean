/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeGLLeading

/-! Third-depth GL minimal degrees from the two reduced auxiliary bases. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m r s : Type*} [Field K]
  [Fintype n] [Fintype m] [Fintype r] [Fintype s]
  [DecidableEq n] [DecidableEq m] [DecidableEq r] [DecidableEq s]

theorem depth_three_gl_kernel_hilbert
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P 3))))
    (Bt : Basis s K[X] (LinearMap.ker (Matrix.toLin'
      (P*(M^3 : Matrix n n K[X])*polynomialKernelBasisMatrix _ Bv).transpose)))
    (R : Matrix n (Fin 3 × m) K[X]) (hR : observabilityMatrix M P 3*R=1)
    (D₀ D₁ D₂ : Matrix s m K[X])
    (hrel : (polynomialKernelBasisMatrix _ Bt).transpose*P*M^3=
      D₀*P+D₁*(P*M)+D₂*(P*M^2))
    (hO : Function.Injective (observabilityMatrix M P 4).mulVec)
    (a : r → ℕ) (b : s → ℕ) (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x i, (polynomialKernelBasisMatrix _ Bv x i).natDegree≤a i)
    (hT : ∀ y j, (polynomialKernelBasisMatrix _ Bt y j).natDegree≤b j)
    (hVL : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix _ Bv x i).coeff (a i))))
    (hTL : Function.Injective (Matrix.mulVec
      (fun y j => (polynomialKernelBasisMatrix _ Bt y j).coeff (b j))))
    (hOL : Function.Injective (Matrix.mulVec (fun x i =>
      (observabilityMatrix M P 3 i x).coeff (i.1.val+1)))) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d)=
      ∑ ij : r × s, (d+1-(a ij.1+b ij.2+3)) := by
  obtain ⟨hD₀,hD₁,hD₂⟩ := depth_three_beta_coefficients_degree M P
    (polynomialKernelBasisMatrix _ Bt).transpose D₀ D₁ D₂ b hM hP (fun j y => hT y j) hrel hOL
  apply polynomial_kernel_basis_hilbert (glEquationMatrix M P)
    (depthThreeGLKernelBasis M P Bv Bt R hR D₀ D₁ D₂ hrel hO)
    (fun ij => a ij.1+b ij.2+3) d
  · rw [polynomialKernelBasisMatrix_depthThreeGL]
    exact depthThreeGLColumns_degree M P _ _ D₀ D₁ D₂ a b hM hP hV
      (fun j y => hT y j) hD₀ hD₁ hD₂
  · rw [polynomialKernelBasisMatrix_depthThreeGL]
    exact depthThreeGLColumns_leading_injective M P _ _ D₀ D₁ D₂ a b hM hP hV
      (fun j y => hT y j) hD₁ hD₂ hVL hTL hOL

theorem depth_three_gl_kernel_hilbert_of_bases
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P 3))))
    (Bt : Basis s K[X] (LinearMap.ker (Matrix.toLin'
      (P*(M^3 : Matrix n n K[X])*polynomialKernelBasisMatrix _ Bv).transpose)))
    (R : Matrix n (Fin 3 × m) K[X]) (hR : observabilityMatrix M P 3*R=1)
    (hO : Function.Injective (observabilityMatrix M P 4).mulVec)
    (a : r → ℕ) (b : s → ℕ) (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x i, (polynomialKernelBasisMatrix _ Bv x i).natDegree≤a i)
    (hT : ∀ y j, (polynomialKernelBasisMatrix _ Bt y j).natDegree≤b j)
    (hVL : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix _ Bv x i).coeff (a i))))
    (hTL : Function.Injective (Matrix.mulVec
      (fun y j => (polynomialKernelBasisMatrix _ Bt y j).coeff (b j))))
    (hOL : Function.Injective (Matrix.mulVec (fun x i =>
      (observabilityMatrix M P 3 i x).coeff (i.1.val+1)))) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d)=
      ∑ ij : r × s, (d+1-(a ij.1+b ij.2+3)) := by
  let T : Matrix s m K[X] := (polynomialKernelBasisMatrix _ Bt).transpose
  have hTF : T*(P*(M^3 : Matrix n n K[X])*polynomialKernelBasisMatrix _ Bv)=0 := by
    simpa only [T,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero] using
      congrArg Matrix.transpose (polynomialKernelBasisMatrix_mul _ Bt)
  obtain ⟨D₀,D₁,D₂,hrel⟩ := exists_depth_three_beta_coefficients M P Bv R hR T hTF
  exact depth_three_gl_kernel_hilbert M P Bv Bt R hR D₀ D₁ D₂ hrel hO a b hM hP hV hT hVL hTL hOL d

theorem generic_depth_three_gl_kernel_hilbert_of_bases
    (hmn : 3*Fintype.card m<Fintype.card n)
    (hnm : Fintype.card n≤4*Fintype.card m)
    (Bv : Basis r (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) 3))))
    (Bt : Basis s (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' ((genericAffineRows K n m)*
        (genericAffineSquare K n m)^3*polynomialKernelBasisMatrix _ Bv).transpose)))
    (a : r → ℕ) (b : s → ℕ)
    (hV : ∀ x i, (polynomialKernelBasisMatrix _ Bv x i).natDegree≤a i)
    (hT : ∀ y j, (polynomialKernelBasisMatrix _ Bt y j).natDegree≤b j)
    (hVL : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix _ Bv x i).coeff (a i))))
    (hTL : Function.Injective (Matrix.mulVec
      (fun y j => (polynomialKernelBasisMatrix _ Bt y j).coeff (b j)))) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (glEquationMatrix (genericAffineSquare K n m)
        (genericAffineRows K n m)) d)=∑ ij : r × s, (d+1-(a ij.1+b ij.2+3)) := by
  obtain ⟨R,_,hR⟩ := generic_actual_depth_three_stack_right_inverse (K := K) hmn
  exact depth_three_gl_kernel_hilbert_of_bases _ _ Bv Bt R hR
    (generic_terminal_observability_injective 3 (Nat.le_of_lt hmn) hnm) a b
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m)
    hV hT hVL hTL (generic_actual_depth_three_stack_leading_injective hmn) d

end FD56

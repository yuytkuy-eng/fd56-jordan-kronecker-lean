/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthTwoGLDegree

/-! The actual GL Hilbert function from the two auxiliary polynomial bases. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K m n r s : Type*} [Field K] [Fintype m] [Fintype n] [Fintype r] [Fintype s]
  [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq s]

theorem depthTwo_gl_kernel_hilbert (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P (P*M)))))
    (Bt : Basis s K[X] (LinearMap.ker (Matrix.toLin'
      (P*M*M*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) Bv).transpose)))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P (P*M)*R=1)
    (D₀ D₁ : Matrix s m K[X])
    (hrel : (polynomialKernelBasisMatrix _ Bt).transpose*P*M*M=D₀*P+D₁*(P*M))
    (hF : Function.Injective (P*M*M*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) Bv).mulVec)
    (a : r → ℕ) (b : s → ℕ) (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x i, (polynomialKernelBasisMatrix (depthTwoStack P (P*M)) Bv x i).natDegree ≤ a i)
    (hT : ∀ y j, (polynomialKernelBasisMatrix _ Bt y j).natDegree ≤ b j)
    (hVL : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix (depthTwoStack P (P*M)) Bv x i).coeff (a i))))
    (hTL : Function.Injective (Matrix.mulVec
      (fun y j => (polynomialKernelBasisMatrix _ Bt y j).coeff (b j))))
    (hO : Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P (P*M) i x).coeff (depthTwoRowDegree i)))) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d) =
      ∑ ij : r × s, (d+1-(a ij.1+b ij.2+2)) := by
  obtain ⟨hD₀,hD₁⟩ := depthTwo_beta_coefficients_degree M P
    (polynomialKernelBasisMatrix _ Bt).transpose D₀ D₁ b hM hP
    (fun j y => hT y j) hrel hO
  apply polynomial_kernel_basis_hilbert (glEquationMatrix M P)
    (depthTwoGLKernelBasis M P Bv Bt R hR D₀ D₁ hrel hF)
    (fun ij => a ij.1+b ij.2+2) d
  · rw [polynomialKernelBasisMatrix_depthTwoGL]
    exact depthTwoGLColumns_degree M P _ _ D₀ D₁ a b hM hP hV
      (fun j y => hT y j) hD₀ hD₁
  · rw [polynomialKernelBasisMatrix_depthTwoGL]
    exact depthTwoGLColumns_leading_injective M P _ _ D₀ D₁ a b hM hP hV
      (fun j y => hT y j) hD₁ hVL hTL hO

theorem depthTwo_gl_kernel_hilbert_of_bases (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P (P*M)))))
    (Bt : Basis s K[X] (LinearMap.ker (Matrix.toLin'
      (P*M*M*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) Bv).transpose)))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P (P*M)*R=1)
    (hF : Function.Injective (P*M*M*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) Bv).mulVec)
    (a : r → ℕ) (b : s → ℕ) (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x i, (polynomialKernelBasisMatrix (depthTwoStack P (P*M)) Bv x i).natDegree ≤ a i)
    (hT : ∀ y j, (polynomialKernelBasisMatrix _ Bt y j).natDegree ≤ b j)
    (hVL : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix (depthTwoStack P (P*M)) Bv x i).coeff (a i))))
    (hTL : Function.Injective (Matrix.mulVec
      (fun y j => (polynomialKernelBasisMatrix _ Bt y j).coeff (b j))))
    (hO : Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P (P*M) i x).coeff (depthTwoRowDegree i)))) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d) =
      ∑ ij : r × s, (d+1-(a ij.1+b ij.2+2)) := by
  let V := polynomialKernelBasisMatrix (depthTwoStack P (P*M)) Bv
  let T := (polynomialKernelBasisMatrix (P*M*M*V).transpose Bt).transpose
  have hTF : T*(P*M*M*V)=0 := by
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero] using
      congrArg Matrix.transpose (polynomialKernelBasisMatrix_mul (P*M*M*V).transpose Bt)
  obtain ⟨D₀,D₁,hrel⟩ := exists_depthTwo_beta_coefficients M P Bv R hR T hTF
  exact depthTwo_gl_kernel_hilbert M P Bv Bt R hR D₀ D₁ hrel hF a b hM hP hV hT hVL hTL hO d

end FD56

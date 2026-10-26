/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityGLBasis
import FD56.Hilbert.ObservabilityGLLeading
import FD56.Hilbert.ConvolutionDegrees

/-! Arbitrary-depth GL minimal degrees from the two actual reduced auxiliary bases. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m r s : Type*} [Field K]
  [Fintype n] [Fintype m] [Fintype r] [Fintype s]
  [DecidableEq n] [DecidableEq m] [DecidableEq r] [DecidableEq s]

theorem observability_gl_kernel_hilbert_of_bases
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ)
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P (q+1)))))
    (Bt : Basis s K[X] (LinearMap.ker (Matrix.toLin'
      (P * M ^ (q+1) * polynomialKernelBasisMatrix _ Bv).transpose)))
    (R : Matrix n (Fin (q+1) × m) K[X]) (hR : observabilityMatrix M P (q+1) * R = 1)
    (hO : Function.Injective (observabilityMatrix M P (q+2)).mulVec)
    (a : r → ℕ) (b : s → ℕ) (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x i, (polynomialKernelBasisMatrix _ Bv x i).natDegree ≤ a i)
    (hT : ∀ y j, (polynomialKernelBasisMatrix _ Bt y j).natDegree ≤ b j)
    (hVL : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix _ Bv x i).coeff (a i))))
    (hTL : Function.Injective (Matrix.mulVec
      (fun y j => (polynomialKernelBasisMatrix _ Bt y j).coeff (b j))))
    (hPL : Function.Surjective (matrixCoeff P 1).mulVec)
    (hOL : Function.Injective (Matrix.mulVec (fun x (i : Fin (q+1) × m) =>
      (observabilityMatrix M P (q+1) i x).coeff (i.1.val+1))))
    (hOT : Function.Injective (Matrix.mulVec (fun (i : Fin (q+2) × m) x =>
      (observabilityMatrix M P (q+2) i x).coeff (i.1.val+1)))) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d) =
      ∑ ij : r × s, (d+1-(a ij.1+b ij.2+q+1)) := by
  let V := polynomialKernelBasisMatrix (observabilityMatrix M P (q+1)) Bv
  let T : Matrix s m K[X] := (polynomialKernelBasisMatrix _ Bt).transpose
  have hTF : T * (P * M ^ (q+1) * V) = 0 := by
    simpa only [T, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using
      congrArg Matrix.transpose (polynomialKernelBasisMatrix_mul _ Bt)
  obtain ⟨H,D,hzero,hstep,hend⟩ := exists_observability_backward_rows M P q Bv R hR T hTF
  have hrow : Function.Injective (Matrix.mulVec
      (show Matrix n (Fin (q+1) × m) K from fun x i =>
        (matrixCoeff P 1 * matrixCoeff M 1 ^ i.1.val) i.2 x)) := by
    have he : (fun x (i : Fin (q+1) × m) =>
        (observabilityMatrix M P (q+1) i x).coeff (i.1.val+1)) =
        (fun x (i : Fin (q+1) × m) => (matrixCoeff P 1 * matrixCoeff M 1 ^ i.1.val) i.2 x) := by
      funext x i
      exact (observability_polynomial_degree_top M P (q+1) hM hP i x).2
    rwa [he] at hOL
  have hD := structured_coefficients_degree M P D T q b hM hP (fun j y => hT y j)
    (structuredCoefficientRows_relation M P H D T q hzero hstep hend) hrow
  have hH := structured_rows_degree M P H D T q b hM hP hstep hend hD (fun j y => hT y j)
  apply polynomial_kernel_basis_hilbert (glEquationMatrix M P)
    (observabilityGLKernelBasis M P q Bv Bt R hR hO H D hzero hstep hend)
    (fun ij => a ij.1+b ij.2+q+1) d
  · rw [polynomialKernelBasisMatrix_observabilityGL]
    exact structuredColumns_degree M V H D T q a b hM hV hH hD (fun j y => hT y j)
  · rw [polynomialKernelBasisMatrix_observabilityGL]
    exact observability_structuredColumns_leading_injective M P V H D T q a b
      hM hP hV (fun j y => hT y j) hH hend (observability_basis_annihilation M P q Bv)
      hVL hTL hPL hOT

theorem observability_gl_minimal_degrees_of_bases {r s : ℕ}
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ)
    (Bv : Basis (Fin r) K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P (q+1)))))
    (Bt : Basis (Fin s) K[X] (LinearMap.ker (Matrix.toLin'
      (P * M ^ (q+1) * polynomialKernelBasisMatrix _ Bv).transpose)))
    (R : Matrix n (Fin (q+1) × m) K[X]) (hR : observabilityMatrix M P (q+1) * R = 1)
    (hO : Function.Injective (observabilityMatrix M P (q+2)).mulVec)
    (a : Fin r → ℕ) (b : Fin s → ℕ) (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x i, (polynomialKernelBasisMatrix _ Bv x i).natDegree ≤ a i)
    (hT : ∀ y j, (polynomialKernelBasisMatrix _ Bt y j).natDegree ≤ b j)
    (hVL : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix _ Bv x i).coeff (a i))))
    (hTL : Function.Injective (Matrix.mulVec
      (fun y j => (polynomialKernelBasisMatrix _ Bt y j).coeff (b j))))
    (hPL : Function.Surjective (matrixCoeff P 1).mulVec)
    (hOL : Function.Injective (Matrix.mulVec (fun x (i : Fin (q+1) × m) =>
      (observabilityMatrix M P (q+1) i x).coeff (i.1.val+1))))
    (hOT : Function.Injective (Matrix.mulVec (fun (i : Fin (q+2) × m) x =>
      (observabilityMatrix M P (q+2) i x).coeff (i.1.val+1))))
    (alpha beta : List ℕ) (ha : (List.ofFn a).Perm alpha) (hb : (List.ofFn b).Perm beta) :
    HasMinimalKernelDegrees (glEquationMatrix M P)
      ((degreeConvolution alpha beta).map (fun e => e+q)) := by
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [observability_gl_kernel_hilbert_of_bases M P q Bv Bt R hR hO a b hM hP
    hV hT hVL hTL hPL hOL hOT d]
  simpa only [degreeConvolution, List.map_flatMap, List.map_map, Function.comp_def,
    show ∀ x y : ℕ, x+y+1+q = x+y+q+1 by omega] using
      sum_pairs_of_permuted_degrees a b alpha beta ha hb (fun x y => d+1-(x+y+q+1))

end FD56

/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MiddleGL
import FD56.Hilbert.MinimalProfile

/-! The degree list of the middle GL kernel is a shifted pairwise sum
of the two actual auxiliary minimal degree lists. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

def degreeConvolution (alpha beta : List ℕ) : List ℕ :=
  alpha.flatMap (fun a => beta.map (fun b => a + b + 1))

theorem nat_sum_flatMap (xs : List ℕ) (f : ℕ → List ℕ) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem sum_pairs_of_permuted_degrees {r s : ℕ} (a : Fin r → ℕ) (b : Fin s → ℕ)
    (alpha beta : List ℕ) (ha : (List.ofFn a).Perm alpha) (hb : (List.ofFn b).Perm beta)
    (f : ℕ → ℕ → ℕ) :
    (∑ ij : Fin r × Fin s, f (a ij.1) (b ij.2)) =
      (alpha.flatMap (fun x => beta.map (f x))).sum := by
  rw [Fintype.sum_prod_type, nat_sum_flatMap]
  have houter := (ha.map (fun x => (beta.map (f x)).sum)).sum_eq
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] at houter
  rw [← houter]
  apply Finset.sum_congr rfl
  intro i _
  have hinner := (hb.map (f (a i))).sum_eq
  simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using hinner

theorem degreeConvolution_hilbert {r s : ℕ} (a : Fin r → ℕ) (b : Fin s → ℕ)
    (alpha beta : List ℕ) (ha : (List.ofFn a).Perm alpha) (hb : (List.ofFn b).Perm beta)
    (d : ℕ) :
    (∑ ij : Fin r × Fin s, (d + 1 - (a ij.1 + b ij.2 + 1))) =
      ((degreeConvolution alpha beta).map (fun e => d + 1 - e)).sum := by
  simpa only [degreeConvolution, List.map_flatMap, List.map_map, Function.comp_def] using
    sum_pairs_of_permuted_degrees a b alpha beta ha hb (fun x y => d + 1 - (x + y + 1))

theorem hasMinimalKernelDegrees_of_convolution_hilbert
    {K x y : Type*} [Field K] [Fintype y] [DecidableEq y]
    (A : Matrix x y K[X]) {r s : ℕ} (a : Fin r → ℕ) (b : Fin s → ℕ)
    (alpha beta : List ℕ) (ha : (List.ofFn a).Perm alpha) (hb : (List.ofFn b).Perm beta)
    (hH : ∀ d, Module.finrank K (polynomialKernelAtDegree A d) =
      ∑ ij : Fin r × Fin s, (d + 1 - (a ij.1 + b ij.2 + 1))) :
    HasMinimalKernelDegrees A (degreeConvolution alpha beta) := by
  apply (hasMinimalKernelDegrees_iff_hilbert A _).mpr
  intro d
  rw [hH d]
  exact degreeConvolution_hilbert a b alpha beta ha hb d

theorem middle_gl_minimal_degrees_of_bases
    {K n m : Type*} [Field K] [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) {r s : ℕ}
    (Bv : Basis (Fin r) K[X] (LinearMap.ker (Matrix.toLin' P)))
    (Bt : Basis (Fin s) K[X] (LinearMap.ker (Matrix.toLin'
      (P * M * polynomialKernelBasisMatrix P Bv).transpose)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P Bv).mulVec)
    (a : Fin r → ℕ) (b : Fin s → ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x k, (polynomialKernelBasisMatrix P Bv x k).natDegree ≤ a k)
    (hT : ∀ y j, (polynomialKernelBasisMatrix _ Bt y j).natDegree ≤ b j)
    (hVlead : Function.Injective (Matrix.mulVec
      (fun x k => (polynomialKernelBasisMatrix P Bv x k).coeff (a k))))
    (hTlead : Function.Injective (Matrix.mulVec
      (fun y j => (polynomialKernelBasisMatrix _ Bt y j).coeff (b j))))
    (hPlead : Function.Injective (matrixCoeff P 1).transpose.mulVec)
    (alpha beta : List ℕ) (ha : (List.ofFn a).Perm alpha) (hb : (List.ofFn b).Perm beta) :
    HasMinimalKernelDegrees (glEquationMatrix M P) (degreeConvolution alpha beta) := by
  apply hasMinimalKernelDegrees_of_convolution_hilbert (glEquationMatrix M P)
    a b alpha beta ha hb
  intro d
  exact middle_gl_kernel_hilbert_of_bases M P Bv Bt R hPR hG a b hM hP hV hT
    hVlead hTlead hPlead d

end FD56

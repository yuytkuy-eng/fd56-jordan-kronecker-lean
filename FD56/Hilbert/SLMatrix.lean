/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.KernelDimension
import FD56.Hilbert.HilbertObstruction
import FD56.Stabilizer.ConstraintMap

/-! A coordinate matrix for the full SL equations and its bounded kernel.
The scalar correction is eliminated without changing the radical. -/

noncomputable section
namespace FD56
open Polynomial Matrix
open scoped BigOperators

abbrev SLInput (n m : Type*) := (n × n) ⊕ (n × m)
abbrev SLOutput (n m : Type*) := Unit ⊕ ((m × n) ⊕ (n × n))

def matrixPairEquiv (R V n m : Type*) [Semiring R] [AddCommMonoid V] [Module R V] :
    (SLInput n m → V) ≃ₗ[R] (Matrix n n V × Matrix n m V) where
  toFun v := (fun i j => v (.inl (i, j)), fun i j => v (.inr (i, j)))
  invFun z := Sum.elim (fun ij => z.1 ij.1 ij.2) (fun ij => z.2 ij.1 ij.2)
  left_inv v := by apply _root_.funext; intro i; cases i <;> rfl
  right_inv z := rfl
  map_add' v w := rfl
  map_smul' c v := rfl

def constraintOutputEquiv (R n m : Type*) [Semiring R] :
    (R × Matrix m n R × Matrix n n R) ≃ₗ[R] (SLOutput n m → R) where
  toFun z := Sum.elim (fun _ => z.1)
    (Sum.elim (fun ij => z.2.1 ij.1 ij.2) (fun ij => z.2.2 ij.1 ij.2))
  invFun v := (v (.inl ()), fun i j => v (.inr (.inl (i,j))),
    fun i j => v (.inr (.inr (i,j))))
  left_inv z := rfl
  right_inv v := by
    apply _root_.funext
    intro i
    rcases i with u | ij | ij
    · cases u; rfl
    · rfl
    · rfl
  map_add' z w := by apply _root_.funext; intro i; rcases i with u | ij | ij <;> rfl
  map_smul' c z := by apply _root_.funext; intro i; rcases i with u | ij | ij <;> rfl

variable {R n m : Type*} [CommRing R] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

def slEquationLinearMap (M : Matrix n n R) (P : Matrix m n R) (i₀ : n) :
    (SLInput n m → R) →ₗ[R] (SLOutput n m → R) :=
  (constraintOutputEquiv R n m).toLinearMap.comp
    ((slConstraintMap M P i₀).comp (matrixPairEquiv R R n m).toLinearMap)

def slEquationMatrix (M : Matrix n n R) (P : Matrix m n R) (i₀ : n) :
    Matrix (SLOutput n m) (SLInput n m) R :=
  LinearMap.toMatrix' (slEquationLinearMap M P i₀)

variable {K : Type*} [Field K]

theorem slEquationMatrix_kernel_iff (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (i₀ : n) (v : SLInput n m → K[X]) :
    slEquationMatrix M P i₀ *ᵥ v = 0 ↔
      SLRadical M P (fun i j => v (.inl (i,j))) (fun i j => v (.inr (i,j))) := by
  change Matrix.toLin' (LinearMap.toMatrix' (slEquationLinearMap M P i₀)) v = 0 ↔ _
  rw [Matrix.toLin'_toMatrix']
  change constraintOutputEquiv K[X] n m
    (slConstraintMap M P i₀ (matrixPairEquiv K[X] K[X] n m v)) = 0 ↔ _
  rw [(constraintOutputEquiv K[X] n m).map_eq_zero_iff]
  exact slConstraintMap_eq_zero_iff M P i₀ _ _

theorem bounded_slEquationMatrix_kernel_iff (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (i₀ : n) (d : ℕ) (v : SLInput n m → BoundedPoly K d) :
    v ∈ polynomialKernelAtDegree (slEquationMatrix M P i₀) d ↔
      matrixPairEquiv K (BoundedPoly K d) n m v ∈ boundedSLKernel M P d := by
  exact slEquationMatrix_kernel_iff M P i₀ (fun i => (v i).val)

def boundedSLKernelEquiv (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (i₀ : n) (d : ℕ) :
    polynomialKernelAtDegree (slEquationMatrix M P i₀) d ≃ₗ[K] boundedSLKernel M P d where
  toFun v := ⟨matrixPairEquiv K (BoundedPoly K d) n m v.val,
    (bounded_slEquationMatrix_kernel_iff M P i₀ d v.val).mp v.property⟩
  invFun z := ⟨(matrixPairEquiv K (BoundedPoly K d) n m).symm z.val, by
    apply (bounded_slEquationMatrix_kernel_iff M P i₀ d _).mpr
    simp only [LinearEquiv.apply_symm_apply]
    exact z.property⟩
  left_inv v := by apply Subtype.ext; exact (matrixPairEquiv K (BoundedPoly K d) n m).left_inv v.val
  right_inv z := by apply Subtype.ext; exact (matrixPairEquiv K (BoundedPoly K d) n m).right_inv z.val
  map_add' v w := by apply Subtype.ext; rfl
  map_smul' c v := by apply Subtype.ext; rfl

theorem slHilbert_eq_matrix_kernel (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (i₀ : n) (d : ℕ) :
    slHilbert M P d = Module.finrank K (polynomialKernelAtDegree (slEquationMatrix M P i₀) d) :=
  (boundedSLKernelEquiv M P i₀ d).finrank_eq.symm

theorem slHilbert_of_polynomial_basis {F k : Type*} [Field F] [IsAlgClosed K]
    [Fintype k] [DecidableEq k]
    (φ : K[X] →+* F) (hφ : Function.Injective φ)
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (i₀ : n)
    (Z : Matrix (SLInput n m) k K[X]) (e : k → ℕ)
    (hAZ : slEquationMatrix M P i₀ * Z = 0)
    (hZ : ∀ i j, (Z i j).natDegree ≤ e j)
    (hpoint : ∀ x : K, Function.Injective (Z.map (Polynomial.evalRingHom x)).mulVec)
    (hdim : Module.finrank F (LinearMap.ker (Matrix.toLin' ((slEquationMatrix M P i₀).map φ))) =
      Fintype.card k)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (Z i j).coeff (e j)))) :
    HasHilbertProfile M P e := by
  intro d
  rw [slHilbert_eq_matrix_kernel M P i₀ d]
  exact polynomial_kernel_hilbert_function φ hφ (slEquationMatrix M P i₀) Z e d
    hAZ hZ hpoint hdim hlead

end FD56

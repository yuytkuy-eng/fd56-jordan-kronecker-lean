/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialKernel

/-! The Hilbert function of an actual bounded polynomial kernel follows from
the polynomial-basis criteria, via a linear equivalence of coefficient spaces. -/

noncomputable section
namespace FD56
open Polynomial Matrix
open scoped BigOperators
variable {K a b k : Type*} [Field K] [Fintype b] [Fintype k]

def boundedKernelMap (A : Matrix a b K[X]) (d : ℕ) :
    (b → BoundedPoly K d) →ₗ[K] (a → K[X]) where
  toFun Y := A *ᵥ (fun i => (Y i).val)
  map_add' Y W := by
    change A *ᵥ ((fun i => (Y i).val) + (fun i => (W i).val)) = _
    exact Matrix.mulVec_add _ _ _
  map_smul' c Y := by
    change A *ᵥ (c • (fun i => (Y i).val)) = _
    exact Matrix.mulVec_smul _ _ _

def polynomialKernelAtDegree (A : Matrix a b K[X]) (d : ℕ) :
    Submodule K (b → BoundedPoly K d) := LinearMap.ker (boundedKernelMap A d)

theorem mem_degreeLT_shift_iff (p : K[X]) (d e : ℕ) :
    p ∈ Polynomial.degreeLT K (d + 1 - e) ↔
      p = 0 ∨ (e ≤ d ∧ p.natDegree ≤ d - e) := by
  by_cases hp : p = 0
  · subst p; simp
  · rw [Polynomial.mem_degreeLT, Polynomial.degree_eq_natDegree hp, Nat.cast_lt]
    simp only [hp, false_or]
    omega

def kernelFromCoordinates (A : Matrix a b K[X]) (Z : Matrix b k K[X])
    (e : k → ℕ) (d : ℕ) (hAZ : A * Z = 0)
    (hZ : ∀ i j, (Z i j).natDegree ≤ e j) :
    (∀ j, Polynomial.degreeLT K (d + 1 - e j)) →ₗ[K] polynomialKernelAtDegree A d where
  toFun c := by
    have hb := polynomial_combination_degree_bound Z e (fun j => (c j).val) d hZ
      (fun j => (mem_degreeLT_shift_iff _ d (e j)).mp (c j).property)
    refine ⟨fun i => boundedPolyOf ((Z *ᵥ (fun j => (c j).val)) i) (hb i), ?_⟩
    change A *ᵥ (Z *ᵥ (fun j => (c j).val)) = 0
    rw [Matrix.mulVec_mulVec, hAZ, Matrix.zero_mulVec]
  map_add' c c' := by
    apply Subtype.ext
    apply _root_.funext
    intro i
    apply Subtype.ext
    change (Z *ᵥ ((fun j => (c j).val) + (fun j => (c' j).val))) i = _
    rw [Matrix.mulVec_add]
    rfl
  map_smul' s c := by
    apply Subtype.ext
    apply _root_.funext
    intro i
    apply Subtype.ext
    change (Z *ᵥ (s • (fun j => (c j).val))) i = _
    rw [Matrix.mulVec_smul]
    rfl

theorem kernelFromCoordinates_bijective {F : Type*} [Field F] [IsAlgClosed K]
    [Fintype a] [DecidableEq a] [DecidableEq b] [DecidableEq k]
    (φ : K[X] →+* F) (hφ : Function.Injective φ)
    (A : Matrix a b K[X]) (Z : Matrix b k K[X]) (e : k → ℕ) (d : ℕ)
    (hAZ : A * Z = 0) (hZ : ∀ i j, (Z i j).natDegree ≤ e j)
    (hpoint : ∀ x : K, Function.Injective (Z.map (Polynomial.evalRingHom x)).mulVec)
    (hdim : Module.finrank F (LinearMap.ker (Matrix.toLin' (A.map φ))) = Fintype.card k)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (Z i j).coeff (e j)))) :
    Function.Bijective (kernelFromCoordinates A Z e d hAZ hZ) := by
  obtain ⟨L, hL⟩ := polynomial_left_inverse_of_pointwise_injective Z hpoint
  constructor
  · intro c c' h
    have hv : Z *ᵥ (fun j => (c j).val) = Z *ᵥ (fun j => (c' j).val) := by
      exact congrArg (fun Y : polynomialKernelAtDegree A d => fun i => (Y.val i).val) h
    have hc := congrArg (fun v => L *ᵥ v) hv
    dsimp only at hc
    simp only [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec] at hc
    apply _root_.funext
    intro j
    exact Subtype.ext (congrArg (fun v => v j) hc)
  · intro Y
    let y : Matrix b Unit K[X] := fun i _ => (Y.val i).val
    have hy : A * y = 0 ∧ ∀ i, (y i ()).natDegree ≤ d := by
      constructor
      · apply Matrix.ext
        intro i u
        have hz := congrArg (fun v => v i) Y.property
        exact hz
      · intro i
        exact boundedPoly_degree d (Y.val i)
    obtain ⟨c, ⟨hc, hbound⟩, _⟩ :=
      (bounded_polynomial_kernel_coordinates φ hφ A Z e hAZ hpoint hdim hZ hlead y d).mp hy
    let c' : ∀ j, Polynomial.degreeLT K (d + 1 - e j) :=
      fun j => ⟨c j (), (mem_degreeLT_shift_iff _ d (e j)).mpr (hbound j)⟩
    refine ⟨c', ?_⟩
    apply Subtype.ext
    apply _root_.funext
    intro i
    apply Subtype.ext
    exact (congrArg (fun B => B i ()) hc).symm

theorem polynomial_kernel_hilbert_function {F : Type*} [Field F] [IsAlgClosed K]
    [Fintype a] [DecidableEq a] [DecidableEq b] [DecidableEq k]
    (φ : K[X] →+* F) (hφ : Function.Injective φ)
    (A : Matrix a b K[X]) (Z : Matrix b k K[X]) (e : k → ℕ) (d : ℕ)
    (hAZ : A * Z = 0) (hZ : ∀ i j, (Z i j).natDegree ≤ e j)
    (hpoint : ∀ x : K, Function.Injective (Z.map (Polynomial.evalRingHom x)).mulVec)
    (hdim : Module.finrank F (LinearMap.ker (Matrix.toLin' (A.map φ))) = Fintype.card k)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (Z i j).coeff (e j)))) :
    Module.finrank K (polynomialKernelAtDegree A d) = ∑ j, (d + 1 - e j) := by
  let equiv := LinearEquiv.ofBijective (kernelFromCoordinates A Z e d hAZ hZ)
    (kernelFromCoordinates_bijective φ hφ A Z e d hAZ hZ hpoint hdim hlead)
  rw [← equiv.finrank_eq]
  letI (j : k) : Module.Finite K (Polynomial.degreeLT K (d + 1 - e j)) :=
    Module.Finite.of_injective (Polynomial.degreeLTEquiv K (d + 1 - e j)).toLinearMap
      (Polynomial.degreeLTEquiv K (d + 1 - e j)).injective
  rw [Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro j _
  rw [(Polynomial.degreeLTEquiv K (d + 1 - e j)).finrank_eq]
  simp

end FD56

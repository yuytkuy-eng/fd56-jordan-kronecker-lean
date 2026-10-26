/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialBezout
import FD56.LinearAlgebra.ExactKernelBasis
import FD56.Hilbert.MinimalProfile

/-! A polynomial left inverse and fraction-field nullity certify a reduced kernel basis. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem minimal_degrees_of_left_inverse_and_nullity
    {K F a b : Type*} [Field K] [Field F]
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] {N : ℕ}
    (φ : K[X] →+* F) (hφ : Function.Injective φ)
    (A : Matrix a b K[X]) (Z : Matrix b (Fin N) K[X])
    (L : Matrix (Fin N) b K[X]) (hL : L * Z = 1) (hAZ : A * Z = 0)
    (hdim : Module.finrank F (LinearMap.ker (Matrix.toLin' (A.map φ))) = N)
    (e : Fin N → ℕ) (hZ : ∀ i j, (Z i j).natDegree ≤ e j)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (Z i j).coeff (e j)))) :
    HasMinimalKernelDegrees A (List.ofFn e) := by
  have hex := kernel_basis_of_left_inverse_and_spanning φ hφ A Z L hL hAZ
    (fun Y hY => matrix_kernel_spanning_of_nullity
      (A.map φ) (Z.map φ) (L.map φ)
      (by simpa using congrArg (fun B => B.map φ) hL)
      (by simpa using congrArg (fun B => B.map φ) hAZ)
      (by simpa using hdim) (Y.map φ)
      (by simpa using congrArg (fun B => B.map φ) hY))
  have hv (x : b → K[X]) : A *ᵥ x = 0 ↔ ∃! v : Fin N → K[X], x = Z *ᵥ v := by
    constructor
    · intro hx
      obtain ⟨c, hc, hu⟩ := (hex (fun i _ => x i)).mp (by
        funext i j
        exact congrFun hx i)
      refine ⟨fun i => c i (), ?_, ?_⟩
      · exact funext fun i => congrArg (fun B => B i ()) hc
      · intro v hv
        have hh := hu (fun i _ => v i) (by
          funext i j
          cases j
          exact congrFun hv i)
        exact funext fun i => congrArg (fun B => B i ()) hh
    · rintro ⟨v, hv, _⟩
      rw [hv, Matrix.mulVec_mulVec, hAZ, Matrix.zero_mulVec]
  obtain ⟨B, hB⟩ := kernel_basis_of_unique_coordinates A Z hv
  have he : polynomialKernelBasisMatrix A B = Z := funext fun i => funext fun j => hB i j
  refine ⟨N, B, e, ?_, ?_, List.Perm.refl _⟩
  · rw [he]
    exact hZ
  · rw [he]
    exact hlead

theorem minimal_degrees_of_bezout_and_nullity
    {K F a b ι : Type*} [Field K] [Field F]
    [Fintype a] [Fintype b] [Fintype ι] [DecidableEq a] [DecidableEq b] {N : ℕ}
    (φ : K[X] →+* F) (hφ : Function.Injective φ)
    (A : Matrix a b K[X]) (Z : Matrix b (Fin N) K[X])
    (E : ι → Matrix (Fin N) b K[X]) (w : ι → K[X])
    (hw : ∑ i, w i * Matrix.det (E i * Z) = 1) (hAZ : A * Z = 0)
    (hdim : Module.finrank F (LinearMap.ker (Matrix.toLin' (A.map φ))) = N)
    (e : Fin N → ℕ) (hZ : ∀ i j, (Z i j).natDegree ≤ e j)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (Z i j).coeff (e j)))) :
    HasMinimalKernelDegrees A (List.ofFn e) := by
  obtain ⟨L, hL⟩ := left_inverse_of_bezout Z E w hw
  exact minimal_degrees_of_left_inverse_and_nullity φ hφ A Z L hL hAZ hdim e hZ hlead

end FD56

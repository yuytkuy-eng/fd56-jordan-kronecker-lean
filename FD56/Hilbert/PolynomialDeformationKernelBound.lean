/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MinimalDegreeNullity

/-! Polynomial kernel bases stay independent after evaluation. Consequently
an injective residue map into a fixed finite-dimensional subspace bounds the
fraction-field nullity of a polynomial deformation. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K F a b V : Type*} [Field K] [Field F]
  [Algebra K[X] F] [IsFractionRing K[X] F]
  [Fintype b] [DecidableEq b] [AddCommGroup V] [Module K V]

theorem polynomial_deformation_nullity_le_of_residue_map
    (A : Matrix a b K[X]) (x : K) (f : (b → K) →ₗ[K] V)
    (T : Submodule K V) [Module.Finite K T]
    (hmem : ∀ v : b → K[X], A*ᵥv=0 → f (fun i => (v i).eval x) ∈ T)
    (hzero : ∀ v : b → K[X], A*ᵥv=0 →
      f (fun i => (v i).eval x)=0 → (fun i => (v i).eval x)=0) :
    Module.finrank F (LinearMap.ker (Matrix.toLin' (A.map (algebraMap K[X] F)))) ≤
      Module.finrank K T := by
  classical
  obtain ⟨r,⟨B⟩⟩ := polynomial_kernel_has_finite_basis A
  rw [polynomial_kernel_basis_fraction_finrank A B]
  let Z := polynomialKernelBasisMatrix A B
  let Zx := Z.map (Polynomial.evalRingHom x)
  have heval (c : Fin r → K) :
      (fun i => ((Z*ᵥ(fun j => C (c j))) i).eval x)=Zx*ᵥc := by
    funext i
    simpa [Zx, Function.comp_def] using
      RingHom.map_mulVec (Polynomial.evalRingHom x) Z (fun j => C (c j)) i
  have hker (c : Fin r → K) : A*ᵥ(Z*ᵥ(fun j => C (c j)))=0 := by
    rw [Matrix.mulVec_mulVec,polynomialKernelBasisMatrix_mul,Matrix.zero_mulVec]
  let g : (Fin r → K) →ₗ[K] T :=
    (f.comp (Matrix.toLin' Zx)).codRestrict T (by
      intro c
      change f (Zx*ᵥc) ∈ T
      rw [← heval c]
      exact hmem _ (hker c))
  have hg : Function.Injective g := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    have hfc : f (Zx*ᵥc)=0 := congrArg Subtype.val hc
    rw [← heval c] at hfc
    have hz := hzero _ (hker c) hfc
    rw [heval] at hz
    exact (polynomialKernelBasisMatrix_pointwise_injective A B x)
      (hz.trans (Matrix.mulVec_zero Zx).symm)
  simpa only [Module.finrank_fintype_fun_eq_card] using
    LinearMap.finrank_le_finrank_of_injective hg

theorem polynomial_deformation_nullity_le_of_evaluation_mem
    (A : Matrix a b K[X]) (x : K) (T : Submodule K (b → K))
    (hmem : ∀ v : b → K[X], A*ᵥv=0 → (fun i => (v i).eval x) ∈ T) :
    Module.finrank F (LinearMap.ker (Matrix.toLin' (A.map (algebraMap K[X] F)))) ≤
      Module.finrank K T :=
  polynomial_deformation_nullity_le_of_residue_map A x LinearMap.id T
    hmem (fun _ _ h => h)

end FD56

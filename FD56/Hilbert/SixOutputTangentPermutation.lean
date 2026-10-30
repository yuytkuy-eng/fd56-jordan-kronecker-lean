/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.SixOutputTangentPermutation
import FD56.Hilbert.KernelDimension

/-! The fixed row permutation exchanging the two normalized endpoint pairs
preserves every bounded tangent-kernel dimension. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
attribute [local irreducible] sixOutputPluckerTangent twoColumnWedge

private theorem swapped_coordinates_add {V : Type*} [AddCommGroup V]
    (z w : Fin 15 → V) :
    sixOutputTailSwapCoordinates (z+w)=sixOutputTailSwapCoordinates z+sixOutputTailSwapCoordinates w := by
  funext j
  fin_cases j <;> simp [sixOutputTailSwapCoordinates] <;> abel

private theorem swapped_coordinates_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (c : K) (z : Fin 15 → V) :
    sixOutputTailSwapCoordinates (c • z)=c • sixOutputTailSwapCoordinates z := by
  funext j
  fin_cases j <;> simp [sixOutputTailSwapCoordinates]

private theorem swapped_bound_val {K : Type*} [Field K]
    (d : ℕ) (z : Fin 15 → BoundedPoly K d) :
    (fun j => (sixOutputTailSwapCoordinates z j).val)=
      sixOutputTailSwapCoordinates (fun j => (z j).val) := by
  funext j
  fin_cases j <;> rfl

private def boundedKernelSwapMap {K : Type*} [Field K]
    (u v : Fin 6 → K[X]) (d : ℕ) :
    polynomialKernelAtDegree (sixOutputPluckerTangent (twoColumnWedge u v)) d →ₗ[K]
      polynomialKernelAtDegree (sixOutputPluckerTangent
        (twoColumnWedge (u ∘ sixOutputTailSwap) (v ∘ sixOutputTailSwap))) d where
  toFun z := ⟨sixOutputTailSwapCoordinates z.val,by
    change _*ᵥ(fun j => (sixOutputTailSwapCoordinates z.val j).val)=0
    rw [swapped_bound_val]
    exact sixOutputPluckerTangent_tailSwap_kernel u v _ z.property⟩
  map_add' z w := Subtype.ext (swapped_coordinates_add z.val w.val)
  map_smul' c z := Subtype.ext (swapped_coordinates_smul c z.val)

private theorem boundedKernelSwapMap_bijective {K : Type*} [Field K]
    (u v : Fin 6 → K[X]) (d : ℕ) : Function.Bijective (boundedKernelSwapMap u v d) := by
  constructor
  · intro z w h
    apply Subtype.ext
    have he := congrArg (fun x => sixOutputTailSwapCoordinates x.val) h
    exact (sixOutputTailSwapCoordinates_involutive z.val).symm.trans
      (he.trans (sixOutputTailSwapCoordinates_involutive w.val))
  · intro z
    have hu : (u ∘ sixOutputTailSwap) ∘ sixOutputTailSwap=u := by
      funext i
      exact congrArg u (sixOutputTailSwap_involutive i)
    have hv : (v ∘ sixOutputTailSwap) ∘ sixOutputTailSwap=v := by
      funext i
      exact congrArg v (sixOutputTailSwap_involutive i)
    have hz : sixOutputPluckerTangent (twoColumnWedge u v)*ᵥ
        sixOutputTailSwapCoordinates (fun j => (z.val j).val)=0 := by
      simpa only [hu,hv] using sixOutputPluckerTangent_tailSwap_kernel
        (u ∘ sixOutputTailSwap) (v ∘ sixOutputTailSwap) (fun j => (z.val j).val) z.property
    refine ⟨⟨sixOutputTailSwapCoordinates z.val,?_⟩,?_⟩
    · change _*ᵥ(fun j => (sixOutputTailSwapCoordinates z.val j).val)=0
      rw [swapped_bound_val]
      exact hz
    · apply Subtype.ext
      exact sixOutputTailSwapCoordinates_involutive z.val

theorem six_output_tail_swap_kernel_finrank {K : Type*} [Field K]
    (u v : Fin 6 → K[X]) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (sixOutputPluckerTangent
      (twoColumnWedge (u ∘ sixOutputTailSwap) (v ∘ sixOutputTailSwap))) d)=
      Module.finrank K (polynomialKernelAtDegree
        (sixOutputPluckerTangent (twoColumnWedge u v)) d) :=
  (LinearEquiv.ofBijective (boundedKernelSwapMap u v d)
    (boundedKernelSwapMap_bijective u v d)).finrank_eq.symm

end FD56

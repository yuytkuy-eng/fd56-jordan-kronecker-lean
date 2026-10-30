/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.SixOutputTripleTangentPermutation
import FD56.Hilbert.KernelDimension

/-! Exchanging endpoint blocks preserves every bounded triple tangent-kernel dimension. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
attribute [local irreducible] sixOutputTriplePluckerTangent sixOutputTriplePluckerMinors

private def tripleKernelSwapMap {K : Type*} [Field K]
    (G : Matrix (Fin 6) (Fin 3) K[X]) (d : ℕ) :
    polynomialKernelAtDegree (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G)) d →ₗ[K]
      polynomialKernelAtDegree (sixOutputTriplePluckerTangent
        (sixOutputTriplePluckerMinors (fun i j => G (sixOutputTripleTailSwap i) j))) d where
  toFun z := ⟨sixOutputTripleTailSwapCoordinates z.val,
    sixOutputTriplePluckerTangent_tailSwap_kernel G (fun j => (z.val j).val) z.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem tripleKernelSwapMap_bijective {K : Type*} [Field K]
    (G : Matrix (Fin 6) (Fin 3) K[X]) (d : ℕ) : Function.Bijective (tripleKernelSwapMap G d) := by
  constructor
  · intro z w h
    apply Subtype.ext
    have he := congrArg (fun x => sixOutputTripleTailSwapCoordinates x.val) h
    exact (sixOutputTripleTailSwapCoordinates_involutive z.val).symm.trans
      (he.trans (sixOutputTripleTailSwapCoordinates_involutive w.val))
  · intro z
    have hG : (fun i j => G (sixOutputTripleTailSwap (sixOutputTripleTailSwap i)) j)=G := by
      funext i j
      rw [sixOutputTripleTailSwap_involutive]
    have hz : sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G)*ᵥ
        sixOutputTripleTailSwapCoordinates (fun j => (z.val j).val)=0 := by
      simpa only [hG] using sixOutputTriplePluckerTangent_tailSwap_kernel
        (fun i j => G (sixOutputTripleTailSwap i) j) (fun j => (z.val j).val) z.property
    refine ⟨⟨sixOutputTripleTailSwapCoordinates z.val,hz⟩,?_⟩
    exact Subtype.ext (sixOutputTripleTailSwapCoordinates_involutive z.val)

theorem six_output_triple_tail_swap_kernel_finrank {K : Type*} [Field K]
    (G : Matrix (Fin 6) (Fin 3) K[X]) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (sixOutputTriplePluckerTangent
      (sixOutputTriplePluckerMinors (fun i j => G (sixOutputTripleTailSwap i) j))) d)=
      Module.finrank K (polynomialKernelAtDegree
        (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G)) d) :=
  (LinearEquiv.ofBijective (tripleKernelSwapMap G d)
    (tripleKernelSwapMap_bijective G d)).finrank_eq.symm

end FD56

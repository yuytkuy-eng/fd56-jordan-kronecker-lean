/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FamilySLWitnessKernel
import FD56.Hilbert.UniformWitnessExtension

/-! The two high rows of the small mixed witness control its scalar relation. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

theorem familySLWitness_partial_scalar_obstruction
    (E : Matrix (Fin 2) (Fin 8) K[X]) (c : K[X]) (hE : DegreeBound E 1)
    (hrel : E * familySLWitness = (-c) •
      (fun i j => if i.castSucc = j then 1 else 0 : Matrix (Fin 2) (Fin 3) K[X])) :
    E = 0 ∧ c = 0 := by
  let E' : Matrix (Fin 3) (Fin 8) K[X] := ![E 0,E 1,0]
  have hc : c = 0 := by
    apply familySLWitness_scalar_obstruction_of_rows E' c (hE 0) (hE 1)
    · intro j
      have h := congrArg (fun A : Matrix (Fin 2) (Fin 3) K[X] => A 0 j) hrel
      simpa [E',Matrix.mul_apply,Matrix.smul_apply,mul_ite] using h
    · intro j
      have h := congrArg (fun A : Matrix (Fin 2) (Fin 3) K[X] => A 1 j) hrel
      simpa [E',Matrix.mul_apply,Matrix.smul_apply,mul_ite] using h
  refine ⟨?_,hc⟩
  funext i
  apply familySLWitness_affine_kernel_zero (E i) (hE i)
  funext j
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 3) K[X] => A i j) hrel
  simpa [hc,Matrix.mulVec,dotProduct,Matrix.mul_apply,mul_comm] using h

theorem familySLWitness_eval_zero_injective :
    Function.Injective ((familySLWitness (K := K)).map (Polynomial.evalRingHom 0)).mulVec := by
  intro u v huv
  have h0 := congrFun huv (0 : Fin 8)
  have h2 := congrFun huv (2 : Fin 8)
  have h5 := congrFun huv (5 : Fin 8)
  simp [familySLWitness,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at h0 h2 h5
  funext j
  fin_cases j
  · simpa only [h5,add_left_inj] using h0
  · exact h2
  · exact h5

end FD56

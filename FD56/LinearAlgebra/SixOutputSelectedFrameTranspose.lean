/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.SelectedFrameTranspose
import FD56.LinearAlgebra.SixOutputPluckerTangent

/-! Upper coordinates retain row independence for alternating six-output frames. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000

theorem sixOutput_upper_entries_determine {R : Type*} [AddGroup R]
    (H J : Matrix (Fin 6) (Fin 6) R)
    (hHd : ∀ i, H i i=0) (hHs : ∀ i j, H j i= -H i j)
    (hJd : ∀ i, J i i=0) (hJs : ∀ i j, J j i= -J i j)
    (hupper : ∀ k, H (sixOutputPair k).1 (sixOutputPair k).2=
      J (sixOutputPair k).1 (sixOutputPair k).2) : H=J := by
  have hlt (i j : Fin 6) (hij : i<j) : H i j=J i j := by
    fin_cases i <;> fin_cases j <;> norm_num at hij ⊢
    all_goals first
      | exact hupper 0 | exact hupper 1 | exact hupper 2 | exact hupper 3
      | exact hupper 4 | exact hupper 5 | exact hupper 6 | exact hupper 7
      | exact hupper 8 | exact hupper 9 | exact hupper 10 | exact hupper 11
      | exact hupper 12 | exact hupper 13 | exact hupper 14
  funext i j
  rcases lt_trichotomy i j with hij|hij|hij
  · exact hlt i j hij
  · subst j; rw [hHd,hJd]
  · rw [hHs j i,hJs j i,hlt j i hij]

theorem sixOutput_transpose_upper_pairs_injective
    {R b : Type*} [CommRing R] [Fintype b]
    (C : Matrix b (Fin 6 × Fin 6) R)
    (hC : Function.Injective C.transpose.mulVec)
    (hd : ∀ t i, C t (i,i)=0)
    (hs : ∀ t i j, C t (j,i)= -C t (i,j)) :
    Function.Injective (C.submatrix id sixOutputPair).transpose.mulVec := by
  intro x y hxy
  apply hC
  have hd' (v : b → R) (i : Fin 6) : (C.transpose *ᵥ v) (i,i)=0 := by
    simp only [Matrix.mulVec,Matrix.transpose_apply,dotProduct,hd,zero_mul,Finset.sum_const_zero]
  have hs' (v : b → R) (i j : Fin 6) :
      (C.transpose *ᵥ v) (j,i)= -(C.transpose *ᵥ v) (i,j) := by
    change (∑ t, C t (j,i)*v t)= -(∑ t, C t (i,j)*v t)
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [hs t i j,neg_mul]
  have h := sixOutput_upper_entries_determine
    (fun i j => (C.transpose *ᵥ x) (i,j)) (fun i j => (C.transpose *ᵥ y) (i,j))
    (hd' x) (hs' x) (hd' y) (hs' y) (fun k => congrFun hxy k)
  funext ij
  exact congrFun (congrFun h ij.1) ij.2

end FD56

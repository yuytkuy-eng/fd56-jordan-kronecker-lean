/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.InteriorTerminalRowEquiv
import FD56.LinearAlgebra.SixOutputPluckerTangent
import FD56.LinearAlgebra.ComplementaryKernelMinorReindex

/-! Signed complementary quadruples for fifteen coordinates and nine selected minors. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000

def sixOutputComplementaryQuad : Fin 15 → Fin 4 → Fin 6 :=
  ![![2,3,4,5],![1,3,4,5],![1,2,4,5],![1,2,3,5],![1,2,3,4],![0,3,4,5],![0,2,4,5],![0,2,3,5],![0,2,3,4],![0,1,4,5],![0,1,3,5],![0,1,3,4],![0,1,2,5],![0,1,2,4],![0,1,2,3]]

def sixOutputComplementarySign : Fin 15 → ℤ := ![1,-1,1,-1,1,1,-1,1,-1,1,-1,1,1,-1,1]

private def complementaryPermutation (i : Fin 15) : Equiv.Perm (Fin 6) where
  toFun := (![![2,3,4,5,0,1],![1,3,4,5,0,2],![1,2,4,5,0,3],![1,2,3,5,0,4],![1,2,3,4,0,5],![0,3,4,5,1,2],![0,2,4,5,1,3],![0,2,3,5,1,4],![0,2,3,4,1,5],![0,1,4,5,2,3],![0,1,3,5,2,4],![0,1,3,4,2,5],![0,1,2,5,3,4],![0,1,2,4,3,5],![0,1,2,3,4,5]] : Fin 15 → Fin 6 → Fin 6) i
  invFun := (![![4,5,0,1,2,3],![4,0,5,1,2,3],![4,0,1,5,2,3],![4,0,1,2,5,3],![4,0,1,2,3,5],![0,4,5,1,2,3],![0,4,1,5,2,3],![0,4,1,2,5,3],![0,4,1,2,3,5],![0,1,4,5,2,3],![0,1,4,2,5,3],![0,1,4,2,3,5],![0,1,2,4,5,3],![0,1,2,4,3,5],![0,1,2,3,4,5]] : Fin 15 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

def sixOutputComplementaryRows (i : Fin 15) : (Fin 4 ⊕ Fin 2) ≃ Fin 6 :=
  finSumFinEquiv.trans (complementaryPermutation i)

theorem sixOutputComplementaryRows_inl (i : Fin 15) (j : Fin 4) :
    sixOutputComplementaryRows i (Sum.inl j)=sixOutputComplementaryQuad i j := by
  revert i j
  decide +kernel

theorem sixOutputComplementaryRows_inr (i : Fin 15) (j : Fin 2) :
    sixOutputComplementaryRows i (Sum.inr j)=
      ![(sixOutputPair i).1,(sixOutputPair i).2] j := by
  revert i j
  decide +kernel

theorem sixOutputComplementaryRows_sign (i : Fin 15) :
    (Equiv.Perm.sign ((sixOutputComplementaryRows i).trans
      (finSumFinEquiv : (Fin 4 ⊕ Fin 2) ≃ Fin 6).symm) : ℤ)=
      sixOutputComplementarySign i := by
  revert i
  decide +kernel

theorem sixOutputComplementarySign_sq (i : Fin 15) :
    sixOutputComplementarySign i*sixOutputComplementarySign i=1 := by
  revert i
  decide +kernel

def sixOutputCorankTwoSelectedPair (z : Option (Fin 4 × Fin 2)) : Fin 15 :=
  match z with
  | none => 14
  | some (a,b) => (![![4,3],![8,7],![11,10],![13,12]] : Fin 4 → Fin 2 → Fin 15) a b

def sixOutputCorankTwoSelectedSign (z : Option (Fin 4 × Fin 2)) : ℤ :=
  match z with
  | none => 1
  | some (_,b) => if b=0 then -1 else 1

theorem sixOutputCorankTwoSelectedPair_injective :
    Function.Injective sixOutputCorankTwoSelectedPair := by decide +kernel

theorem sixOutputCorankTwoSelectedSign_sq (z : Option (Fin 4 × Fin 2)) :
    sixOutputCorankTwoSelectedSign z*sixOutputCorankTwoSelectedSign z=1 := by
  revert z
  decide +kernel

private def selectedPermutation (z : Option (Fin 4 × Fin 2)) : Equiv.Perm (Fin 4) where
  toFun := match z with
    | none => id
    | some (a,_) => (![![3,0,1,2],![0,3,1,2],![0,1,3,2],![0,1,2,3]] : Fin 4 → Fin 4 → Fin 4) a
  invFun := match z with
    | none => id
    | some (a,_) => (![![1,2,3,0],![0,2,3,1],![0,1,3,2],![0,1,2,3]] : Fin 4 → Fin 4 → Fin 4) a
  left_inv := by revert z; decide +kernel
  right_inv := by revert z; decide +kernel

private theorem selected_permutation_rows (z : Option (Fin 4 × Fin 2)) (i : Fin 4) :
    interiorTerminalRow 4 2 z i=
      sixOutputComplementaryQuad (sixOutputCorankTwoSelectedPair z) (selectedPermutation z i) := by
  revert z i
  decide +kernel

private theorem selected_permutation_sign (z : Option (Fin 4 × Fin 2)) :
    (Equiv.Perm.sign (selectedPermutation z) : ℤ)=
      sixOutputCorankTwoSelectedSign z*sixOutputComplementarySign (sixOutputCorankTwoSelectedPair z) := by
  revert z
  decide +kernel

theorem six_output_corank_two_selected_det {R : Type*} [CommRing R]
    (G : Matrix (Fin 6) (Fin 4) R) (z : Option (Fin 4 × Fin 2)) :
    (G.submatrix (interiorTerminalRow 4 2 z) id).det=
      (sixOutputCorankTwoSelectedSign z : R)*
        (sixOutputComplementarySign (sixOutputCorankTwoSelectedPair z) : R)*
          (G.submatrix (sixOutputComplementaryQuad (sixOutputCorankTwoSelectedPair z)) id).det := by
  have he : G.submatrix (interiorTerminalRow 4 2 z) id=
      (G.submatrix (sixOutputComplementaryQuad (sixOutputCorankTwoSelectedPair z)) id).submatrix
        (selectedPermutation z) id := by
    funext i j
    simp only [Matrix.submatrix_apply,id_eq,selected_permutation_rows]
  rw [he,Matrix.det_permute]
  change (((Equiv.Perm.sign (selectedPermutation z) : ℤ) : R)*_)=_
  rw [selected_permutation_sign,Int.cast_mul]

theorem six_output_signed_complementary_minors_common_scalar {K : Type*} [Field K]
    (G : Matrix (Fin 6) (Fin 4) K[X]) (L : Matrix (Fin 4) (Fin 6) K[X])
    (hLG : L * G=1)
    (B : Basis (Fin 2) K[X] (LinearMap.ker (Matrix.toLin' G.transpose))) :
    ∃ c : K, c≠0 ∧ ∀ i : Fin 15,
      (sixOutputComplementarySign i : K[X]) *
          (G.submatrix (sixOutputComplementaryQuad i) id).det=
        C c * twoColumnWedge
          (fun j => polynomialKernelBasisMatrix G.transpose B j 0)
          (fun j => polynomialKernelBasisMatrix G.transpose B j 1)
          (sixOutputPair i).1 (sixOutputPair i).2 := by
  obtain ⟨c,hc,hm⟩ := polynomial_dual_basis_selected_complementary_minors (K:=K)
    G L hLG B (finSumFinEquiv : (Fin 4 ⊕ Fin 2) ≃ Fin 6).symm
    sixOutputComplementaryRows
  refine ⟨c,hc,?_⟩
  intro i
  have hi := hm i
  simp only [sixOutputComplementaryRows_inl,sixOutputComplementaryRows_inr,
    sixOutputComplementaryRows_sign,map_intCast] at hi
  have hs : (sixOutputComplementarySign i : K[X]) *
      (sixOutputComplementarySign i : K[X])=1 := by
    rw [← Int.cast_mul,sixOutputComplementarySign_sq,Int.cast_one]
  rw [hi,← mul_assoc,← mul_assoc,hs,one_mul]
  congr 1
  simp only [Matrix.det_fin_two,Matrix.submatrix_apply,id_eq,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,twoColumnWedge]
  ring

end FD56

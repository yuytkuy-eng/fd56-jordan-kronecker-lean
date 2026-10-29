/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.InteriorTerminalRowEquiv
import FD56.LinearAlgebra.FiveOutputPluckerTangent
import FD56.LinearAlgebra.ComplementaryKernelMinorReindex

/-! Ordered complementary triples for the ten five-output Plucker coordinates,
including the signs of the seven selected interior minors. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxHeartbeats 2000000

def fiveOutputComplementaryTriple : Fin 10 → Fin 3 → Fin 5 :=
  ![![2,3,4],![1,3,4],![1,2,4],![1,2,3],![0,3,4],
    ![0,2,4],![0,2,3],![0,1,4],![0,1,3],![0,1,2]]

def fiveOutputComplementarySign : Fin 10 → ℤ :=
  ![1,-1,1,-1,1,-1,1,1,-1,1]

private def complementaryPermutation (i : Fin 10) : Equiv.Perm (Fin 5) where
  toFun := (![![2,3,4,0,1],![1,3,4,0,2],![1,2,4,0,3],![1,2,3,0,4],
    ![0,3,4,1,2],![0,2,4,1,3],![0,2,3,1,4],![0,1,4,2,3],
    ![0,1,3,2,4],![0,1,2,3,4]] : Fin 10 → Fin 5 → Fin 5) i
  invFun := (![![3,4,0,1,2],![3,0,4,1,2],![3,0,1,4,2],![3,0,1,2,4],
    ![0,3,4,1,2],![0,3,1,4,2],![0,3,1,2,4],![0,1,3,4,2],
    ![0,1,3,2,4],![0,1,2,3,4]] : Fin 10 → Fin 5 → Fin 5) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

def fiveOutputComplementaryRows (i : Fin 10) : (Fin 3 ⊕ Fin 2) ≃ Fin 5 :=
  finSumFinEquiv.trans (complementaryPermutation i)

theorem fiveOutputComplementaryRows_inl (i : Fin 10) (j : Fin 3) :
    fiveOutputComplementaryRows i (Sum.inl j)=fiveOutputComplementaryTriple i j := by
  revert i j
  decide +kernel

theorem fiveOutputComplementaryRows_inr (i : Fin 10) (j : Fin 2) :
    fiveOutputComplementaryRows i (Sum.inr j)=
      ![(fiveOutputPair i).1,(fiveOutputPair i).2] j := by
  revert i j
  decide +kernel

theorem fiveOutputComplementaryRows_sign (i : Fin 10) :
    (Equiv.Perm.sign ((fiveOutputComplementaryRows i).trans
      (finSumFinEquiv : (Fin 3 ⊕ Fin 2) ≃ Fin 5).symm) : ℤ)=
      fiveOutputComplementarySign i := by
  revert i
  decide +kernel

theorem fiveOutputComplementarySign_sq (i : Fin 10) :
    fiveOutputComplementarySign i * fiveOutputComplementarySign i=1 := by
  revert i
  decide +kernel

def fiveOutputCorankTwoSelectedPair (z : Option (Fin 3 × Fin 2)) : Fin 10 :=
  match z with
  | none => 9
  | some (a,b) => (![![3,2],![6,5],![8,7]] : Fin 3 → Fin 2 → Fin 10) a b

def fiveOutputCorankTwoSelectedSign (z : Option (Fin 3 × Fin 2)) : ℤ :=
  match z with
  | none => 1
  | some (_,b) => if b=0 then -1 else 1

theorem fiveOutputCorankTwoSelectedPair_injective :
    Function.Injective fiveOutputCorankTwoSelectedPair := by
  decide +kernel

theorem fiveOutputCorankTwoSelectedSign_sq (z : Option (Fin 3 × Fin 2)) :
    fiveOutputCorankTwoSelectedSign z * fiveOutputCorankTwoSelectedSign z=1 := by
  revert z
  decide +kernel

theorem five_output_corank_two_selected_det {R : Type*} [CommRing R]
    (G : Matrix (Fin 5) (Fin 3) R) (z : Option (Fin 3 × Fin 2)) :
    (G.submatrix (interiorTerminalRow 3 2 z) id).det=
      (fiveOutputCorankTwoSelectedSign z : R) *
        (fiveOutputComplementarySign (fiveOutputCorankTwoSelectedPair z) : R) *
          (G.submatrix (fiveOutputComplementaryTriple (fiveOutputCorankTwoSelectedPair z)) id).det := by
  cases z with
  | none => simp [fiveOutputCorankTwoSelectedSign,fiveOutputCorankTwoSelectedPair,
      fiveOutputComplementarySign,fiveOutputComplementaryTriple,interiorTerminalRow,
      Matrix.det_fin_three]
  | some ab =>
    rcases ab with ⟨a,b⟩
    fin_cases a <;> fin_cases b <;>
      simp [fiveOutputCorankTwoSelectedSign,fiveOutputCorankTwoSelectedPair,
        fiveOutputComplementarySign,fiveOutputComplementaryTriple,interiorTerminalRow,
        Matrix.det_fin_three] <;> ring

theorem five_output_signed_complementary_minors_common_scalar {K : Type*} [Field K]
    (G : Matrix (Fin 5) (Fin 3) K[X]) (L : Matrix (Fin 3) (Fin 5) K[X])
    (hLG : L * G=1)
    (B : Basis (Fin 2) K[X] (LinearMap.ker (Matrix.toLin' G.transpose))) :
    ∃ c : K, c≠0 ∧ ∀ i : Fin 10,
      (fiveOutputComplementarySign i : K[X]) *
          (G.submatrix (fiveOutputComplementaryTriple i) id).det=
        C c * twoColumnWedge
          (fun j => polynomialKernelBasisMatrix G.transpose B j 0)
          (fun j => polynomialKernelBasisMatrix G.transpose B j 1)
          (fiveOutputPair i).1 (fiveOutputPair i).2 := by
  obtain ⟨c,hc,hm⟩ := polynomial_dual_basis_selected_complementary_minors (K:=K)
    G L hLG B (finSumFinEquiv : (Fin 3 ⊕ Fin 2) ≃ Fin 5).symm
    fiveOutputComplementaryRows
  refine ⟨c,hc,?_⟩
  intro i
  have hi := hm i
  simp only [fiveOutputComplementaryRows_inl,fiveOutputComplementaryRows_inr,
    fiveOutputComplementaryRows_sign,map_intCast] at hi
  have hs : (fiveOutputComplementarySign i : K[X]) *
      (fiveOutputComplementarySign i : K[X])=1 := by
    rw [← Int.cast_mul,fiveOutputComplementarySign_sq,Int.cast_one]
  rw [hi,← mul_assoc,← mul_assoc,hs,one_mul]
  congr 1
  simp only [Matrix.det_fin_two,Matrix.submatrix_apply,id_eq,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,twoColumnWedge]
  ring

end FD56

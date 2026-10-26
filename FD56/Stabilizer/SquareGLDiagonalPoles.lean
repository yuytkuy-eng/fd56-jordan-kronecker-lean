/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLKirillovPencil
import FD56.Hilbert.RegularPoleBlocks
import FD56.Hilbert.StarCouplingDecomposition

/-! The actual square GL Kirillov pencil with diagonal row pencil has
star-shaped resonant couplings. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

def squareGLPoleIndex (n : Type*) : ((n × n) ⊕ (n × n)) ≃ SLInput n n :=
  Equiv.sumCongr (Equiv.prodComm n n) (Equiv.refl (n × n))

def squareGLCommutatorBlock (M : Matrix n n R) : Matrix (n × n) (n × n) R :=
  fun i j => (if j.1=i.2 then M i.1 j.2 else 0) - if i.1=j.2 then M j.1 i.2 else 0

omit [Fintype n] in
theorem squareGLCommutatorBlock_skew (M : Matrix n n R) :
    (squareGLCommutatorBlock M).transpose = -squareGLCommutatorBlock M := by
  ext i j
  simp only [squareGLCommutatorBlock,Matrix.transpose_apply,Matrix.neg_apply]
  ring

omit [Fintype n] in
theorem squareGLCommutatorBlock_diag_zero (M : Matrix n n R) (i : n × n) :
    squareGLCommutatorBlock M i i = 0 := by
  simp [squareGLCommutatorBlock]

theorem glKirillovMatrix_diagonal_reindex (M : Matrix n n R) (p : n → R) :
    (glKirillovMatrix M (Matrix.diagonal p)).submatrix
        (squareGLPoleIndex n) (squareGLPoleIndex n) =
      Matrix.fromBlocks (squareGLCommutatorBlock M)
        (-(Matrix.diagonal (fun i : n × n => p i.2)))
        (Matrix.diagonal (fun i : n × n => p i.2)) 0 := by
  ext x y
  rcases x with ⟨i,j⟩ | ⟨i,j⟩ <;> rcases y with ⟨a,b⟩ | ⟨a,b⟩
  all_goals simp [glKirillovMatrix,squareGLPoleIndex,glTraceDualIndexEquiv,
    glEquationMatrix,LinearMap.toMatrix'_apply,glEquationLinearMap,matrixPairEquiv,
    stabilizerResidual,Matrix.mul_apply,Pi.single_apply,Matrix.submatrix_apply,
    squareGLCommutatorBlock,Matrix.diagonal_apply]
  all_goals split_ifs <;> simp_all [eq_comm]

def squareGLPartnerSign : Matrix ((n × n) ⊕ (n × n)) ((n × n) ⊕ (n × n)) R :=
  Matrix.fromBlocks 1 0 0 (-1)

theorem squareGLPartnerSign_inverse :
    squareGLPartnerSign (R := R) (n := n) * squareGLPartnerSign = 1 := by
  simp [squareGLPartnerSign,Matrix.fromBlocks_multiply,Matrix.fromBlocks_one]

theorem squareGLPartnerSign_congruence (A D : Matrix (n × n) (n × n) R) :
    (squareGLPartnerSign (R := R) (n := n)).transpose * Matrix.fromBlocks A (-D) D 0 *
      squareGLPartnerSign = Matrix.fromBlocks A D (-D) 0 := by
  simp [squareGLPartnerSign,Matrix.fromBlocks_transpose,Matrix.fromBlocks_multiply]

omit [Fintype n] in
theorem squareGLPartnerSign_map {S : Type*} [CommRing S] (f : R →+* S) :
    (squareGLPartnerSign (R := R) (n := n)).map f = squareGLPartnerSign := by
  ext i j
  cases i <;> cases j <;> simp [squareGLPartnerSign,Matrix.one_apply]

variable {K : Type*} [Field K]

omit [Fintype n] in
theorem squareGLCommutatorBlock_affine (A B : Matrix n n K) :
    squareGLCommutatorBlock (affineMatrixPencil A B) =
      affineMatrixPencil (squareGLCommutatorBlock A) (squareGLCommutatorBlock B) := by
  funext i j
  simp only [squareGLCommutatorBlock,affineMatrixPencil]
  split_ifs <;> simp <;> ring

omit [Fintype n] in
theorem squareGL_resonant_coupling (lam : n → K) (A B : Matrix n n K) (i : n) :
    regularLocalCoupling lam (squareGLCommutatorBlock A) (squareGLCommutatorBlock B) i =
      starCoupling i (fun j => -(A j i + lam i*B j i)) := by
  ext j k
  simp only [regularLocalCoupling,squareGLCommutatorBlock,starCoupling]
  split_ifs <;> ring

theorem squareGL_diagonal_constant_normalization (lam : n → K) (A B : Matrix n n K) :
    ∃ T S : Matrix (SLInput n n) (SLInput n n) K,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose * glKirillovMatrix (affineMatrixPencil A B)
          (Matrix.diagonal (fun i => X-C (lam i))) * T.map C =
        regularPolePencil (fun i : n × n => lam i.2)
          (squareGLCommutatorBlock A) (squareGLCommutatorBlock B) := by
  let e := squareGLPoleIndex n
  let Q := squareGLPartnerSign (R := K) (n := n)
  have hH : (glKirillovMatrix (affineMatrixPencil A B)
        (Matrix.diagonal (fun i => X-C (lam i)))).submatrix e e =
      Matrix.fromBlocks (affineMatrixPencil (squareGLCommutatorBlock A) (squareGLCommutatorBlock B))
        (-(regularPoleDiagonal (fun i : n × n => lam i.2)))
        (regularPoleDiagonal (fun i : n × n => lam i.2)) 0 := by
    rw [glKirillovMatrix_diagonal_reindex,squareGLCommutatorBlock_affine]
    rfl
  have hback : glKirillovMatrix (affineMatrixPencil A B)
        (Matrix.diagonal (fun i => X-C (lam i))) =
      (Matrix.fromBlocks (affineMatrixPencil (squareGLCommutatorBlock A) (squareGLCommutatorBlock B))
        (-(regularPoleDiagonal (fun i : n × n => lam i.2)))
        (regularPoleDiagonal (fun i : n × n => lam i.2)) 0).submatrix e.symm e.symm := by
    funext i j
    have h := congrFun (congrFun hH (e.symm i)) (e.symm j)
    simpa only [Matrix.submatrix_apply,Equiv.apply_symm_apply] using h
  refine ⟨Q.submatrix e.symm id,Q.submatrix id e.symm,?_,?_,?_⟩
  · change Q.submatrix e.symm (Equiv.refl _) * Q.submatrix (Equiv.refl _) e.symm = 1
    rw [Matrix.submatrix_mul_equiv,squareGLPartnerSign_inverse]
    exact Matrix.submatrix_one_equiv e.symm
  · rw [Matrix.submatrix_mul_equiv,squareGLPartnerSign_inverse,Matrix.submatrix_id_id]
  · rw [hback]
    change (Q.map C).transpose.submatrix id e.symm *
      (Matrix.fromBlocks (affineMatrixPencil (squareGLCommutatorBlock A) (squareGLCommutatorBlock B))
        (-(regularPoleDiagonal (fun i : n × n => lam i.2)))
        (regularPoleDiagonal (fun i : n × n => lam i.2)) 0).submatrix e.symm e.symm *
      (Q.map C).submatrix e.symm id = _
    rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,Matrix.submatrix_id_id]
    rw [squareGLPartnerSign_map,squareGLPartnerSign_congruence]
    rfl

theorem squareGL_diagonal_pole_decomposition (lam : n → K) (hlam : Function.Injective lam)
    (A B : Matrix n n K) :
    ∃ T : Matrix (SLInput n n) ((n ⊕ n) × n) K,
    ∃ S : Matrix ((n ⊕ n) × n) (SLInput n n) K,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose * glKirillovMatrix (affineMatrixPencil A B)
          (Matrix.diagonal (fun i => X-C (lam i))) * T.map C =
        Matrix.blockDiagonal (fun i => pairedCoupling
          ((starCoupling i (fun j => -(A j i+lam i*B j i))).map C) (X-C (lam i))) := by
  obtain ⟨T₀,S₀,hTS₀,hST₀,hcong₀⟩ := squareGL_diagonal_constant_normalization lam A B
  obtain ⟨T₁,S₁,hTS₁,hST₁,hcong₁⟩ := regular_pole_block_decomposition lam hlam
    (squareGLCommutatorBlock A) (squareGLCommutatorBlock B)
    (squareGLCommutatorBlock_skew A) (squareGLCommutatorBlock_skew B)
    (squareGLCommutatorBlock_diag_zero B)
  have hlocal : regularLocalPolePencil lam (squareGLCommutatorBlock A) (squareGLCommutatorBlock B) =
      fun i => pairedCoupling ((starCoupling i (fun j => -(A j i+lam i*B j i))).map C) (X-C (lam i)) := by
    funext i
    simp only [regularLocalPolePencil,squareGL_resonant_coupling,pairedCoupling]
  refine ⟨T₀*T₁,S₁*S₀,?_,?_,?_⟩
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc T₁,hTS₁,Matrix.one_mul,hTS₀]
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc S₀,hST₀,Matrix.one_mul,hST₁]
  · rw [Matrix.map_mul,Matrix.transpose_mul]
    calc
      _ = (T₁.map C).transpose *
          ((T₀.map C).transpose * glKirillovMatrix (affineMatrixPencil A B)
            (Matrix.diagonal (fun i => X-C (lam i))) * T₀.map C) * T₁.map C := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hcong₀,hcong₁,hlocal]

end FD56

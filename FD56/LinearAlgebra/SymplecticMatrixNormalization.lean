/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.AlternatingPivotSplit
import FD56.LinearAlgebra.FullKrylovBound

/-! Constant symplectic coordinates for a nondegenerate alternating matrix. -/

noncomputable section
namespace FD56
open Matrix

variable {K : Type*} [Field K]

def standardSymplecticMatrix (K : Type*) [Field K] (k : ℕ) :
    Matrix (Fin 2 × Fin k) (Fin 2 × Fin k) K :=
  Matrix.blockDiagonal (fun _ : Fin k => (![![0,1],![-1,0]] : Matrix (Fin 2) (Fin 2) K))

def symplecticSuccessorIndex (k : ℕ) :
    (Fin 2 × Fin (k+1)) ≃ (Fin 2 ⊕ (Fin 2 × Fin k)) where
  toFun ij := Fin.cases (Sum.inl ij.1) (fun j => Sum.inr (ij.1,j)) ij.2
  invFun
    | Sum.inl i => (i,0)
    | Sum.inr (i,j) => (i,j.succ)
  left_inv := by
    rintro ⟨i,j⟩
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  right_inv := by
    rintro (i | ⟨i,j⟩) <;> rfl

theorem standardSymplecticMatrix_successor (k : ℕ) :
    (Matrix.fromBlocks (![![0,1],![-1,0]] : Matrix (Fin 2) (Fin 2) K) 0 0
      (standardSymplecticMatrix K k)).submatrix (symplecticSuccessorIndex k)
        (symplecticSuccessorIndex k) = standardSymplecticMatrix K (k+1) := by
  ext ⟨i,j⟩ ⟨u,v⟩
  refine Fin.cases ?_ (fun j => ?_) j <;>
    refine Fin.cases ?_ (fun v => ?_) v <;>
    simp [symplecticSuccessorIndex,standardSymplecticMatrix,Matrix.blockDiagonal_apply,
      eq_comm]

theorem matrix_alternating_submatrix_equiv {n p : Type*} [Fintype n] [Fintype p]
    [DecidableEq n] [DecidableEq p] (A : Matrix n n K) (e : p ≃ n)
    (hA : ∀ v : n → K, v ⬝ᵥ (A *ᵥ v)=0) :
    ∀ v : p → K, v ⬝ᵥ (A.submatrix e e *ᵥ v)=0 := by
  intro v
  rw [Matrix.submatrix_mulVec_equiv,← comp_equiv_symm_dotProduct]
  exact hA (v ∘ e.symm)

theorem matrix_congruence_reindex {n p q r : Type*}
    [Fintype n] [Fintype p] [Fintype q] [Fintype r]
    [DecidableEq n] [DecidableEq p] [DecidableEq q] [DecidableEq r]
    (A : Matrix n n K) (B : Matrix p p K) (T : Matrix n p K) (U : Matrix p n K)
    (hTU : T*U=1) (hUT : U*T=1) (hAB : T.transpose*A*T=B)
    (e : q ≃ n) (f : r ≃ p) :
    T.submatrix e f * U.submatrix f e=1 ∧ U.submatrix f e * T.submatrix e f=1 ∧
      (T.submatrix e f).transpose * A.submatrix e e * T.submatrix e f=B.submatrix f f := by
  constructor
  · rw [Matrix.submatrix_mul_equiv,hTU]
    exact Matrix.submatrix_one_equiv e
  constructor
  · rw [Matrix.submatrix_mul_equiv,hUT]
    exact Matrix.submatrix_one_equiv f
  · change T.transpose.submatrix f e * A.submatrix e e * T.submatrix e f = _
    rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,hAB]

theorem alternating_nondegenerate_symplectic_normalization {n : Type*}
    [Fintype n] [DecidableEq n] (B : Matrix n n K)
    (hB : ∀ v : n → K, v ⬝ᵥ (B *ᵥ v)=0) (hdet : B.det≠0) :
    ∃ k : ℕ, Fintype.card n=2*k ∧
    ∃ T : Matrix n (Fin 2 × Fin k) K,
    ∃ U : Matrix (Fin 2 × Fin k) n K,
      T*U=1 ∧ U*T=1 ∧ T.transpose*B*T=standardSymplecticMatrix K k := by
  classical
  generalize hsize : Fintype.card n = N
  induction N using Nat.strong_induction_on generalizing n with
  | h N ih =>
    by_cases hz : Fintype.card n=0
    · letI : IsEmpty n := Fintype.card_eq_zero_iff.mp hz
      refine ⟨0,by omega,0,0,?_,?_,?_⟩ <;> ext i j <;> exact isEmptyElim i
    · haveI : Nonempty n := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hz)
      have hne : B≠0 := by intro he; simp [he] at hdet
      obtain ⟨i,hi⟩ := Function.ne_iff.mp hne
      obtain ⟨j,hij⟩ := Function.ne_iff.mp hi
      have hijd : i≠j := by
        intro he
        subst j
        exact hij (alternating_matrix_diag_zero B hB i)
      let r : Fin 2 ↪ n :=
        ⟨![i,j],by
          intro a b hab
          fin_cases a <;> fin_cases b
          · rfl
          · exact (hijd (by simpa using hab)).elim
          · exact (hijd (by simpa using hab.symm)).elim
          · rfl⟩
      let s := {k : n // k ∉ Set.range r}
      let e : (Fin 2 ⊕ s) ≃ n := coordinateEmbeddingSumEquiv r
      have hcard : 2+Fintype.card s=Fintype.card n := by
        simpa only [Fintype.card_sum,Fintype.card_fin] using Fintype.card_congr e
      let B' := B.submatrix e e
      have halt := matrix_alternating_submatrix_equiv B e hB
      have hpivot : B' (Sum.inl 0) (Sum.inl 1)≠0 := hij
      have hdet' : B'.det≠0 := by simpa only [B',Matrix.det_submatrix_equiv_self] using hdet
      obtain ⟨T,U,D,hTU,hUT,he,hD,hDdet⟩ := alternating_nondegenerate_pivot_split B' halt hpivot hdet'
      obtain ⟨k,hk,Q,R,hQR,hRQ,hQD⟩ := ih (Fintype.card s) (by omega) D hD hDdet rfl
      let F : Matrix (Fin 2 ⊕ s) (Fin 2 ⊕ (Fin 2 × Fin k)) K := Matrix.fromBlocks 1 0 0 Q
      let G : Matrix (Fin 2 ⊕ (Fin 2 × Fin k)) (Fin 2 ⊕ s) K := Matrix.fromBlocks 1 0 0 R
      have hFG : F*G=1 := by simp [F,G,Matrix.fromBlocks_multiply,hQR,Matrix.fromBlocks_one]
      have hGF : G*F=1 := by simp [F,G,Matrix.fromBlocks_multiply,hRQ,Matrix.fromBlocks_one]
      have hXU : (T*F)*(G*U)=1 := by
        rw [Matrix.mul_assoc,← Matrix.mul_assoc F,hFG,Matrix.one_mul,hTU]
      have hUX : (G*U)*(T*F)=1 := by
        rw [Matrix.mul_assoc,← Matrix.mul_assoc U,hUT,Matrix.one_mul,hGF]
      have hcong : (T*F).transpose*B'*(T*F)=
          Matrix.fromBlocks (![![0,1],![-1,0]] : Matrix (Fin 2) (Fin 2) K) 0 0
            (standardSymplecticMatrix K k) := by
        rw [Matrix.transpose_mul]
        calc
          _ = F.transpose*(T.transpose*B'*T)*F := by simp only [Matrix.mul_assoc]
          _ = _ := by
            rw [he]
            simp only [F,Matrix.fromBlocks_transpose,Matrix.transpose_zero,Matrix.transpose_one,
              Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,
              Matrix.one_mul,Matrix.mul_one,hQD]
      obtain ⟨h1,h2,h3⟩ := matrix_congruence_reindex B' _ (T*F) (G*U)
        hXU hUX hcong e.symm (symplecticSuccessorIndex k)
      refine ⟨k+1,by omega,(T*F).submatrix e.symm (symplecticSuccessorIndex k),
        (G*U).submatrix (symplecticSuccessorIndex k) e.symm,h1,h2,?_⟩
      simpa only [B',Matrix.submatrix_submatrix,Equiv.self_comp_symm,
        Matrix.submatrix_id_id,standardSymplecticMatrix_successor] using h3

end FD56

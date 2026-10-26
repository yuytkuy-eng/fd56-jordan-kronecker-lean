/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.PairedCouplingCongruence

/-! A nonzero decomposable local coupling gives one Jordan block of size four
and a direct sum of Jordan blocks of size two. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

def rankTwoRegularIndex (n : Type*) :
    ((Fin 2 ⊕ Fin 2) ⊕ ((Fin 1 ⊕ Fin 1) × n)) ≃ ((Fin 2 ⊕ n) ⊕ (Fin 2 ⊕ n)) where
  toFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr i) => .inr (.inl i)
    | .inr (.inl _,j) => .inl (.inr j)
    | .inr (.inr _,j) => .inr (.inr j)
  invFun
    | .inl (.inl i) => .inl (.inl i)
    | .inr (.inl i) => .inl (.inr i)
    | .inl (.inr j) => .inr (.inl 0,j)
    | .inr (.inr j) => .inr (.inr 0,j)
  left_inv x := by
    rcases x with (i|i) | ⟨(i|i),j⟩ <;> try rfl
    all_goals fin_cases i; rfl
  right_inv x := by rcases x with (i|i) | (i|i) <;> rfl

def rankTwoRegularTarget (a : K) :
    Matrix ((Fin 2 ⊕ Fin 2) ⊕ ((Fin 1 ⊕ Fin 1) × n))
      ((Fin 2 ⊕ Fin 2) ⊕ ((Fin 1 ⊕ Fin 1) × n)) K[X] :=
  Matrix.fromBlocks (skewJordanBlockPencil a 2) 0 0
    (Matrix.blockDiagonal (fun _ : n => skewJordanBlockPencil a 1))

omit [Fintype n] in
theorem rankTwoRegular_normalized_reindex (a : K) :
    (pairedCoupling
      ((Matrix.fromBlocks (![![0,1],![-1,0]] : Matrix (Fin 2) (Fin 2) K)
        0 0 (0 : Matrix n n K)).map C) (X-C a)).submatrix
          (rankTwoRegularIndex n) (rankTwoRegularIndex n) =
      Matrix.fromBlocks (rankTwoRegularCoupling (X-C a)) 0 0
        (Matrix.blockDiagonal (fun _ : n => skewJordanBlockPencil a 1)) := by
  funext i j
  rcases i with (i|i) | ⟨(i|i),u⟩ <;>
    rcases j with (j|j) | ⟨(j|j),v⟩ <;>
    simp [Matrix.submatrix_apply,rankTwoRegularIndex,pairedCoupling,
      rankTwoRegularCoupling,Matrix.blockDiagonal_apply,skewJordanBlockPencil,
      jordanUpperPencil,Matrix.one_apply]
  all_goals try { fin_cases i <;> fin_cases j <;> simp }
  all_goals split_ifs <;> simp_all
  all_goals have hij : j=i := Subsingleton.elim _ _; contradiction

theorem rankTwoRegular_constant_decomposition (a c : K) (hc : c≠0) (w : n → K) :
    ∃ T : Matrix ((Fin 2 ⊕ n) ⊕ (Fin 2 ⊕ n))
      ((Fin 2 ⊕ Fin 2) ⊕ ((Fin 1 ⊕ Fin 1) × n)) K,
    ∃ S : Matrix ((Fin 2 ⊕ Fin 2) ⊕ ((Fin 1 ⊕ Fin 1) × n))
      ((Fin 2 ⊕ n) ⊕ (Fin 2 ⊕ n)) K,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose * pairedCoupling ((rankTwoForm c w).map C) (X-C a) * T.map C =
        rankTwoRegularTarget (n := n) a := by
  obtain ⟨hQS,hSQ⟩ := rankTwoCoordinate_inverse c hc w
  obtain ⟨T₀,S₀,hTS,hST,hcong⟩ := pairedCoupling_constant_normalization
    (rankTwoForm c w) (rankTwoCoordinateChange c w) (rankTwoCoordinateInverse c w)
    _ hQS hSQ (rankTwoCoordinate_congruence c hc w) a
  obtain ⟨T₄,S₄,hT₄S₄,hS₄T₄,hfour⟩ := rankTwoRegularCoupling_constant_congruence a
  let r := (Fin 1 ⊕ Fin 1) × n
  let T₁ : Matrix ((Fin 2 ⊕ Fin 2) ⊕ r) ((Fin 2 ⊕ Fin 2) ⊕ r) K :=
    Matrix.fromBlocks T₄ 0 0 1
  let S₁ : Matrix ((Fin 2 ⊕ Fin 2) ⊕ r) ((Fin 2 ⊕ Fin 2) ⊕ r) K :=
    Matrix.fromBlocks S₄ 0 0 1
  have hTS₁ : T₁*S₁=1 := by simp [T₁,S₁,Matrix.fromBlocks_multiply,hT₄S₄,Matrix.fromBlocks_one]
  have hST₁ : S₁*T₁=1 := by simp [T₁,S₁,Matrix.fromBlocks_multiply,hS₄T₄,Matrix.fromBlocks_one]
  let e := rankTwoRegularIndex n
  let P := T₀.submatrix id e
  let Q := S₀.submatrix e id
  have hPQ : P*Q=1 := by
    dsimp [P,Q]
    rw [Matrix.submatrix_mul_equiv,hTS,Matrix.submatrix_id_id]
  have hQP : Q*P=1 := by
    change S₀.submatrix e (Equiv.refl _) * T₀.submatrix (Equiv.refl _) e = 1
    rw [Matrix.submatrix_mul_equiv,hST]
    exact Matrix.submatrix_one_equiv e
  have hpencil : (P.map C).transpose *
        pairedCoupling ((rankTwoForm c w).map C) (X-C a) * P.map C =
      Matrix.fromBlocks (rankTwoRegularCoupling (X-C a)) 0 0
        (Matrix.blockDiagonal (fun _ : n => skewJordanBlockPencil a 1)) := by
    have he : (P.map C).transpose *
          pairedCoupling ((rankTwoForm c w).map C) (X-C a) * P.map C =
        ((T₀.map C).transpose * pairedCoupling ((rankTwoForm c w).map C) (X-C a) *
          T₀.map C).submatrix e e := by
      change (T₀.map C).transpose.submatrix e (Equiv.refl _) *
        (pairedCoupling ((rankTwoForm c w).map C) (X-C a)).submatrix
          (Equiv.refl _) (Equiv.refl _) * (T₀.map C).submatrix (Equiv.refl _) e = _
      rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
    rw [he,hcong]
    exact rankTwoRegular_normalized_reindex a
  have hmapT : T₁.map C = Matrix.fromBlocks (T₄.map C) 0 0 (1 : Matrix r r K[X]) := by
    ext i j
    cases i <;> cases j <;> simp [T₁,Matrix.one_apply]
  have hfinal : (T₁.map C).transpose *
      Matrix.fromBlocks (rankTwoRegularCoupling (X-C a)) 0 0
        (Matrix.blockDiagonal (fun _ : n => skewJordanBlockPencil a 1)) * T₁.map C =
        rankTwoRegularTarget (n := n) a := by
    rw [hmapT]
    simp only [Matrix.fromBlocks_transpose,Matrix.transpose_zero,Matrix.transpose_one,
      Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,
      Matrix.one_mul,Matrix.mul_one,hfour,rankTwoRegularTarget]
  refine ⟨P*T₁,S₁*Q,?_,?_,?_⟩
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc T₁,hTS₁,Matrix.one_mul,hPQ]
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc Q,hQP,Matrix.one_mul,hST₁]
  · rw [Matrix.map_mul,Matrix.transpose_mul]
    calc
      _ = (T₁.map C).transpose *
          ((P.map C).transpose * pairedCoupling ((rankTwoForm c w).map C) (X-C a) * P.map C) *
          T₁.map C := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hpencil,hfinal]

end FD56

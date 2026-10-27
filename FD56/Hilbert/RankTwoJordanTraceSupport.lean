/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.NilpotentRankTwoJordan

/-! A functional annihilating the pole kernels is supported on two coordinates per pole. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K a : Type*} [Field K] [Fintype a] [DecidableEq a]

theorem rankTwoJordanPencil_pole_zero_column (x : K) (k : ℕ)
    (j : rankTwoJordanIndex k)
    (hx : j≠Sum.inl (Sum.inl 0)) (hy : j≠Sum.inl (Sum.inr 1)) :
    ∀ i, (rankTwoJordanPencil x k i j).eval x=0 := by
  intro i
  rcases j with j | ⟨j,b⟩
  · rcases j with j | j
    · fin_cases j
      · exact (hx rfl).elim
      · rcases i with i | i
        · rcases i with i | i <;> fin_cases i <;>
            simp [rankTwoJordanPencil,skewJordanBlockPencil,jordanUpperPencil]
        · simp [rankTwoJordanPencil]
    · fin_cases j
      · rcases i with i | i
        · rcases i with i | i <;> fin_cases i <;>
            simp [rankTwoJordanPencil,skewJordanBlockPencil,jordanUpperPencil]
        · simp [rankTwoJordanPencil]
      · exact (hy rfl).elim
  · rcases i with i | ⟨i,c⟩
    · simp [rankTwoJordanPencil]
    · rcases i with i | i <;> rcases j with j | j <;>
        fin_cases i <;> fin_cases j <;>
        simp [rankTwoJordanPencil,Matrix.blockDiagonal_apply,skewJordanBlockPencil,
          jordanUpperPencil] <;> split_ifs <;> simp

theorem rank_two_jordan_sum_pole_kernel_single (lam : a → K) (k : ℕ)
    (b : a) (j : rankTwoJordanIndex k)
    (hx : j≠Sum.inl (Sum.inl 0)) (hy : j≠Sum.inl (Sum.inr 1)) :
    ((Matrix.blockDiagonal' (fun c : a => rankTwoJordanPencil (lam c) k)).map
      (Polynomial.evalRingHom (lam b))) *ᵥ Pi.single ⟨b,j⟩ 1=0 := by
  rw [Matrix.mulVec_single_one]
  funext i
  rcases i with ⟨c,i⟩
  by_cases hc : c=b
  · subst c
    simpa only [Matrix.transpose_apply,Matrix.map_apply,Matrix.blockDiagonal'_apply_eq,Pi.zero_apply,
      Polynomial.coe_evalRingHom] using rankTwoJordanPencil_pole_zero_column (lam b) k j hx hy i
  · simp [Matrix.map_apply,Matrix.blockDiagonal'_apply_ne _ _ _ hc]

theorem rank_two_jordan_sum_functional_coefficient_zero (lam : a → K) (k : ℕ)
    (ell : ((Σ _ : a, rankTwoJordanIndex k) → K) →ₗ[K] K)
    (hell : ∀ b v, ((Matrix.blockDiagonal' (fun c : a => rankTwoJordanPencil (lam c) k)).map
      (Polynomial.evalRingHom (lam b))) *ᵥ v=0 → ell v=0)
    (b : a) (j : rankTwoJordanIndex k)
    (hx : j≠Sum.inl (Sum.inl 0)) (hy : j≠Sum.inl (Sum.inr 1)) :
    ell (Pi.single ⟨b,j⟩ 1)=0 :=
  hell b _ (rank_two_jordan_sum_pole_kernel_single lam k b j hx hy)

theorem rank_two_jordan_sum_functional_sparse (lam : a → K) (k : ℕ)
    (ell : ((Σ _ : a, rankTwoJordanIndex k) → K) →ₗ[K] K)
    (hell : ∀ b v, ((Matrix.blockDiagonal' (fun c : a => rankTwoJordanPencil (lam c) k)).map
      (Polynomial.evalRingHom (lam b))) *ᵥ v=0 → ell v=0)
    (v : (Σ _ : a, rankTwoJordanIndex k) → K) :
    ell v=∑ b : a, (
      ell (Pi.single ⟨b,Sum.inl (Sum.inl 0)⟩ 1)*v ⟨b,Sum.inl (Sum.inl 0)⟩+
      ell (Pi.single ⟨b,Sum.inl (Sum.inr 1)⟩ 1)*v ⟨b,Sum.inl (Sum.inr 1)⟩) := by
  have hzero := rank_two_jordan_sum_functional_coefficient_zero lam k ell hell
  have hsingle (i : Σ _ : a, rankTwoJordanIndex k) (x : K) :
      (Pi.single i x : (Σ _ : a, rankTwoJordanIndex k) → K)=
        x•(Pi.single i 1 : (Σ _ : a, rankTwoJordanIndex k) → K) := by
    funext j
    by_cases h : j=i
    · subst j
      simp
    · simp [Pi.single_apply,h]
  calc
    ell v = ∑ i, ell (Pi.single i 1)*v i := by
      conv_lhs => rw [← Finset.univ_sum_single v]
      rw [_root_.map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hsingle,_root_.map_smul]
      exact mul_comm _ _
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro b _
      rw [Fintype.sum_sum_type]
      have htail : (∑ j : (Fin 1 ⊕ Fin 1) × Fin k,
          ell (Pi.single ⟨b,Sum.inr j⟩ 1)*v ⟨b,Sum.inr j⟩)=0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [hzero b (Sum.inr j) (by simp) (by simp),zero_mul]
      rw [htail,add_zero,Fintype.sum_sum_type]
      have hx1 : ell (Pi.single ⟨b,Sum.inl (Sum.inl 1)⟩ 1)=0 :=
        hzero b _ (by simp) (by simp)
      have hy0 : ell (Pi.single ⟨b,Sum.inl (Sum.inr 0)⟩ 1)=0 :=
        hzero b _ (by simp) (by simp)
      simp [Fin.sum_univ_succ,hx1,hy0]

end FD56

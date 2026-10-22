/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FamilySLWitnessKernel
import FD56.Hilbert.ScalarBlockObstruction
import FD56.Hilbert.MiddleSLHilbert
import FD56.Hilbert.MiddleGLShift
import FD56.Hilbert.MiddleBetaWitness
import FD56.Hilbert.RepeatedKernel
import FD56.Hilbert.SLReindex

/-! Realization of the repeated sparse auxiliary matrix by affine full
SL pencils in dimensions `(11k,8k)`. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

def familySLBlockLengths (k : ℕ) (i : Fin k × Fin 3) : ℕ := ![3, 3, 2] i.2

abbrev FamilySLRows (k : ℕ) := Σ i : Fin k × Fin 3, Fin (familySLBlockLengths k i)
abbrev FamilySLColumns (k : ℕ) := Σ i : Fin k × Fin 3, Fin (familySLBlockLengths k i + 1)

theorem familySLRows_card (k : ℕ) : Fintype.card (FamilySLRows k) = 8 * k := by
  simp [FamilySLRows, Fintype.card_sigma, Fintype.sum_prod_type,
    familySLBlockLengths, Fin.sum_univ_succ, Nat.mul_comm]

theorem familySLColumns_card (k : ℕ) : Fintype.card (FamilySLColumns k) = 11 * k := by
  simp [FamilySLColumns, Fintype.card_sigma, Fintype.sum_prod_type,
    familySLBlockLengths, Fin.sum_univ_succ, Nat.mul_comm]

def familySLRowEquiv (k : ℕ) : FamilySLRows k ≃ Fin k × Fin 8 :=
  Fintype.equivOfCardEq (by rw [familySLRows_card]; simp [Nat.mul_comm])

def familySLRepeatedWitness (k : ℕ) : Matrix (FamilySLRows k) (Fin k × Fin 3) K[X] :=
  (repeatedBlockMatrix (Fin k) (familySLWitness (K := K))).submatrix
    (familySLRowEquiv k) (Equiv.refl _)

theorem familySLBlockLengths_adjacent (k : ℕ) (i j : Fin k × Fin 3) :
    familySLBlockLengths k i ≤ familySLBlockLengths k j + 1 := by
  rcases i with ⟨i, x⟩
  rcases j with ⟨j, y⟩
  fin_cases x <;> fin_cases y <;> norm_num [familySLBlockLengths]

theorem familySLRepeatedWitness_column_degree (k : ℕ) :
    ∀ x j, (familySLRepeatedWitness (K := K) k x j).natDegree ≤
      familySLBlockLengths k j + 2 := by
  intro x j
  have h := repeatedBlockMatrix_column_degree (Fin k) (familySLWitness (K := K))
    ![5, 5, 4] familySLWitness_column_degree (familySLRowEquiv k x) j
  change (familySLRepeatedWitness (K := K) k x j).natDegree ≤ ![5, 5, 4] j.2 at h
  rcases j with ⟨i, j⟩
  fin_cases j <;> exact h

theorem polynomial_mulVec_injective_of_leading {a b : Type*} [Fintype b]
    (G : Matrix a b K[X]) (e : b → ℕ)
    (hG : ∀ x j, (G x j).natDegree ≤ e j)
    (hlead : Function.Injective (Matrix.mulVec (fun x j => (G x j).coeff (e j)))) :
    Function.Injective G.mulVec := by
  intro u v h
  by_contra huv
  obtain ⟨_, x, _, hx⟩ := predictable_weighted_degree G e (u - v) hG hlead
    (sub_ne_zero.mpr huv)
  apply hx
  rw [Matrix.mulVec_sub, h, sub_self]
  rfl

theorem familySLRepeatedWitness_injective (k : ℕ) :
    Function.Injective (familySLRepeatedWitness (K := K) k).mulVec := by
  have hi := repeatedBlockMatrix_mulVec_injective (Fin k) (familySLWitness (K := K))
    (polynomial_mulVec_injective_of_leading familySLWitness ![5, 5, 4]
      familySLWitness_column_degree familySLWitness_leading_injective)
  intro u v h
  apply hi
  funext x
  have hh := congrFun h ((familySLRowEquiv k).symm x)
  simpa only [familySLRepeatedWitness, Matrix.submatrix_mulVec_equiv,
    Function.comp_apply, Equiv.refl_symm, Equiv.refl_apply, Equiv.apply_symm_apply] using hh

theorem blockMonomialKernel_column_degree {r : Type*} [Fintype r] [DecidableEq r]
    (e : r → ℕ) : ∀ x j, (blockMonomialKernel (K := K) e x j).natDegree ≤ e j := by
  intro x j
  by_cases h : x.1 = j
  · subst j
    simpa [blockMonomialKernel] using Nat.le_of_lt_succ x.2.isLt
  · simp [blockMonomialKernel, h]

theorem blockMonomialKernel_leading_injective {r : Type*} [Fintype r] [DecidableEq r]
    (e : r → ℕ) : Function.Injective (Matrix.mulVec
      (fun x j => (blockMonomialKernel (K := K) e x j).coeff (e j))) := by
  have hcoeff (i : r) : ((-Polynomial.X : K[X]) ^ e i).coeff (e i) = (-1 : K) ^ e i := by
    have hn : ((-Polynomial.X : K[X]) ^ e i).natDegree = e i := by simp
    calc
      _ = ((-Polynomial.X : K[X]) ^ e i).leadingCoeff := by
        simpa only [hn] using
          (Polynomial.coeff_natDegree (p := (-Polynomial.X : K[X]) ^ e i))
      _ = _ := by simp
  have hrow (v : r → K) (i : r) :
      (Matrix.mulVec (fun x j => (blockMonomialKernel (K := K) e x j).coeff (e j)) v)
        ⟨i, Fin.last (e i)⟩ = (-1 : K) ^ e i * v i := by
    simp only [Matrix.mulVec, dotProduct, blockMonomialKernel, Fin.val_last]
    rw [Fintype.sum_eq_single i]
    · simp [hcoeff]
    · intro j hj
      simp [Ne.symm hj]
  intro u v h
  funext i
  have hh := congrFun h ⟨i, Fin.last (e i)⟩
  rw [hrow, hrow] at hh
  exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hh

theorem familySLRepeatedWitness_scalar_obstruction (k : ℕ) (hk : 0 < k)
    (E : Matrix (Fin k × Fin 3) (FamilySLRows k) K[X]) (c : K[X])
    (hE : ∀ i j, E i j = 0 ∨ (familySLBlockLengths k i + 1 ≤ 5 ∧
      (E i j).natDegree ≤ 5 - (familySLBlockLengths k i + 1)))
    (hrel : E * familySLRepeatedWitness k =
      (-c) • (1 : Matrix (Fin k × Fin 3) (Fin k × Fin 3) K[X])) : c = 0 := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let E' := E.submatrix (Equiv.refl _) (familySLRowEquiv k).symm
  apply repeatedBlockMatrix_scalar_obstruction (Fin k) (familySLWitness (K := K))
    ![1, 1, 2] familySLWitness_weighted_scalar_obstruction E' c
  · intro i j
    have he := hE i ((familySLRowEquiv k).symm j)
    change (E i ((familySLRowEquiv k).symm j)).natDegree ≤ ![1, 1, 2] i.2
    rcases he with hz | ⟨_, hd⟩
    · simp [hz]
    · rcases i with ⟨i, x⟩
      fin_cases x <;> exact hd
  · have hh := hrel
    change E * (repeatedBlockMatrix (Fin k) familySLWitness).submatrix
      (familySLRowEquiv k) (Equiv.refl _) =
        (-c) • (1 : Matrix (Fin k × Fin 3) (Fin k × Fin 3) K[X]) at hh
    have hE' : E'.submatrix (Equiv.refl _) (familySLRowEquiv k) = E := by
      funext i j
      simp [E']
    rw [← hE', Matrix.submatrix_mul_equiv] at hh
    simpa only [Matrix.submatrix_id_id, Equiv.coe_refl] using hh

theorem familySLRepeatedWitness_kernel_hilbert (k d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (familySLRepeatedWitness (K := K) k).transpose d) =
      k * Module.finrank K (polynomialKernelAtDegree (familySLWitness (K := K)).transpose d) := by
  change Module.finrank K (polynomialKernelAtDegree
    ((repeatedBlockMatrix (Fin k) (familySLWitness (K := K))).transpose.submatrix
      (Equiv.refl _) (familySLRowEquiv k)) d) = _
  rw [reindex_kernel_hilbert, repeatedBlockMatrix_transpose, repeatedBlockMatrix_kernel_hilbert]
  simp

theorem exists_family_sl_block_degree_five_witness (k : ℕ) (hk : 0 < k) :
    ∃ M : Matrix (FamilySLColumns k) (FamilySLColumns k) K[X],
      DegreeBound M 1 ∧ slHilbert M (rectangularBlockPencil (familySLBlockLengths k)) 5 = k ^ 2 := by
  let e := familySLBlockLengths k
  let P : Matrix (FamilySLRows k) (FamilySLColumns k) K[X] := rectangularBlockPencil e
  let B := rectangularBlockKernelBasis (K := K) e
  obtain ⟨M, hM, hPMG⟩ := rectangularBlockPencil_affine_middle_lift e
    (familySLBlockLengths_adjacent k) (familySLRepeatedWitness (K := K) k)
    (familySLRepeatedWitness_column_degree k)
  obtain ⟨R, hR⟩ := rectangularBlockPencil_right_inverse (K := K) e
  have hVB : polynomialKernelBasisMatrix P B = blockMonomialKernel e :=
    polynomialKernelBasisMatrix_rectangularBlock e
  have hGM : P * M * polynomialKernelBasisMatrix P B = familySLRepeatedWitness k := by
    rw [hVB]
    exact hPMG
  have hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec := by
    rw [hGM]
    exact familySLRepeatedWitness_injective k
  have hV : ∀ x i, (polynomialKernelBasisMatrix P B x i).natDegree ≤ e i := by
    rw [hVB]
    exact blockMonomialKernel_column_degree e
  have hVL : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix P B x i).coeff (e i))) := by
    rw [hVB]
    exact blockMonomialKernel_leading_injective e
  have hP : DegreeBound P 1 := rectangularBlockPencil_degree e
  have hPL : Function.Injective (matrixCoeff P 1).transpose.mulVec :=
    rectangularBlockPencil_leading_transpose_injective e
  let i₀ : FamilySLColumns k := ⟨(⟨0, hk⟩, 0), 0⟩
  have hSL : slHilbert M P 5 =
      Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) 5) := by
    apply middle_slHilbert_of_scalar_obstruction M P B R hR hG e hM hP hV hVL hPL i₀ 5
    intro E c hE hrel
    apply familySLRepeatedWitness_scalar_obstruction k hk E c hE
    simpa only [hGM] using hrel
  have hd : ∀ i, e i + 1 ≤ 5 := by
    rintro ⟨i, j⟩
    fin_cases j <;> norm_num [e, familySLBlockLengths]
  refine ⟨M, hM, ?_⟩
  change slHilbert M P 5 = k ^ 2
  rw [hSL, middle_gl_kernel_hilbert_shifted M P B R hR hG e hM hP hV hVL hPL 5 hd]
  have hsum : (∑ i, Module.finrank K (polynomialKernelAtDegree
      (P * M * polynomialKernelBasisMatrix P B).transpose (5 - (e i + 1)))) =
      ∑ i, k * Module.finrank K (polynomialKernelAtDegree (familySLWitness (K := K)).transpose
        (5 - (e i + 1))) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hGM, familySLRepeatedWitness_kernel_hilbert]
  rw [hsum]
  simp [e, familySLBlockLengths, Fintype.sum_prod_type, Fin.sum_univ_succ,
    familySLWitness_affine_kernel_finrank, familySLWitness_quadratic_kernel_finrank, pow_two]

/-- An affine full SL pencil realizes the critical bounded dimension k²
on the ordinary finite matrix index types. -/
theorem exists_family_sl_degree_five_witness (k : ℕ) (hk : 0 < k) :
    ∃ (M : Matrix (Fin (11 * k)) (Fin (11 * k)) K[X])
      (P : Matrix (Fin (8 * k)) (Fin (11 * k)) K[X]),
      DegreeBound M 1 ∧ DegreeBound P 1 ∧ slHilbert M P 5 = k ^ 2 := by
  obtain ⟨M, hM, hH⟩ := exists_family_sl_block_degree_five_witness (K := K) k hk
  let en : Fin (11 * k) ≃ FamilySLColumns k :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, familySLColumns_card])
  let em : Fin (8 * k) ≃ FamilySLRows k :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, familySLRows_card])
  refine ⟨M.submatrix en en, (rectangularBlockPencil (familySLBlockLengths k)).submatrix em en,
    (fun i j => hM (en i) (en j)),
    (fun i j => rectangularBlockPencil_degree (familySLBlockLengths k) (em i) (en j)), ?_⟩
  rw [slHilbert_reindex]
  exact hH

end FD56

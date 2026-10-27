/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.NilpotentRankTwoJordan
import FD56.Stabilizer.GLKirillovPencil

/-! The number of rank-two primary blocks is fixed by the full ambient dimension. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators
variable {K : Type*} [Field K] {m ι : Type*} [Fintype m] [Fintype ι]
  [DecidableEq m] [DecidableEq ι]

theorem divisible_rank_two_basis_pole_count (q : ℕ) (hm : 2≤Fintype.card m)
    (T : Matrix (SLInput (Fin (q+1) × m) m) (Σ _ : ι, rankTwoJordanIndex (Fintype.card m-2)) K)
    (S : Matrix (Σ _ : ι, rankTwoJordanIndex (Fintype.card m-2)) (SLInput (Fin (q+1) × m) m) K)
    (hTS : T*S=1) (hST : S*T=1) :
    Fintype.card ι=Fintype.card m*(q+1)*(q+2)/2 := by
  let e : ((SLInput (Fin (q+1) × m) m) → K) ≃ₗ[K]
      ((Σ _ : ι, rankTwoJordanIndex (Fintype.card m-2)) → K) :=
    { Matrix.toLin' S with
      invFun := Matrix.toLin' T
      left_inv := by
        intro v
        change T *ᵥ (S *ᵥ v)=v
        rw [Matrix.mulVec_mulVec,hTS,Matrix.one_mulVec]
      right_inv := by
        intro v
        change S *ᵥ (T *ᵥ v)=v
        rw [Matrix.mulVec_mulVec,hST,Matrix.one_mulVec] }
  have hj : Fintype.card (rankTwoJordanIndex (Fintype.card m-2))=2*Fintype.card m := by
    simp only [rankTwoJordanIndex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega
  have hdim := e.finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_sigma,hj,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,SLInput,Fintype.card_sum,
    Fintype.card_prod,Fintype.card_fin] at hdim
  have he : (2*Fintype.card ι)*Fintype.card m=
      (Fintype.card m*(q+1)*(q+2))*Fintype.card m := by nlinarith [hdim]
  have hc : 2*Fintype.card ι=Fintype.card m*(q+1)*(q+2) :=
    Nat.eq_of_mul_eq_mul_right (by omega) he
  omega

end FD56

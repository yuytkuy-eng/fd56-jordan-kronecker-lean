/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.RankTwoRegularDecomposition

/-! Local Jordan decomposition for a star-shaped alternating coupling in
arbitrary coordinates, with any chosen nonzero off-diagonal pivot. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K m n : Type*} [Field K] [Fintype m] [DecidableEq m]

def twoPivotIndex (i j : m) (hij : i≠j) :
    (Fin 2 ⊕ {k : m // k≠i ∧ k≠j}) ≃ m where
  toFun
    | .inl k => if k=0 then i else j
    | .inr k => k.val
  invFun k := if hi : k=i then .inl 0 else
    if hj : k=j then .inl 1 else .inr ⟨k,hi,hj⟩
  left_inv x := by
    rcases x with k | ⟨k,hki,hkj⟩
    · fin_cases k <;> simp [hij,Ne.symm hij]
    · simp [hki,hkj]
  right_inv k := by
    by_cases hi : k=i
    · subst k; simp
    · by_cases hj : k=j
      · subst k; simp [hi]
      · simp [hi,hj]

def starCoupling (i : m) (w : m → K) : Matrix m m K :=
  fun u v => (if u=i then w v else 0) - if v=i then w u else 0

theorem twoPivot_complement_card (i j : m) (hij : i≠j) :
    Fintype.card {k : m // k≠i ∧ k≠j} = Fintype.card m - 2 := by
  have h := Fintype.card_congr (twoPivotIndex i j hij)
  simp only [Fintype.card_sum,Fintype.card_fin] at h
  omega

omit [Fintype m] in
theorem starCoupling_reindex (i j : m) (hij : i≠j) (w : m → K) :
    (starCoupling i w).submatrix (twoPivotIndex i j hij) (twoPivotIndex i j hij) =
      rankTwoForm (w j) (fun k : {k : m // k≠i ∧ k≠j} => w k.val) := by
  funext u v
  rcases u with u | ⟨u,hu,huj⟩ <;> rcases v with v | ⟨v,hv,hvj⟩
  · fin_cases u <;> fin_cases v <;>
      simp [starCoupling,twoPivotIndex,rankTwoForm,rankTwoCross,hij,Ne.symm hij]
  · fin_cases u <;>
      simp [starCoupling,twoPivotIndex,rankTwoForm,rankTwoCross,hv,hij,Ne.symm hij]
  · fin_cases v <;>
      simp [starCoupling,twoPivotIndex,rankTwoForm,rankTwoCross,hu,hij,Ne.symm hij]
  · simp [starCoupling,twoPivotIndex,rankTwoForm,hu,hv]

omit [Fintype m] in
theorem pairedCoupling_reindex [DecidableEq n] (e : n ≃ m) (A : Matrix m m K) (t : K[X]) :
    (pairedCoupling (A.map C) t).submatrix (Equiv.sumCongr e e) (Equiv.sumCongr e e) =
      pairedCoupling ((A.submatrix e e).map C) t := by
  funext i j
  cases i <;> cases j <;>
    simp [pairedCoupling,Matrix.submatrix_apply,Matrix.one_apply,e.injective.eq_iff]

theorem starCoupling_constant_decomposition (i j : m) (hij : i≠j)
    (w : m → K) (hw : w j≠0) (a : K) :
    ∃ T : Matrix (m ⊕ m)
      ((Fin 2 ⊕ Fin 2) ⊕ ((Fin 1 ⊕ Fin 1) × {k : m // k≠i ∧ k≠j})) K,
    ∃ S : Matrix ((Fin 2 ⊕ Fin 2) ⊕ ((Fin 1 ⊕ Fin 1) × {k : m // k≠i ∧ k≠j}))
      (m ⊕ m) K,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose * pairedCoupling ((starCoupling i w).map C) (X-C a) * T.map C =
        rankTwoRegularTarget (n := {k : m // k≠i ∧ k≠j}) a := by
  let n := {k : m // k≠i ∧ k≠j}
  let v : n → K := fun k => w k.val
  let e := Equiv.sumCongr (twoPivotIndex i j hij) (twoPivotIndex i j hij)
  obtain ⟨T₀,S₀,hTS,hST,hcong⟩ := rankTwoRegular_constant_decomposition a (w j) hw v
  have hreindex : (pairedCoupling ((starCoupling i w).map C) (X-C a)).submatrix e e =
      pairedCoupling ((rankTwoForm (w j) v).map C) (X-C a) := by
    rw [pairedCoupling_reindex,starCoupling_reindex]
  have hback : pairedCoupling ((starCoupling i w).map C) (X-C a) =
      (pairedCoupling ((rankTwoForm (w j) v).map C) (X-C a)).submatrix e.symm e.symm := by
    funext u v
    have h := congrFun (congrFun hreindex (e.symm u)) (e.symm v)
    simpa only [Matrix.submatrix_apply,Equiv.apply_symm_apply] using h
  refine ⟨T₀.submatrix e.symm id,S₀.submatrix id e.symm,?_,?_,?_⟩
  · change T₀.submatrix e.symm (Equiv.refl _) * S₀.submatrix (Equiv.refl _) e.symm = 1
    rw [Matrix.submatrix_mul_equiv,hTS]
    exact Matrix.submatrix_one_equiv e.symm
  · rw [Matrix.submatrix_mul_equiv,hST,Matrix.submatrix_id_id]
  · rw [hback]
    change (T₀.map C).transpose.submatrix id e.symm *
      (pairedCoupling ((rankTwoForm (w j) v).map C) (X-C a)).submatrix e.symm e.symm *
      (T₀.map C).submatrix e.symm id = _
    rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,Matrix.submatrix_id_id,hcong]

end FD56

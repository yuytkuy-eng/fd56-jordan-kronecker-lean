/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.SquareGLTraceCoordinates

/-! A specified local Jordan congruence preserves the trace pivot exactly. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem rankTwoJordanConstantChange_certificate (a c : K) (hc : c≠0) (w : n → K) :
    ∃ S : Matrix ((Fin 2 ⊕ Fin 2) ⊕ ((Fin 1 ⊕ Fin 1) × n))
      ((Fin 2 ⊕ n) ⊕ (Fin 2 ⊕ n)) K,
      rankTwoJordanConstantChange c w*S=1 ∧ S*rankTwoJordanConstantChange c w=1 ∧
      ((rankTwoJordanConstantChange c w).map C).transpose *
          pairedCoupling ((rankTwoForm c w).map C) (X-C a) * (rankTwoJordanConstantChange c w).map C =
        rankTwoRegularTarget (n := n) a := by
  let Q := rankTwoCoordinateChange c w
  let R := rankTwoCoordinateInverse c w
  obtain ⟨hQR,hRQ⟩ := rankTwoCoordinate_inverse c hc w
  let T₀ := pairedCoordinateChange Q R
  let S₀ := pairedCoordinateChange R Q
  have hTS : T₀*S₀=1 := pairedCoordinateChange_inverse Q R hQR
  have hST : S₀*T₀=1 := pairedCoordinateChange_inverse R Q hRQ
  have hRQ' : R.map C*Q.map C=(1 : Matrix (Fin 2 ⊕ n) (Fin 2 ⊕ n) K[X]) := by
    rw [← Matrix.map_mul,hRQ,Matrix.map_one _ (map_zero C) (map_one C)]
  have hcong : (T₀.map C).transpose * pairedCoupling ((rankTwoForm c w).map C) (X-C a) * T₀.map C =
      pairedCoupling
        ((Matrix.fromBlocks (![![0,1],![-1,0]] : Matrix (Fin 2) (Fin 2) K) 0 0 (0 : Matrix n n K)).map C)
        (X-C a) := by
    rw [pairedCoordinateChange_map,pairedCoordinateChange_congruence _ _ _ hRQ']
    have hA : (Q.map C).transpose*(rankTwoForm c w).map C*Q.map C =
        (Matrix.fromBlocks (![![0,1],![-1,0]] : Matrix (Fin 2) (Fin 2) K) 0 0 (0 : Matrix n n K)).map C := by
      change Q.transpose.map C*(rankTwoForm c w).map C*Q.map C = _
      rw [← Matrix.map_mul,← Matrix.map_mul,rankTwoCoordinate_congruence c hc w]
    rw [hA]
  let r := (Fin 1 ⊕ Fin 1) × n
  let T₁ : Matrix ((Fin 2 ⊕ Fin 2) ⊕ r) ((Fin 2 ⊕ Fin 2) ⊕ r) K :=
    Matrix.fromBlocks regularFourChange 0 0 1
  let S₁ : Matrix ((Fin 2 ⊕ Fin 2) ⊕ r) ((Fin 2 ⊕ Fin 2) ⊕ r) K :=
    Matrix.fromBlocks (regularFourChange (R := K)).transpose 0 0 1
  have hTS₁ : T₁*S₁=1 := by
    simp [T₁,S₁,Matrix.fromBlocks_multiply,regularFourChange_inverse.1,Matrix.fromBlocks_one]
  have hST₁ : S₁*T₁=1 := by
    simp [T₁,S₁,Matrix.fromBlocks_multiply,regularFourChange_inverse.2,Matrix.fromBlocks_one]
  let e := rankTwoRegularIndex n
  let P := T₀.submatrix id e
  let V := S₀.submatrix e id
  have hPV : P*V=1 := by
    dsimp [P,V]
    rw [Matrix.submatrix_mul_equiv,hTS,Matrix.submatrix_id_id]
  have hVP : V*P=1 := by
    change S₀.submatrix e (Equiv.refl _) * T₀.submatrix (Equiv.refl _) e = 1
    rw [Matrix.submatrix_mul_equiv,hST]
    exact Matrix.submatrix_one_equiv e
  have hpencil : (P.map C).transpose * pairedCoupling ((rankTwoForm c w).map C) (X-C a) * P.map C =
      Matrix.fromBlocks (rankTwoRegularCoupling (X-C a)) 0 0
        (Matrix.blockDiagonal (fun _ : n => skewJordanBlockPencil a 1)) := by
    have he : (P.map C).transpose * pairedCoupling ((rankTwoForm c w).map C) (X-C a) * P.map C =
        ((T₀.map C).transpose * pairedCoupling ((rankTwoForm c w).map C) (X-C a) * T₀.map C).submatrix e e := by
      change (T₀.map C).transpose.submatrix e (Equiv.refl _) *
        (pairedCoupling ((rankTwoForm c w).map C) (X-C a)).submatrix (Equiv.refl _) (Equiv.refl _) *
        (T₀.map C).submatrix (Equiv.refl _) e = _
      rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
    rw [he,hcong]
    exact rankTwoRegular_normalized_reindex a
  have hmapT : T₁.map C = Matrix.fromBlocks (regularFourChange (R := K[X])) 0 0 (1 : Matrix r r K[X]) := by
    simp only [T₁,Matrix.fromBlocks_map,regularFourChange_map,
      Matrix.map_zero _ (map_zero C),Matrix.map_one _ (map_zero C) (map_one C)]
  have hfour : (regularFourChange (R := K[X])).transpose * rankTwoRegularCoupling (X-C a) *
      regularFourChange = skewJordanBlockPencil a 2 := by
    rw [rankTwoRegularCoupling_congruence]
    have hJ : jordanUpperPencil a 2 = ![![X-C a,1],![0,X-C a]] := by
      funext i j
      fin_cases i <;> fin_cases j <;> simp [jordanUpperPencil]
    simp only [skewJordanBlockPencil,hJ]
  have hfinal : (T₁.map C).transpose *
      Matrix.fromBlocks (rankTwoRegularCoupling (X-C a)) 0 0
        (Matrix.blockDiagonal (fun _ : n => skewJordanBlockPencil a 1)) * T₁.map C =
        rankTwoRegularTarget (n := n) a := by
    rw [hmapT]
    simp only [Matrix.fromBlocks_transpose,Matrix.transpose_zero,Matrix.transpose_one,
      Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,
      Matrix.one_mul,Matrix.mul_one,hfour,rankTwoRegularTarget]
  refine ⟨S₁*V,?_,?_,?_⟩
  · change (P*T₁)*(S₁*V)=1
    rw [Matrix.mul_assoc,← Matrix.mul_assoc T₁,hTS₁,Matrix.one_mul,hPV]
  · change (S₁*V)*(P*T₁)=1
    rw [Matrix.mul_assoc,← Matrix.mul_assoc V,hVP,Matrix.one_mul,hST₁]
  · change ((P*T₁).map C).transpose * _ * (P*T₁).map C = _
    rw [Matrix.map_mul,Matrix.transpose_mul]
    calc
      _ = (T₁.map C).transpose *
          ((P.map C).transpose * pairedCoupling ((rankTwoForm c w).map C) (X-C a) * P.map C) *
          T₁.map C := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hpencil,hfinal]

def starJordanConstantChange (i j : n) (hij : i≠j) (w : n → K) :
    Matrix (n ⊕ n)
      ((Fin 2 ⊕ Fin 2) ⊕ ((Fin 1 ⊕ Fin 1) × {k : n // k≠i ∧ k≠j})) K :=
  (rankTwoJordanConstantChange (w j) (fun k : {k : n // k≠i ∧ k≠j} => w k.val)).submatrix
    (Equiv.sumCongr (twoPivotIndex i j hij) (twoPivotIndex i j hij)).symm id

theorem starJordanConstantChange_pivot (i j : n) (hij : i≠j) (w : n → K)
    (v : ((Fin 2 ⊕ Fin 2) ⊕ ((Fin 1 ⊕ Fin 1) × {k : n // k≠i ∧ k≠j})) → K) :
    (starJordanConstantChange i j hij w *ᵥ v) (.inl i) = v (.inl (.inl 0)) := by
  change (rankTwoJordanConstantChange (w j) (fun k : {k : n // k≠i ∧ k≠j} => w k.val) *ᵥ v)
    ((Equiv.sumCongr (twoPivotIndex i j hij) (twoPivotIndex i j hij)).symm (.inl i)) = _
  have he : (Equiv.sumCongr (twoPivotIndex i j hij) (twoPivotIndex i j hij)).symm (.inl i) =
      .inl (.inl 0) := by simp [twoPivotIndex]
  rw [he,rankTwoJordanConstantChange_pivot]

theorem starJordanConstantChange_certificate (i j : n) (hij : i≠j) (w : n → K)
    (hw : w j≠0) (a : K) :
    ∃ S : Matrix ((Fin 2 ⊕ Fin 2) ⊕ ((Fin 1 ⊕ Fin 1) × {k : n // k≠i ∧ k≠j})) (n ⊕ n) K,
      starJordanConstantChange i j hij w*S=1 ∧ S*starJordanConstantChange i j hij w=1 ∧
      ((starJordanConstantChange i j hij w).map C).transpose *
          pairedCoupling ((starCoupling i w).map C) (X-C a) * (starJordanConstantChange i j hij w).map C =
        rankTwoRegularTarget (n := {k : n // k≠i ∧ k≠j}) a := by
  let m := {k : n // k≠i ∧ k≠j}
  let v : m → K := fun k => w k.val
  let e := Equiv.sumCongr (twoPivotIndex i j hij) (twoPivotIndex i j hij)
  let T₀ := rankTwoJordanConstantChange (w j) v
  obtain ⟨S₀,hTS,hST,hcong⟩ := rankTwoJordanConstantChange_certificate a (w j) hw v
  have hreindex : (pairedCoupling ((starCoupling i w).map C) (X-C a)).submatrix e e =
      pairedCoupling ((rankTwoForm (w j) v).map C) (X-C a) := by
    rw [pairedCoupling_reindex,starCoupling_reindex]
  have hback : pairedCoupling ((starCoupling i w).map C) (X-C a) =
      (pairedCoupling ((rankTwoForm (w j) v).map C) (X-C a)).submatrix e.symm e.symm := by
    funext u v
    have h := congrFun (congrFun hreindex (e.symm u)) (e.symm v)
    simpa only [Matrix.submatrix_apply,Equiv.apply_symm_apply] using h
  refine ⟨S₀.submatrix id e.symm,?_,?_,?_⟩
  · change T₀.submatrix e.symm (Equiv.refl _) * S₀.submatrix (Equiv.refl _) e.symm = 1
    rw [Matrix.submatrix_mul_equiv,hTS]
    exact Matrix.submatrix_one_equiv e.symm
  · change S₀.submatrix id e.symm*T₀.submatrix e.symm id=1
    rw [Matrix.submatrix_mul_equiv,hST,Matrix.submatrix_id_id]
  · rw [hback]
    change (T₀.map C).transpose.submatrix id e.symm *
      (pairedCoupling ((rankTwoForm (w j) v).map C) (X-C a)).submatrix e.symm e.symm *
      (T₀.map C).submatrix e.symm id = _
    rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,Matrix.submatrix_id_id]
    exact hcong

end FD56

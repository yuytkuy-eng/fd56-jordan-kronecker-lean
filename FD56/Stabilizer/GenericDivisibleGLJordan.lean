/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.PolynomialRegularRankTwoJordan
import FD56.Stabilizer.GenericDivisibleGLPrimary

/-! Full constant Jordan congruences for generic divisible GL pencils over an algebraically closed extension. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K L : Type*} {m : Type} [Field K] [Field L] [IsAlgClosed L]
  [Fintype m] [DecidableEq m]

local instance : DecidableEq L := Classical.decEq L

theorem generic_divisible_gl_jordan_decomposition (q : ℕ) (hm : 2≤Fintype.card m)
    (φ : AffineCoefficientField K (MatrixParameters (Fin (q+1) × m) m) →+* L) :
    let H := (glKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m)).map (Polynomial.mapRingHom φ)
    let f := polynomialPencilOperator H
    ∃ T : Matrix (SLInput (Fin (q+1) × m) m)
      (Σ _ : f.Eigenvalues, rankTwoJordanIndex (Fintype.card m-2)) L,
    ∃ S : Matrix (Σ _ : f.Eigenvalues, rankTwoJordanIndex (Fintype.card m-2))
      (SLInput (Fin (q+1) × m) m) L,
      T*S=1 ∧ S*T=1 ∧ (T.map C).transpose*H*T.map C=
        Matrix.blockDiagonal' (fun a : f.Eigenvalues => rankTwoJordanPencil a.val (Fintype.card m-2)) := by
  classical
  let M := genericAffineSquare K (Fin (q+1) × m) m
  let P := genericAffineRows K (Fin (q+1) × m) m
  let H := glKirillovMatrix M P
  let H' := H.map (Polynomial.mapRingHom φ)
  have hH : DegreeBound H 1 := glKirillovMatrix_degreeBound M P 1
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
  have hH' : DegreeBound H' 1 := fun i j => Polynomial.natDegree_map_le.trans (hH i j)
  have hc (k : ℕ) : (fun i j => (H' i j).coeff k)=Matrix.map (fun i j => (H i j).coeff k) φ := by
    funext i j
    simp [H',Matrix.map_apply,Polynomial.coe_mapRingHom,Polynomial.coeff_map]
  have halt (k : ℕ) : ∀ v, v ⬝ᵥ ((fun i j => (H' i j).coeff k) *ᵥ v)=0 := by
    rw [hc]
    exact matrix_alternating_map φ _ (glKirillovMatrix_coefficient_alternating M P k)
  have hlead : Matrix.det (fun i j => (H' i j).coeff 1)≠0 := by
    rw [hc]
    have he := φ.map_det (fun i j => (H i j).coeff 1)
    intro hz
    apply generic_divisible_gl_leading_det_ne_zero K m (q+1)
    exact φ.injective ((he.trans hz).trans (map_zero φ).symm)
  apply polynomial_regular_rank_two_jordan_decomposition H' hH' (halt 0) (halt 1) hlead
    (Fintype.card m)
  intro a ha
  have heval : H'.det.eval a=H.det.eval₂ φ a := by
    rw [show H'.det=H.det.map φ from ((Polynomial.mapRingHom φ).map_det H).symm,
      Polynomial.eval_map]
  obtain ⟨hd,_,hr⟩ := generic_divisible_gl_primary_data q hm φ a (heval.symm.trans ha)
  exact ⟨hd,hr⟩

theorem generic_divisible_gl_jordan_pole_count (q : ℕ) (hm : 2≤Fintype.card m)
    (φ : AffineCoefficientField K (MatrixParameters (Fin (q+1) × m) m) →+* L) :
    let H := (glKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m)).map (Polynomial.mapRingHom φ)
    Fintype.card (polynomialPencilOperator H).Eigenvalues=
      ((q+1)*(q+2)*Fintype.card m)/2 := by
  classical
  let H := (glKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
    (genericAffineRows K (Fin (q+1) × m) m)).map (Polynomial.mapRingHom φ)
  let f := polynomialPencilOperator H
  obtain ⟨T,S,hTS,hST,_⟩ := generic_divisible_gl_jordan_decomposition q hm φ
  let e : ((SLInput (Fin (q+1) × m) m) → L) ≃ₗ[L]
      ((Σ _ : f.Eigenvalues, rankTwoJordanIndex (Fintype.card m-2)) → L) :=
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
  have he : (2*Fintype.card f.Eigenvalues)*Fintype.card m=
      ((q+1)*(q+2)*Fintype.card m)*Fintype.card m := by
    nlinarith [hdim]
  have hc : 2*Fintype.card f.Eigenvalues=(q+1)*(q+2)*Fintype.card m :=
    Nat.eq_of_mul_eq_mul_right (by omega) he
  change Fintype.card f.Eigenvalues=_
  omega

end FD56

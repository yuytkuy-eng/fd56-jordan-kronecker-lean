/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeGLBasis
import FD56.Hilbert.DepthTwoGLDegree

/-! Degree bounds for the third-depth polynomial GL basis. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m r s : Type*} [Field K]
  [Fintype n] [Fintype m] [Fintype r] [Fintype s]
  [DecidableEq n] [DecidableEq m] [DecidableEq r] [DecidableEq s]

omit [Fintype s] [DecidableEq m] [DecidableEq s] in
theorem depth_three_beta_coefficients_degree
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (T D₀ D₁ D₂ : Matrix s m K[X]) (b : s → ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hT : ∀ j x, (T j x).natDegree≤b j)
    (hrel : T*P*M^3=D₀*P+D₁*(P*M)+D₂*(P*M^2))
    (hO : Function.Injective (Matrix.mulVec (fun x i =>
      (observabilityMatrix M P 3 i x).coeff (i.1.val+1)))) :
    (∀ j x, (D₀ j x).natDegree≤b j+3) ∧
    (∀ j x, (D₁ j x).natDegree≤b j+2) ∧
    (∀ j x, (D₂ j x).natDegree≤b j+1) := by
  let D : Matrix s (Fin 3 × m) K[X] := fun j i => ![D₀,D₁,D₂] i.1 j i.2
  have he : D*observabilityMatrix M P 3=T*P*M^3 := by
    rw [hrel]
    funext j x
    simp [D,Matrix.mul_apply,observabilityMatrix,Fintype.sum_prod_type,Fin.sum_univ_succ,
      Finset.mul_sum,Finset.sum_mul,Finset.sum_add_distrib,Matrix.one_apply,add_assoc]
  have hPM3 : DegreeBound (P*M^3) 4 := by
    simpa using degreeBound_mul hP (degreeBound_pow M 1 hM 3)
  have hb : ∀ j x, ((D*observabilityMatrix M P 3) j x).natDegree≤b j+4 := by
    rw [he,Matrix.mul_assoc]
    exact matrix_mul_row_degree T (P*M^3) b 4 hT hPM3
  have hd := row_coordinates_degree_bound (observabilityMatrix M P 3) D
    (fun i => i.1.val+1) (fun j => b j+4)
    (fun i j => (observability_polynomial_degree_top M P 3 hM hP i j).1) hO hb
  refine ⟨?_,?_,?_⟩
  · intro j x
    rcases hd j (0,x) with hz | ⟨_,hh⟩
    · change D₀ j x=0 at hz; simp [hz]
    · change (D₀ j x).natDegree≤b j+4-1 at hh; omega
  · intro j x
    rcases hd j (1,x) with hz | ⟨_,hh⟩
    · change D₁ j x=0 at hz; simp [hz]
    · change (D₁ j x).natDegree≤b j+4-2 at hh; omega
  · intro j x
    rcases hd j (2,x) with hz | ⟨_,hh⟩
    · change D₂ j x=0 at hz; simp [hz]
    · change (D₂ j x).natDegree≤b j+4-3 at hh; omega

omit [Fintype r] [Fintype s] [DecidableEq m] [DecidableEq r] [DecidableEq s] in
theorem depthThreeGLColumns_degree
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (V : Matrix n r K[X]) (T D₀ D₁ D₂ : Matrix s m K[X]) (a : r → ℕ) (b : s → ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x k, (V x k).natDegree≤a k) (hT : ∀ j x, (T j x).natDegree≤b j)
    (hD₀ : ∀ j x, (D₀ j x).natDegree≤b j+3)
    (hD₁ : ∀ j x, (D₁ j x).natDegree≤b j+2)
    (hD₂ : ∀ j x, (D₂ j x).natDegree≤b j+1) :
    ∀ xy kj, (depthThreeGLColumns M P V T D₀ D₁ D₂ xy kj).natDegree≤a kj.1+b kj.2+3 := by
  have hPM : DegreeBound (P*M) 2 := degreeBound_mul hP hM
  have hPM2 : DegreeBound (P*M^2) 3 := by
    simpa using degreeBound_mul hP (degreeBound_pow M 1 hM 2)
  have hTP := matrix_mul_row_degree T P b 1 hT hP
  have hTPM : ∀ j x, ((T*P*M) j x).natDegree≤b j+2 := by
    rw [Matrix.mul_assoc]; exact matrix_mul_row_degree T (P*M) b 2 hT hPM
  have hTPM2 : ∀ j x, ((T*P*(M^2 : Matrix n n K[X])) j x).natDegree≤b j+3 := by
    rw [Matrix.mul_assoc]; exact matrix_mul_row_degree T (P*M^2) b 3 hT hPM2
  have hD2P : ∀ j x, ((D₂*P) j x).natDegree≤b j+2 := by
    simpa only [Nat.add_assoc] using matrix_mul_row_degree D₂ P (fun j => b j+1) 1 hD₂ hP
  have hD2PM : ∀ j x, ((D₂*(P*M)) j x).natDegree≤b j+3 := by
    simpa only [Nat.add_assoc] using matrix_mul_row_degree D₂ (P*M) (fun j => b j+1) 2 hD₂ hPM
  have hD1P : ∀ j x, ((D₁*P) j x).natDegree≤b j+3 := by
    simpa only [Nat.add_assoc] using matrix_mul_row_degree D₁ P (fun j => b j+2) 1 hD₁ hP
  have hH0 (j : s) (x : n) : ((T*P*(M^2 : Matrix n n K[X])-D₂*(P*M)-D₁*P) j x).natDegree≤b j+3 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le
      ((Polynomial.natDegree_sub_le _ _).trans (max_le (hTPM2 j x) (hD2PM j x))) (hD1P j x))
  have hH1 (j : s) (x : n) : ((T*P*M-D₂*P) j x).natDegree≤b j+2 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le (hTPM j x) (hD2P j x))
  have hMV := matrixCoeff_mul_column M V 1 a hM hV
  have hM2 : DegreeBound (M^2) 2 := by simpa using degreeBound_pow M 1 hM 2
  have hM3 : DegreeBound (M^3) 3 := by simpa using degreeBound_pow M 1 hM 3
  have hM2V := matrixCoeff_mul_column (M^2) V 2 a hM2 hV
  have hM3V := matrixCoeff_mul_column (M^3) V 3 a hM3 hV
  intro xy kj
  rcases xy with xy | xy
  · change (_+_+_ : K[X]).natDegree≤_
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · have hh := Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hV xy.1 kj.1) (hH0 kj.2 xy.2)); omega
      · have hh := Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hMV xy.1 kj.1).1 (hH1 kj.2 xy.2)); omega
    · have hh := Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hM2V xy.1 kj.1).1 (hTP kj.2 xy.2)); omega
  · change (_-_-_-_ : K[X]).natDegree≤_
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · apply (Polynomial.natDegree_sub_le _ _).trans
        apply max_le
        · have hh := Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hM3V xy.1 kj.1).1 (hT kj.2 xy.2)); omega
        · have hh := Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hM2V xy.1 kj.1).1 (hD₂ kj.2 xy.2)); omega
      · have hh := Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hMV xy.1 kj.1).1 (hD₁ kj.2 xy.2)); omega
    · have hh := Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hV xy.1 kj.1) (hD₀ kj.2 xy.2)); omega

end FD56

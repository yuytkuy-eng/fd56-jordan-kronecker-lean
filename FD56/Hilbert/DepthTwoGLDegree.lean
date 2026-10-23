/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthTwoGLBasis

/-! Degree bounds and independent leading coefficients for the second GL basis. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K m n r s : Type*} [Field K] [Fintype m] [Fintype n] [Fintype r] [Fintype s]
  [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq s]

omit [Fintype n] [Fintype s] [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq s] in
theorem depthTwo_coefficient_row_product (A : Matrix s m K[X]) (P : Matrix m n K[X])
    (b : s → ℕ) (d : ℕ) (hA : ∀ j x, (A j x).natDegree ≤ b j)
    (hP : DegreeBound P d) (j : s) (x : n) :
    ((A*P) j x).coeff (b j+d) =
      ((show Matrix s m K from fun j y => (A j y).coeff (b j)) * matrixCoeff P d) j x := by
  simp only [Matrix.mul_apply,Polynomial.finset_sum_coeff,matrixCoeff]
  apply Finset.sum_congr rfl
  intro y _
  exact Polynomial.coeff_mul_add_eq_of_natDegree_le (hA j y) (hP y x)

omit [Fintype s] [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq s] in
theorem depthTwo_beta_coefficients_degree (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (T D₀ D₁ : Matrix s m K[X]) (b : s → ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hT : ∀ j x, (T j x).natDegree ≤ b j)
    (hrel : T*P*M*M=D₀*P+D₁*(P*M))
    (hO : Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P (P*M) i x).coeff (depthTwoRowDegree i)))) :
    (∀ j x, (D₀ j x).natDegree ≤ b j+2) ∧
      (∀ j x, (D₁ j x).natDegree ≤ b j+1) := by
  let D := Matrix.fromCols D₀ D₁
  have he : D*depthTwoStack P (P*M)=T*P*M*M := by
    change Matrix.fromCols D₀ D₁ * Matrix.fromRows P (P*M) = _
    rw [Matrix.fromCols_mul_fromRows,hrel]
  have hb : ∀ j x, ((D*depthTwoStack P (P*M)) j x).natDegree ≤ b j+3 := by
    rw [he]
    exact matrix_mul_row_degree (T*P*M) M (fun j => b j+2) 1
      (matrix_mul_row_degree (T*P) M (fun j => b j+1) 1
        (matrix_mul_row_degree T P b 1 hT hP) hM) hM
  have hd := row_coordinates_degree_bound (depthTwoStack P (P*M)) D depthTwoRowDegree
    (fun j => b j+3) (depthTwo_stack_degree _ _ hP (degreeBound_mul hP hM)) hO hb
  constructor
  · intro j x
    rcases hd j (Sum.inl x) with hz | ⟨_,hh⟩
    · change D₀ j x=0 at hz; simp [hz]
    · change (D₀ j x).natDegree ≤ b j+3-1 at hh; omega
  · intro j x
    rcases hd j (Sum.inr x) with hz | ⟨_,hh⟩
    · change D₁ j x=0 at hz; simp [hz]
    · change (D₁ j x).natDegree ≤ b j+3-2 at hh; omega

omit [Fintype r] [Fintype s] [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq s] in
theorem depthTwoGLColumns_degree (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (V : Matrix n r K[X]) (T D₀ D₁ : Matrix s m K[X]) (a : r → ℕ) (b : s → ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x k, (V x k).natDegree ≤ a k) (hT : ∀ j x, (T j x).natDegree ≤ b j)
    (hD₀ : ∀ j x, (D₀ j x).natDegree ≤ b j+2)
    (hD₁ : ∀ j x, (D₁ j x).natDegree ≤ b j+1) :
    ∀ xy kj, (depthTwoGLColumns M P V T D₀ D₁ xy kj).natDegree ≤ a kj.1+b kj.2+2 := by
  have hTP := matrix_mul_row_degree T P b 1 hT hP
  have hTPM := matrix_mul_row_degree (T*P) M (fun j => b j+1) 1 hTP hM
  have hDP := matrix_mul_row_degree D₁ P (fun j => b j+1) 1 hD₁ hP
  have hMV := matrixCoeff_mul_column M V 1 a hM hV
  have hM2V := matrixCoeff_mul_column (M*M) V 2 a (degreeBound_mul hM hM) hV
  intro xy kj
  rcases xy with xy | xy
  · change (V xy.1 kj.1 * (T*P*M-D₁*P) kj.2 xy.2 +
      (M*V) xy.1 kj.1 * (T*P) kj.2 xy.2).natDegree ≤ _
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · have hh := Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hV xy.1 kj.1)
        ((Polynomial.natDegree_sub_le _ _).trans (max_le (hTPM kj.2 xy.2) (hDP kj.2 xy.2))))
      simpa only [Matrix.sub_apply,Nat.add_assoc,Nat.reduceAdd] using hh
    · have hh := Polynomial.natDegree_mul_le.trans
        (Nat.add_le_add (hMV xy.1 kj.1).1 (hTP kj.2 xy.2))
      omega
  · change ((M*M*V) xy.1 kj.1 * T kj.2 xy.2 -
      (M*V) xy.1 kj.1 * D₁ kj.2 xy.2 - V xy.1 kj.1 * D₀ kj.2 xy.2).natDegree ≤ _
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · have hh := Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hM2V xy.1 kj.1).1 (hT kj.2 xy.2)); omega
      · have hh := Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hMV xy.1 kj.1).1 (hD₁ kj.2 xy.2)); omega
    · have hh := Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hV xy.1 kj.1) (hD₀ kj.2 xy.2)); omega

omit [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq s] in
theorem depthTwo_leading_parameter_injective (M : Matrix n n K) (P Q : Matrix m n K)
    (V : Matrix n r K) (T D : Matrix s m K)
    (hV : Function.Injective V.mulVec) (hT : Function.Injective T.transpose.mulVec)
    (hO : Function.Injective (Matrix.fromRows P Q).transpose.mulVec) :
    Function.Injective (fun C : Matrix r s K => V*C*(T*Q-D*P)+M*V*C*T*P) := by
  intro C C' h
  let L := Matrix.fromCols (M*V*C*T-V*C*D) (V*C*T)
  let L' := Matrix.fromCols (M*V*C'*T-V*C'*D) (V*C'*T)
  have he (C : Matrix r s K) :
      Matrix.fromCols (M*V*C*T-V*C*D) (V*C*T) * Matrix.fromRows P Q =
        V*C*(T*Q-D*P)+M*V*C*T*P := by
    rw [Matrix.fromCols_mul_fromRows]
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    abel
  have hL : L*Matrix.fromRows P Q=L'*Matrix.fromRows P Q := by
    simpa only [L,L',he] using h
  have ht := congrArg Matrix.transpose hL
  simp only [Matrix.transpose_mul] at ht
  have hLL := matrix_left_mul_injective_of_mulVec _ hO ht
  have hE : V*C*T=V*C'*T := by
    funext i j
    exact congrFun (congrFun hLL (Sum.inr j)) i
  have hc := matrix_left_mul_injective_of_mulVec V hV
    (by simpa only [Matrix.mul_assoc] using hE)
  have hct := congrArg Matrix.transpose hc
  simp only [Matrix.transpose_mul] at hct
  have hCC := matrix_left_mul_injective_of_mulVec _ hT hct
  exact Matrix.transpose_injective hCC

omit [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq s] in
theorem depthTwoGLColumns_leading_injective (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (V : Matrix n r K[X]) (T D₀ D₁ : Matrix s m K[X]) (a : r → ℕ) (b : s → ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x k, (V x k).natDegree ≤ a k) (hT : ∀ j x, (T j x).natDegree ≤ b j)
    (hD₁ : ∀ j x, (D₁ j x).natDegree ≤ b j+1)
    (hVL : Function.Injective (Matrix.mulVec (fun x k => (V x k).coeff (a k))))
    (hTL : Function.Injective (Matrix.mulVec (fun x j => (T j x).coeff (b j))))
    (hO : Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P (P*M) i x).coeff (depthTwoRowDegree i)))) :
    Function.Injective (Matrix.mulVec (fun xy kj =>
      (depthTwoGLColumns M P V T D₀ D₁ xy kj).coeff (a kj.1+b kj.2+2))) := by
  let V₀ : Matrix n r K := fun x k => (V x k).coeff (a k)
  let T₀ : Matrix s m K := fun j x => (T j x).coeff (b j)
  let D₁₀ : Matrix s m K := fun j x => (D₁ j x).coeff (b j+1)
  let P₀ := matrixCoeff P 1
  let Q₀ := matrixCoeff (P*M) 2
  let M₀ := matrixCoeff M 1
  let H₀ := T₀*Q₀-D₁₀*P₀
  let H₁ := T₀*P₀
  have hTP := matrix_mul_row_degree T P b 1 hT hP
  have hPM : DegreeBound (P*M) 2 := degreeBound_mul hP hM
  have hTPM : ∀ j x, ((T*P*M) j x).natDegree ≤ b j+2 := by
    rw [Matrix.mul_assoc]
    exact matrix_mul_row_degree T (P*M) b 2 hT hPM
  have hDP : ∀ j x, ((D₁*P) j x).natDegree ≤ b j+2 := by
    simpa only [Nat.add_assoc,Nat.reduceAdd] using
      matrix_mul_row_degree D₁ P (fun j => b j+1) 1 hD₁ hP
  have hH : ∀ j x, ((T*P*M-D₁*P) j x).natDegree ≤ b j+2 := by
    intro j x
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le (hTPM j x) (hDP j x))
  have hH₀ (j : s) (x : n) : ((T*P*M-D₁*P) j x).coeff (b j+2)=H₀ j x := by
    change (((T*P*M) j x)-(D₁*P) j x).coeff (b j+2)=_
    rw [Polynomial.coeff_sub,Matrix.mul_assoc,
      depthTwo_coefficient_row_product T (P*M) b 2 hT hPM j x]
    have hd := depthTwo_coefficient_row_product D₁ P (fun j => b j+1) 1 hD₁ hP j x
    simpa only [H₀,T₀,D₁₀,P₀,Q₀,Matrix.sub_apply,Nat.add_assoc,Nat.reduceAdd] using
      congrArg (fun y : K => (T₀*Q₀) j x-y) hd
  have hH₁ (j : s) (x : n) : ((T*P) j x).coeff (b j+1)=H₁ j x :=
    depthTwo_coefficient_row_product T P b 1 hT hP j x
  have hMV := matrixCoeff_mul_column M V 1 a hM hV
  have hc (xy : n × n) (kj : r × s) :
      (depthTwoGLColumns M P V T D₀ D₁ (Sum.inl xy) kj).coeff (a kj.1+b kj.2+2) =
        V₀ xy.1 kj.1 * H₀ kj.2 xy.2 + (M₀*V₀) xy.1 kj.1 * H₁ kj.2 xy.2 := by
    change (V xy.1 kj.1*(T*P*M-D₁*P) kj.2 xy.2 +
      (M*V) xy.1 kj.1*(T*P) kj.2 xy.2).coeff (a kj.1+b kj.2+2)=_
    rw [Polynomial.coeff_add]
    have h₀ : (V xy.1 kj.1*(T*P*M-D₁*P) kj.2 xy.2).coeff (a kj.1+b kj.2+2)=
        V₀ xy.1 kj.1*H₀ kj.2 xy.2 := by
      rw [show a kj.1+b kj.2+2=a kj.1+(b kj.2+2) by omega,
        Polynomial.coeff_mul_add_eq_of_natDegree_le (hV _ _) (hH _ _),hH₀]
    have h₁ : ((M*V) xy.1 kj.1*(T*P) kj.2 xy.2).coeff (a kj.1+b kj.2+2)=
        (M₀*V₀) xy.1 kj.1*H₁ kj.2 xy.2 := by
      rw [show a kj.1+b kj.2+2=(1+a kj.1)+(b kj.2+1) by omega,
        Polynomial.coeff_mul_add_eq_of_natDegree_le (hMV _ _).1 (hTP _ _),
        (hMV _ _).2,hH₁]
    rw [h₀,h₁]
  let A : Matrix (n × n) (r × s) K := fun xy kj =>
    V₀ xy.1 kj.1*H₀ kj.2 xy.2+(M₀*V₀) xy.1 kj.1*H₁ kj.2 xy.2
  have hA (c : r × s → K) : A*ᵥ c = (fun xy =>
      (V₀*(show Matrix r s K from fun i j => c (i,j))*H₀+
        M₀*V₀*(show Matrix r s K from fun i j => c (i,j))*T₀*P₀) xy.1 xy.2) := by
    funext xy
    change (∑ kj, (V₀ xy.1 kj.1*H₀ kj.2 xy.2+
      (M₀*V₀) xy.1 kj.1*H₁ kj.2 xy.2)*c kj)=_
    simp only [add_mul,Finset.sum_add_distrib,Matrix.add_apply]
    exact congrArg₂ (fun x y : K => x+y)
      (congrFun (tensorColumns_mulVec V₀ H₀ c) xy)
      (by simpa only [H₁,Matrix.mul_assoc] using
        congrFun (tensorColumns_mulVec (M₀*V₀) H₁ c) xy)
  have hi : Function.Injective A.mulVec := by
    intro c d h
    have hO' : Function.Injective (Matrix.fromRows P₀ Q₀).transpose.mulVec := by
      have he : (Matrix.fromRows P₀ Q₀).transpose = (fun x i =>
          (depthTwoStack P (P*M) i x).coeff (depthTwoRowDegree i)) := by
        funext x i; cases i <;> rfl
      rw [he]
      exact hO
    have hm := congrArg (fun f : n × n → K => fun i j => f (i,j)) h
    rw [hA,hA] at hm
    have hC := depthTwo_leading_parameter_injective M₀ P₀ Q₀ V₀ T₀ D₁₀ hVL hTL
      hO' hm
    funext k
    exact congrFun (congrFun hC k.1) k.2
  intro c d h
  apply hi
  funext xy
  have hh := congrFun h (Sum.inl xy)
  simpa only [Matrix.mulVec,dotProduct,hc,A] using hh

end FD56

/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeGLDegree

/-! Independent highest coefficients of the third-depth GL columns. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m r s : Type*} [Field K]
  [Fintype n] [Fintype m] [Fintype r] [Fintype s]
  [DecidableEq n] [DecidableEq m] [DecidableEq r] [DecidableEq s]

def depthThreeRows (P Q S : Matrix m n K) : Matrix (Fin 3 × m) n K :=
  fun i x => ![P,Q,S] i.1 i.2 x

def depthThreeCols (A B C : Matrix n m K) : Matrix n (Fin 3 × m) K :=
  fun x i => ![A,B,C] i.1 x i.2

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
theorem depth_three_blocks_mul (A B C : Matrix n m K) (P Q S : Matrix m n K) :
    depthThreeCols A B C*depthThreeRows P Q S=A*P+B*Q+C*S := by
  funext x y
  simp [depthThreeCols,depthThreeRows,Matrix.mul_apply,Fintype.sum_prod_type,
    Fin.sum_univ_succ,add_assoc]

omit [DecidableEq r] [DecidableEq s] in
theorem depth_three_leading_parameter_injective
    (M : Matrix n n K) (P Q S : Matrix m n K)
    (V : Matrix n r K) (T D₁ D₂ : Matrix s m K)
    (hV : Function.Injective V.mulVec) (hT : Function.Injective T.transpose.mulVec)
    (hO : Function.Injective (depthThreeRows P Q S).transpose.mulVec) :
    Function.Injective (fun C : Matrix r s K =>
      V*C*(T*S-D₂*Q-D₁*P)+M*V*C*(T*Q-D₂*P)+M^2*V*C*T*P) := by
  intro C C' h
  dsimp only at h
  let L (C : Matrix r s K) := depthThreeCols
    (M^2*V*C*T-M*V*C*D₂-V*C*D₁) (M*V*C*T-V*C*D₂) (V*C*T)
  have he (C : Matrix r s K) : L C*depthThreeRows P Q S=
      V*C*(T*S-D₂*Q-D₁*P)+M*V*C*(T*Q-D₂*P)+M^2*V*C*T*P := by
    dsimp only [L]
    rw [depth_three_blocks_mul]
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    abel
  have hh : L C*depthThreeRows P Q S=L C'*depthThreeRows P Q S := by rw [he,he,h]
  have ht := congrArg Matrix.transpose hh
  simp only [Matrix.transpose_mul] at ht
  have hL := matrix_left_mul_injective_of_mulVec _ hO ht
  have hE : V*C*T=V*C'*T := by
    funext x j
    exact congrFun (congrFun hL (2,j)) x
  have hc := matrix_left_mul_injective_of_mulVec V hV
    (by simpa only [Matrix.mul_assoc] using hE)
  have hct := congrArg Matrix.transpose hc
  simp only [Matrix.transpose_mul] at hct
  exact Matrix.transpose_injective (matrix_left_mul_injective_of_mulVec _ hT hct)

theorem depthThreeGLColumns_leading_injective
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (V : Matrix n r K[X]) (T D₀ D₁ D₂ : Matrix s m K[X]) (a : r → ℕ) (b : s → ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x k, (V x k).natDegree≤a k) (hT : ∀ j x, (T j x).natDegree≤b j)
    (hD₁ : ∀ j x, (D₁ j x).natDegree≤b j+2)
    (hD₂ : ∀ j x, (D₂ j x).natDegree≤b j+1)
    (hVL : Function.Injective (Matrix.mulVec (fun x k => (V x k).coeff (a k))))
    (hTL : Function.Injective (Matrix.mulVec (fun x j => (T j x).coeff (b j))))
    (hO : Function.Injective (Matrix.mulVec (fun x i =>
      (observabilityMatrix M P 3 i x).coeff (i.1.val+1)))) :
    Function.Injective (Matrix.mulVec (fun xy kj =>
      (depthThreeGLColumns M P V T D₀ D₁ D₂ xy kj).coeff (a kj.1+b kj.2+3))) := by
  let V₀ : Matrix n r K := fun x k => (V x k).coeff (a k)
  let T₀ : Matrix s m K := fun j x => (T j x).coeff (b j)
  let E₁ : Matrix s m K := fun j x => (D₁ j x).coeff (b j+2)
  let E₂ : Matrix s m K := fun j x => (D₂ j x).coeff (b j+1)
  let P₀ := matrixCoeff P 1
  let Q₀ := matrixCoeff (P*M) 2
  let S₀ := matrixCoeff (P*M^2) 3
  let M₀ := matrixCoeff M 1
  let H₀ := T₀*S₀-E₂*Q₀-E₁*P₀
  let H₁ := T₀*Q₀-E₂*P₀
  let H₂ := T₀*P₀
  have hPM : DegreeBound (P*M) 2 := degreeBound_mul hP hM
  have hM2 : DegreeBound (M^2) 2 := by simpa using degreeBound_pow M 1 hM 2
  have hPM2 : DegreeBound (P*M^2) 3 := degreeBound_mul hP hM2
  have hTP := matrix_mul_row_degree T P b 1 hT hP
  have hTPM := matrix_mul_row_degree T (P*M) b 2 hT hPM
  have hTPM2 := matrix_mul_row_degree T (P*M^2) b 3 hT hPM2
  have hD2P := matrix_mul_row_degree D₂ P (fun j => b j+1) 1 hD₂ hP
  have hD2PM := matrix_mul_row_degree D₂ (P*M) (fun j => b j+1) 2 hD₂ hPM
  have hD1P := matrix_mul_row_degree D₁ P (fun j => b j+2) 1 hD₁ hP
  have hH0 (j : s) (x : n) : ((T*P*(M^2 : Matrix n n K[X])-D₂*(P*M)-D₁*P) j x).natDegree≤b j+3 := by
    simp only [Matrix.mul_assoc] at hTPM2 ⊢
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le
      ((Polynomial.natDegree_sub_le _ _).trans (max_le (hTPM2 j x) (by simpa only [Nat.add_assoc] using hD2PM j x)))
      (by simpa only [Nat.add_assoc] using hD1P j x))
  have hH1 (j : s) (x : n) : ((T*P*M-D₂*P) j x).natDegree≤b j+2 := by
    rw [Matrix.mul_assoc]
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le (hTPM j x)
      (by simpa only [Nat.add_assoc] using hD2P j x))
  have hc0 (j : s) (x : n) :
      ((T*P*(M^2 : Matrix n n K[X])-D₂*(P*M)-D₁*P) j x).coeff (b j+3)=H₀ j x := by
    have h0 := depthTwo_coefficient_row_product T (P*M^2) b 3 hT hPM2 j x
    have h1 := depthTwo_coefficient_row_product D₂ (P*M) (fun j => b j+1) 2 hD₂ hPM j x
    have h2 := depthTwo_coefficient_row_product D₁ P (fun j => b j+2) 1 hD₁ hP j x
    simpa only [H₀,T₀,E₁,E₂,P₀,Q₀,S₀,Matrix.sub_apply,Polynomial.coeff_sub,
      Matrix.mul_assoc,Nat.add_assoc] using
      congrArg₂ (fun u v : K => u-v) (congrArg₂ (fun u v : K => u-v) h0 h1) h2
  have hc1 (j : s) (x : n) : ((T*P*M-D₂*P) j x).coeff (b j+2)=H₁ j x := by
    have h0 := depthTwo_coefficient_row_product T (P*M) b 2 hT hPM j x
    have h1 := depthTwo_coefficient_row_product D₂ P (fun j => b j+1) 1 hD₂ hP j x
    simpa only [H₁,T₀,E₂,P₀,Q₀,Matrix.sub_apply,Polynomial.coeff_sub,
      Matrix.mul_assoc,Nat.add_assoc] using congrArg₂ (fun u v : K => u-v) h0 h1
  have hc2 (j : s) (x : n) : ((T*P) j x).coeff (b j+1)=H₂ j x :=
    depthTwo_coefficient_row_product T P b 1 hT hP j x
  have hMV := matrixCoeff_mul_column M V 1 a hM hV
  have hM2V := matrixCoeff_mul_column (M^2) V 2 a hM2 hV
  have hpow : matrixCoeff (M^2) 2=M₀^2 := by simpa only [M₀,one_mul] using matrixCoeff_pow M 1 hM 2
  have hc (xy : n × n) (kj : r × s) :
      (depthThreeGLColumns M P V T D₀ D₁ D₂ (Sum.inl xy) kj).coeff (a kj.1+b kj.2+3)=
        V₀ xy.1 kj.1*H₀ kj.2 xy.2+(M₀*V₀) xy.1 kj.1*H₁ kj.2 xy.2+
          ((M₀^2 : Matrix n n K)*V₀) xy.1 kj.1*H₂ kj.2 xy.2 := by
    change (_+_+_ : K[X]).coeff _=_
    simp only [Polynomial.coeff_add]
    have h0 : (V xy.1 kj.1*(T*P*(M^2 : Matrix n n K[X])-D₂*(P*M)-D₁*P) kj.2 xy.2).coeff
        (a kj.1+b kj.2+3)=V₀ xy.1 kj.1*H₀ kj.2 xy.2 := by
      rw [show a kj.1+b kj.2+3=a kj.1+(b kj.2+3) by omega,
        Polynomial.coeff_mul_add_eq_of_natDegree_le (hV _ _) (hH0 _ _),hc0]
    have h1 : ((M*V) xy.1 kj.1*(T*P*M-D₂*P) kj.2 xy.2).coeff
        (a kj.1+b kj.2+3)=(M₀*V₀) xy.1 kj.1*H₁ kj.2 xy.2 := by
      rw [show a kj.1+b kj.2+3=(1+a kj.1)+(b kj.2+2) by omega,
        Polynomial.coeff_mul_add_eq_of_natDegree_le (hMV _ _).1 (hH1 _ _),(hMV _ _).2,hc1]
    have h2 : (((M^2 : Matrix n n K[X])*V) xy.1 kj.1*(T*P) kj.2 xy.2).coeff
        (a kj.1+b kj.2+3)=((M₀^2 : Matrix n n K)*V₀) xy.1 kj.1*H₂ kj.2 xy.2 := by
      rw [show a kj.1+b kj.2+3=(2+a kj.1)+(b kj.2+1) by omega,
        Polynomial.coeff_mul_add_eq_of_natDegree_le (hM2V _ _).1 (hTP _ _),(hM2V _ _).2,hpow,hc2]
    rw [h0,h1,h2]
  let A : Matrix (n × n) (r × s) K := fun xy kj =>
    V₀ xy.1 kj.1*H₀ kj.2 xy.2+(M₀*V₀) xy.1 kj.1*H₁ kj.2 xy.2+
      ((M₀^2 : Matrix n n K)*V₀) xy.1 kj.1*H₂ kj.2 xy.2
  have hA (c : r × s → K) : A*ᵥ c=fun xy =>
      (V₀*(Matrix.of fun i j => c (i,j))*H₀+M₀*V₀*(Matrix.of fun i j => c (i,j))*H₁+
        (M₀^2 : Matrix n n K)*V₀*(Matrix.of fun i j => c (i,j))*H₂) xy.1 xy.2 := by
    funext xy
    change (∑ kj, (_+_+_)*c kj)=_
    simp only [add_mul,Finset.sum_add_distrib,Matrix.add_apply]
    exact congrArg₂ (fun u v : K => u+v)
      (congrArg₂ (fun u v : K => u+v)
        (congrFun (tensorColumns_mulVec V₀ H₀ c) xy)
        (congrFun (tensorColumns_mulVec (M₀*V₀) H₁ c) xy))
      (congrFun (tensorColumns_mulVec ((M₀^2 : Matrix n n K)*V₀) H₂ c) xy)
  have hO' : Function.Injective (depthThreeRows P₀ Q₀ S₀).transpose.mulVec := by
    have he : (depthThreeRows P₀ Q₀ S₀).transpose=(fun x i =>
        (observabilityMatrix M P 3 i x).coeff (i.1.val+1)) := by
      funext x i
      rcases i with ⟨i,j⟩
      fin_cases i <;> simp [depthThreeRows,P₀,Q₀,S₀,matrixCoeff,observabilityMatrix]
    rw [he]; exact hO
  have hi : Function.Injective A.mulVec := by
    intro c d h
    have he : (Matrix.of fun i j => c (i,j))=(Matrix.of fun i j => d (i,j)) := by
      apply depth_three_leading_parameter_injective M₀ P₀ Q₀ S₀ V₀ T₀ E₁ E₂ hVL hTL hO'
      funext x y
      have hh := congrFun h (x,y)
      simpa only [hA,H₀,H₁,H₂,Matrix.mul_assoc] using hh
    funext kj
    exact congrFun (congrFun he kj.1) kj.2
  intro c d h
  apply hi
  funext xy
  have hh := congrFun h (Sum.inl xy)
  simpa only [Matrix.mulVec,dotProduct,hc,A] using hh

end FD56

/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityGLReduction
import FD56.Hilbert.ObservabilityGLRecurrence

/-! The highest row coefficient of a third-depth GL stabilizer. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m r : Type*} [Field K] [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

omit [DecidableEq m] in
theorem depth_three_observability_row_expansion
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (A : Matrix n (Fin 3 × m) K[X]) :
    A*observabilityMatrix M P 3=
      (Matrix.of fun i j => A i (0,j))*P+
      (Matrix.of fun i j => A i (1,j))*(P*M)+
      (Matrix.of fun i j => A i (2,j))*(P*M^2) := by
  funext i j
  simp [Matrix.mul_apply,observabilityMatrix,Fintype.sum_prod_type,Fin.sum_univ_succ,
    Finset.mul_sum,Finset.sum_mul,Finset.sum_add_distrib,add_assoc,Matrix.one_apply]

omit [Fintype m] in
theorem depth_three_observability_right_inverse_block
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (R : Matrix n (Fin 3 × m) K[X]) (hR : observabilityMatrix M P 3*R=1)
    (i j : Fin 3) :
    (P*M^i.val)*(Matrix.of fun a b => R a (j,b))=if i=j then 1 else 0 := by
  funext a b
  have he := congrFun (congrFun hR (i,a)) (j,b)
  change ((P*M^i.val)*(Matrix.of fun a b => R a (j,b))) a b = _ at he
  by_cases h : i=j <;> simpa [h,Matrix.one_apply,Prod.ext_iff] using he

theorem depth_three_gl_terminal_factor
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P 3))))
    (R : Matrix n (Fin 3 × m) K[X]) (hR : observabilityMatrix M P 3*R=1)
    (hO : Function.Injective (observabilityMatrix M P 4).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (hPX : P*X=0) (hcomm : M*X-X*M=U*P) :
    ∃ E : Matrix r m K[X],
      X*(Matrix.of fun a b => R a (2,b))=polynomialKernelBasisMatrix _ B*E := by
  let Rb (j : Fin 3) : Matrix n m K[X] := Matrix.of fun a b => R a (j,b)
  let A (j : Fin 3) : Matrix n m K[X] := X*Rb j
  let D (j : Fin 3) : Matrix m m K[X] := P*M^3*Rb j
  have hb (i j : Fin 3) : (P*M^i.val)*Rb j=if i=j then 1 else 0 :=
    depth_three_observability_right_inverse_block M P R hR i j
  have hX : X=A 0*P+A 1*(P*M)+A 2*(P*M^2) := by
    have he := gl_observability_row_factor M P 3 B R hR hO X U hPX hcomm
    rw [depth_three_observability_row_expansion] at he
    exact he
  have hPA (j : Fin 3) : P*A j=0 := by
    dsimp [A]
    rw [← Matrix.mul_assoc,hPX,Matrix.zero_mul]
  have hshift (j : Fin 3) : X*M*Rb j=
      A 0*((P*M)*Rb j)+A 1*((P*M^2)*Rb j)+A 2*D j := by
    conv_lhs => rw [hX]
    simp only [D,pow_succ,pow_zero,Matrix.mul_one,Matrix.one_mul,Matrix.add_mul,Matrix.mul_assoc]
  have h1 : M*A 1=A 0+A 2*D 1 := by
    have he := congrArg (fun Y : Matrix n n K[X] => Y*Rb 1) hcomm
    have hb0 := hb 0 1
    have hb1 := hb 1 1
    have hb2 := hb 2 1
    simp only [Fin.val_zero,pow_zero,Matrix.mul_one] at hb0
    simp only [Fin.val_one,pow_one] at hb1
    simp [Fin.ext_iff] at hb0 hb1 hb2
    dsimp only at he
    rw [Matrix.sub_mul,hshift,Matrix.mul_assoc U P,hb0,Matrix.mul_zero,
      hb1,hb2,Matrix.mul_one,Matrix.mul_zero,add_zero] at he
    exact sub_eq_zero.mp (by simpa only [A,Matrix.mul_assoc] using he)
  have h2 : M*A 2=A 1+A 2*D 2 := by
    have he := congrArg (fun Y : Matrix n n K[X] => Y*Rb 2) hcomm
    have hb0 := hb 0 2
    have hb1 := hb 1 2
    have hb2 := hb 2 2
    simp only [Fin.val_zero,pow_zero,Matrix.mul_one] at hb0
    simp only [Fin.val_one,pow_one] at hb1
    simp [Fin.ext_iff] at hb0 hb1 hb2
    dsimp only at he
    rw [Matrix.sub_mul,hshift,Matrix.mul_assoc U P,hb0,Matrix.mul_zero,
      hb1,hb2,Matrix.mul_one,Matrix.mul_zero,zero_add] at he
    exact sub_eq_zero.mp (by simpa only [A,Matrix.mul_assoc] using he)
  have hPM1 : P*M*A 1=0 := by
    rw [Matrix.mul_assoc,h1,Matrix.mul_add,← Matrix.mul_assoc P (A 2),hPA,hPA,Matrix.zero_mul,add_zero]
  have hPM2 : P*M*A 2=0 := by
    rw [Matrix.mul_assoc,h2,Matrix.mul_add,← Matrix.mul_assoc P (A 2),hPA,hPA,Matrix.zero_mul,add_zero]
  have hPMM2 : P*M^2*A 2=0 := by
    calc
      P*M^2*A 2=(P*M)*(M*A 2) := by rw [pow_two]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h2,Matrix.mul_add,← Matrix.mul_assoc (P*M) (A 2),hPM1,hPM2,Matrix.zero_mul,add_zero]
  apply matrix_factor_through_kernel_basis _ B (A 2)
  funext i j
  rcases i with ⟨i,k⟩
  change ((P*M^i.val)*A 2) k j=0
  fin_cases i
  · simpa using congrFun (congrFun (hPA 2) k) j
  · simpa using congrFun (congrFun hPM2 k) j
  · simpa using congrFun (congrFun hPMM2 k) j

theorem depth_three_gl_terminal_beta_parameter
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P 3))))
    (R : Matrix n (Fin 3 × m) K[X]) (hR : observabilityMatrix M P 3*R=1)
    (hO : Function.Injective (observabilityMatrix M P 4).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (hPX : P*X=0) (hcomm : M*X-X*M=U*P) :
    ∃! E : Matrix r m K[X],
      X*(Matrix.of fun a b => R a (2,b))=polynomialKernelBasisMatrix _ B*E ∧
      E*(P*M^3*polynomialKernelBasisMatrix _ B)=0 := by
  let V := polynomialKernelBasisMatrix (observabilityMatrix M P 3) B
  let A (j : Fin 3) : Matrix n m K[X] := X*(Matrix.of fun a b => R a (j,b))
  have hV (j : ℕ) (hj : j<3) : P*M^j*V=0 := by
    have he := polynomialKernelBasisMatrix_mul (observabilityMatrix M P 3) B
    funext i k
    exact congrFun (congrFun he (⟨j,hj⟩,i)) k
  have hXV : X*V=0 := gl_annihilates_observability_kernel M P X U V 3 hPX hcomm hV hO
  have hXMV : X*M*V=0 := by
    have he := congrArg (fun Y : Matrix n n K[X] => Y*V) hcomm
    have hPV : P*V=0 := by simpa using hV 0 (by omega)
    dsimp only at he
    rw [Matrix.sub_mul,Matrix.mul_assoc M X,hXV,Matrix.mul_zero,
      Matrix.mul_assoc U P,hPV,Matrix.mul_zero] at he
    exact (sub_eq_zero.mp he).symm
  have hX : X=A 0*P+A 1*(P*M)+A 2*(P*M^2) := by
    have he := gl_observability_row_factor M P 3 B R hR hO X U hPX hcomm
    rw [depth_three_observability_row_expansion] at he
    exact he
  have hAF : A 2*(P*M^3*V)=0 := by
    have he : X*M*V=A 0*(P*M*V)+A 1*(P*M^2*V)+A 2*(P*M^3*V) := by
      conv_lhs => rw [hX]
      simp only [pow_succ,pow_zero,Matrix.mul_one,Matrix.one_mul,Matrix.add_mul,Matrix.mul_assoc]
    have hV1 : P*M*V=0 := by simpa using hV 1 (by omega)
    simp only [hV1,hV 2 (by omega),Matrix.mul_zero,zero_add,hXMV] at he
    exact he.symm
  obtain ⟨E,hE⟩ := depth_three_gl_terminal_factor M P B R hR hO X U hPX hcomm
  have hVi := polynomialKernelBasisMatrix_injective (observabilityMatrix M P 3) B
  refine ⟨E,⟨hE,?_⟩,?_⟩
  · apply matrix_left_mul_injective_of_mulVec _ hVi
    change A 2=V*E at hE
    rw [hE] at hAF
    simpa only [V,Matrix.mul_assoc,Matrix.mul_zero] using hAF
  · intro E' hE'
    exact matrix_left_mul_injective_of_mulVec _ hVi (hE'.1.symm.trans hE)

end FD56

/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthTwoBetaKernel
import FD56.Hilbert.MiddleGL

/-! Polynomial normal forms for the second observability range. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K m n r : Type*} [Field K] [Fintype m] [Fintype n] [Fintype r]
  [DecidableEq m] [DecidableEq n] [DecidableEq r]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
theorem depthTwo_stack_mul_zero_iff {t : Type*} (P Q : Matrix m n K[X])
    (Y : Matrix n t K[X]) : depthTwoStack P Q * Y = 0 ↔ P*Y=0 ∧ Q*Y=0 := by
  constructor
  · intro h
    constructor
    · funext i j; exact congrFun (congrFun h (Sum.inl i)) j
    · funext i j; exact congrFun (congrFun h (Sum.inr i)) j
  · rintro ⟨hP,hQ⟩
    funext i j
    cases i with
    | inl i => exact congrFun (congrFun hP i) j
    | inr i => exact congrFun (congrFun hQ i) j

omit [DecidableEq m] [DecidableEq r] in
theorem depthTwo_gl_annihilates_kernel (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P (P*M)))))
    (hF : Function.Injective (P*M*M*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) B).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (hPX : P*X=0) (hcomm : M*X-X*M=U*P) :
    X * polynomialKernelBasisMatrix (depthTwoStack P (P*M)) B = 0 := by
  let V := polynomialKernelBasisMatrix (depthTwoStack P (P*M)) B
  have hOV : depthTwoStack P (P*M) * V = 0 := polynomialKernelBasisMatrix_mul _ B
  obtain ⟨hPV,hPMV⟩ := (depthTwo_stack_mul_zero_iff _ _ V).mp hOV
  have hMXV : M*X*V=X*M*V := by
    have hh := congrArg (fun A : Matrix n n K[X] => A*V) hcomm
    simp only [Matrix.sub_mul,Matrix.mul_assoc,hPV,Matrix.mul_zero] at hh
    simpa only [Matrix.mul_assoc] using sub_eq_zero.mp hh
  have hOXV : depthTwoStack P (P*M) * (X*V) = 0 := by
    apply (depthTwo_stack_mul_zero_iff _ _ _).mpr
    constructor
    · rw [← Matrix.mul_assoc,hPX,Matrix.zero_mul]
    · calc
        (P*M)*(X*V) = P*(M*X*V) := by simp only [Matrix.mul_assoc]
        _ = P*(X*M*V) := by rw [hMXV]
        _ = 0 := by rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hPX,Matrix.zero_mul,Matrix.zero_mul]
  obtain ⟨C,hC⟩ := matrix_factor_through_kernel_basis _ B (X*V) hOXV
  change X*V=V*C at hC
  have hMXMV : M*X*M*V=X*M*M*V := by
    have hh := congrArg (fun A : Matrix n n K[X] => A*M*V) hcomm
    simp only [Matrix.sub_mul,Matrix.mul_assoc,← Matrix.mul_assoc P M V,hPMV,
      Matrix.mul_zero] at hh
    simpa only [Matrix.mul_assoc] using sub_eq_zero.mp hh
  have hFC : (P*M*M*V)*C=0 := by
    calc
      (P*M*M*V)*C = P*M*M*(X*V) := by rw [hC]; simp only [Matrix.mul_assoc]
      _ = P*M*(M*X*V) := by simp only [Matrix.mul_assoc]
      _ = P*M*(X*M*V) := by rw [hMXV]
      _ = P*(M*X*M*V) := by simp only [Matrix.mul_assoc]
      _ = P*(X*M*M*V) := by rw [hMXMV]
      _ = 0 := by rw [← Matrix.mul_assoc,← Matrix.mul_assoc,← Matrix.mul_assoc,
        hPX,Matrix.zero_mul,Matrix.zero_mul,Matrix.zero_mul]
  have hC0 : C=0 := matrix_left_mul_injective_of_mulVec _ hF
    (hFC.trans (Matrix.mul_zero _).symm)
  rw [hC,hC0,Matrix.mul_zero]

omit [DecidableEq r] in
theorem depthTwo_gl_row_factor (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P (P*M)))))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P (P*M)*R=1)
    (hF : Function.Injective (P*M*M*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) B).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (hPX : P*X=0) (hcomm : M*X-X*M=U*P) :
    ∃ A Z : Matrix n m K[X], X=A*P+Z*(P*M) ∧
      depthTwoStack P (P*M)*Z=0 := by
  have hXV := depthTwo_gl_annihilates_kernel M P B hF X U hPX hcomm
  have he := row_factor_through_of_kernel_basis _ B R hR X hXV
  let A : Matrix n m K[X] := fun i j => (X*R) i (Sum.inl j)
  let Z : Matrix n m K[X] := fun i j => (X*R) i (Sum.inr j)
  have hX : X=A*P+Z*(P*M) := by
    rw [he]
    funext i j
    simp only [Matrix.mul_apply,Fintype.sum_sum_type,depthTwoStack,Sum.elim_inl,
      Sum.elim_inr,Matrix.add_apply,A,Z]
  have hPXR : P*(X*R)=0 := by rw [← Matrix.mul_assoc,hPX,Matrix.zero_mul]
  have hPA : P*A=0 := by
    funext i j
    exact congrFun (congrFun hPXR i) (Sum.inl j)
  have hPZ : P*Z=0 := by
    funext i j
    exact congrFun (congrFun hPXR i) (Sum.inr j)
  have hp : P*M*X=P*U*P := by
    have hh := congrArg (fun Y : Matrix n n K[X] => P*Y) hcomm
    simpa only [Matrix.mul_sub,← Matrix.mul_assoc,hPX,Matrix.zero_mul,sub_zero] using hh
  let L : Matrix m (m ⊕ m) K[X] := fun i j => Sum.elim (fun k => (P*M*A-P*U) i k)
      (fun k => (P*M*Z) i k) j
  have hfac : L * depthTwoStack P (P*M) = 0 := by
    have hh : (P*M*A-P*U)*P+(P*M*Z)*(P*M)=0 := by
      rw [Matrix.sub_mul,sub_add_eq_add_sub]
      apply sub_eq_zero.mpr
      simpa only [hX,Matrix.mul_add,Matrix.mul_assoc] using hp
    funext i j
    have he := congrFun (congrFun hh i) j
    simpa only [L,Matrix.mul_apply,Fintype.sum_sum_type,depthTwoStack,Sum.elim_inl,
      Sum.elim_inr,Matrix.add_apply] using he
  have hfac0 := row_factor_unique_of_right_inverse _ R hR L
    0 (hfac.trans (Matrix.zero_mul _).symm)
  have hPMZ : P*M*Z=0 := by
    funext i j
    exact congrFun (congrFun hfac0 i) (Sum.inr j)
  exact ⟨A,Z,hX,(depthTwo_stack_mul_zero_iff _ _ Z).mpr ⟨hPZ,hPMZ⟩⟩

omit [DecidableEq r] in
theorem depthTwo_gl_normal_form (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P (P*M)))))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P (P*M)*R=1)
    (hF : Function.Injective (P*M*M*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) B).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (hPX : P*X=0) (hcomm : M*X-X*M=U*P) :
    let V := polynomialKernelBasisMatrix (depthTwoStack P (P*M)) B
    ∃ E D₀ D₁ : Matrix r m K[X],
      E*(P*M*M*V)=0 ∧ E*P*M*M=D₀*P+D₁*(P*M) ∧
      X=V*(E*P*M-D₁*P)+M*V*E*P ∧
      U=M*M*V*E-M*V*D₁-V*D₀ := by
  intro V
  have hOV : depthTwoStack P (P*M)*V=0 := polynomialKernelBasisMatrix_mul _ B
  obtain ⟨hPV,hPMV⟩ := (depthTwo_stack_mul_zero_iff _ _ V).mp hOV
  have hXV := depthTwo_gl_annihilates_kernel M P B hF X U hPX hcomm
  change X*V=0 at hXV
  obtain ⟨A,Z,hX,hOZ⟩ := depthTwo_gl_row_factor M P B R hR hF X U hPX hcomm
  obtain ⟨E,hZ⟩ := matrix_factor_through_kernel_basis _ B Z hOZ
  change Z=V*E at hZ
  have hXMV : X*M*V=0 := by
    have hh := congrArg (fun Y : Matrix n n K[X] => Y*V) hcomm
    simp only [Matrix.sub_mul,Matrix.mul_assoc,hXV,hPV,Matrix.mul_zero,zero_sub,
      neg_eq_zero] at hh
    simpa only [Matrix.mul_assoc] using hh
  have hEF : E*(P*M*M*V)=0 := by
    have hz : V*(E*(P*M*M*V))=0 := by
      have hh := hXMV
      rw [hX,hZ] at hh
      simpa only [Matrix.add_mul,Matrix.mul_assoc,← Matrix.mul_assoc P M V,hPMV,
        Matrix.mul_zero,zero_add] using hh
    exact matrix_left_mul_injective_of_mulVec V (polynomialKernelBasisMatrix_injective _ B)
      (hz.trans (Matrix.mul_zero _).symm)
  have hEV : (E*P*M*M)*V=0 := by simpa only [Matrix.mul_assoc] using hEF
  have he := row_factor_through_of_kernel_basis _ B R hR (E*P*M*M) hEV
  let D := E*P*M*M*R
  let D₀ : Matrix r m K[X] := fun i j => D i (Sum.inl j)
  let D₁ : Matrix r m K[X] := fun i j => D i (Sum.inr j)
  have hrel : E*P*M*M=D₀*P+D₁*(P*M) := by
    rw [he]
    funext i j
    simp only [Matrix.mul_apply,Fintype.sum_sum_type,depthTwoStack,Sum.elim_inl,
      Sum.elim_inr,Matrix.add_apply,D₀,D₁,D]
  let L : Matrix n (m ⊕ m) K[X] := fun i j =>
    Sum.elim (fun k => (M*A-U-V*D₀) i k) (fun k => (M*V*E-A-V*D₁) i k) j
  have hL : L*depthTwoStack P (P*M)=0 := by
    have heq : (M*A-U-V*D₀)*P+(M*V*E-A-V*D₁)*(P*M) =
        (M*X-X*M)-U*P := by
      rw [hX,hZ]
      have hr : V*(E*P*M*M)=V*(D₀*P+D₁*(P*M)) := congrArg (fun Y => V*Y) hrel
      simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
        Matrix.mul_assoc] at hr ⊢
      rw [hr]
      abel
    have hz : (M*A-U-V*D₀)*P+(M*V*E-A-V*D₁)*(P*M)=0 := by
      rw [heq,hcomm,sub_self]
    funext i j
    simpa only [L,Matrix.mul_apply,Fintype.sum_sum_type,depthTwoStack,Sum.elim_inl,
      Sum.elim_inr,Matrix.add_apply] using congrFun (congrFun hz i) j
  have hL0 := row_factor_unique_of_right_inverse _ R hR L 0
    (hL.trans (Matrix.zero_mul _).symm)
  have hlow : M*A-U-V*D₀=0 := by
    funext i j
    exact congrFun (congrFun hL0 i) (Sum.inl j)
  have hhigh : M*V*E-A-V*D₁=0 := by
    funext i j
    exact congrFun (congrFun hL0 i) (Sum.inr j)
  have hA : A=M*V*E-V*D₁ := by
    have hh := sub_eq_zero.mp hhigh
    apply (eq_sub_iff_add_eq).mpr
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hh).symm
  refine ⟨E,D₀,D₁,hEF,hrel,?_,?_⟩
  · rw [hX,hZ,hA]
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    abel
  · have hu : U=M*A-V*D₀ := by
      have hh := sub_eq_zero.mp hlow
      apply (eq_sub_iff_add_eq).mpr
      simpa only [add_comm] using (sub_eq_iff_eq_add.mp hh).symm
    rw [hu,hA]
    simp only [Matrix.mul_sub,Matrix.mul_assoc]

omit [DecidableEq n] [DecidableEq r] in
theorem depthTwo_gl_parameter_unique (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (V : Matrix n r K[X]) (hV : Function.Injective V.mulVec)
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P (P*M)*R=1)
    (E E' D D' : Matrix r m K[X])
    (hX : V*(E*P*M-D*P)+M*V*E*P = V*(E'*P*M-D'*P)+M*V*E'*P) : E=E' := by
  let L : Matrix n (m ⊕ m) K[X] := fun i j =>
    Sum.elim (fun k => (M*V*E-V*D) i k) (fun k => (V*E) i k) j
  let L' : Matrix n (m ⊕ m) K[X] := fun i j =>
    Sum.elim (fun k => (M*V*E'-V*D') i k) (fun k => (V*E') i k) j
  have he (E D : Matrix r m K[X]) :
      (show Matrix n (m ⊕ m) K[X] from fun i j =>
        Sum.elim (fun k => (M*V*E-V*D) i k) (fun k => (V*E) i k) j) *
        depthTwoStack P (P*M) = V*(E*P*M-D*P)+M*V*E*P := by
    change Matrix.fromCols (M*V*E-V*D) (V*E) * Matrix.fromRows P (P*M) = _
    rw [Matrix.fromCols_mul_fromRows]
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    abel
  have hL : L=L' := row_factor_unique_of_right_inverse _ R hR L L'
    (by simpa only [L,L',he] using hX)
  apply matrix_left_mul_injective_of_mulVec V hV
  funext i j
  exact congrFun (congrFun hL i) (Sum.inr j)

end FD56

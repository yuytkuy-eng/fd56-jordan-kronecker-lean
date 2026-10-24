/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeGLNormalForm

/-! Polynomial reconstruction of third-depth GL stabilizers. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n m r : Type*} [Field K] [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

theorem depth_three_gl_zero_of_terminal_zero
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P 3))))
    (R : Matrix n (Fin 3 × m) K[X]) (hR : observabilityMatrix M P 3*R=1)
    (hO : Function.Injective (observabilityMatrix M P 4).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (hPX : P*X=0) (hcomm : M*X-X*M=U*P)
    (hzero : X*(Matrix.of fun a b => R a (2,b))=0) : X=0 ∧ U=0 := by
  obtain ⟨hX,h1,h2⟩ := depth_three_gl_coefficient_equations M P B R hR hO X U hPX hcomm
  dsimp only at hX h1 h2
  rw [hzero,Matrix.mul_zero,Matrix.zero_mul,add_zero] at h2
  rw [← h2,Matrix.mul_zero,hzero,Matrix.zero_mul,add_zero] at h1
  simp only [hzero,← h2,← h1,Matrix.zero_mul,add_zero] at hX
  refine ⟨hX,?_⟩
  rw [hX,Matrix.mul_zero,Matrix.zero_mul,sub_self] at hcomm
  have he := congrArg (fun Y : Matrix n n K[X] => Y*(Matrix.of fun a b => R a (0,b))) hcomm
  have hPR := depth_three_observability_right_inverse_block M P R hR 0 0
  simp only [Fin.val_zero,pow_zero,Matrix.mul_one,ite_true] at hPR
  simpa only [Matrix.zero_mul,Matrix.mul_assoc,hPR,Matrix.mul_one] using he.symm

def depthThreeReconstructedX (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (V : Matrix n r K[X]) (E F₁ F₂ : Matrix r m K[X]) : Matrix n n K[X] :=
  V*(E*P*M^2-F₂*(P*M)-F₁*P)+M*V*(E*P*M-F₂*P)+M^2*V*E*P

def depthThreeReconstructedU (M : Matrix n n K[X])
    (V : Matrix n r K[X]) (E F₀ F₁ F₂ : Matrix r m K[X]) : Matrix n m K[X] :=
  M^3*V*E-M^2*V*F₂-M*V*F₁-V*F₀

omit [DecidableEq m] [DecidableEq r] in
theorem depth_three_reconstructed_pair_equations
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (V : Matrix n r K[X]) (E F₀ F₁ F₂ : Matrix r m K[X])
    (hPV : P*V=0) (hPMV : P*M*V=0) (hPMMV : P*M^2*V=0)
    (hrel : E*P*M^3=F₀*P+F₁*(P*M)+F₂*(P*M^2)) :
    P*depthThreeReconstructedX M P V E F₁ F₂=0 ∧
      M*depthThreeReconstructedX M P V E F₁ F₂-
        depthThreeReconstructedX M P V E F₁ F₂*M=
          depthThreeReconstructedU M V E F₀ F₁ F₂*P := by
  constructor
  · simp only [depthThreeReconstructedX,Matrix.mul_add,← Matrix.mul_assoc,
      hPV,hPMV,hPMMV,Matrix.zero_mul,add_zero]
  · have hh := congrArg (fun Y : Matrix r n K[X] => V*Y) hrel
    simp only [depthThreeReconstructedX,depthThreeReconstructedU,pow_succ,pow_zero,
      Matrix.mul_one,Matrix.one_mul,Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,
      Matrix.sub_mul,Matrix.mul_assoc] at hh ⊢
    rw [hh]
    abel

omit [DecidableEq r] in
theorem depth_three_reconstructed_terminal
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (R : Matrix n (Fin 3 × m) K[X]) (hR : observabilityMatrix M P 3*R=1)
    (V : Matrix n r K[X]) (E F₁ F₂ : Matrix r m K[X]) :
    depthThreeReconstructedX M P V E F₁ F₂*(Matrix.of fun a b => R a (2,b))=V*E := by
  let R₂ : Matrix n m K[X] := Matrix.of fun a b => R a (2,b)
  have h0 := depth_three_observability_right_inverse_block M P R hR 0 2
  have h1 := depth_three_observability_right_inverse_block M P R hR 1 2
  have h2 := depth_three_observability_right_inverse_block M P R hR 2 2
  simp [Fin.ext_iff] at h0 h1 h2
  have he : depthThreeReconstructedX M P V E F₁ F₂*R₂=
      V*(E*((P*M^2)*R₂)-F₂*((P*M)*R₂)-F₁*(P*R₂))+
      M*V*(E*((P*M)*R₂)-F₂*(P*R₂))+M^2*V*E*(P*R₂) := by
    simp only [depthThreeReconstructedX,Matrix.add_mul,Matrix.sub_mul,Matrix.mul_sub,
      Matrix.mul_assoc]
  simpa only [R₂,h0,h1,h2,Matrix.mul_one,Matrix.mul_zero,sub_zero,sub_self,add_zero] using he

theorem depth_three_gl_reconstruction
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P 3))))
    (R : Matrix n (Fin 3 × m) K[X]) (hR : observabilityMatrix M P 3*R=1)
    (hO : Function.Injective (observabilityMatrix M P 4).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (hPX : P*X=0) (hcomm : M*X-X*M=U*P)
    (E F₀ F₁ F₂ : Matrix r m K[X])
    (hE : X*(Matrix.of fun a b => R a (2,b))=polynomialKernelBasisMatrix _ B*E)
    (hrel : E*P*M^3=F₀*P+F₁*(P*M)+F₂*(P*M^2)) :
    X=depthThreeReconstructedX M P (polynomialKernelBasisMatrix _ B) E F₁ F₂ ∧
    U=depthThreeReconstructedU M (polynomialKernelBasisMatrix _ B) E F₀ F₁ F₂ := by
  let V := polynomialKernelBasisMatrix (observabilityMatrix M P 3) B
  let Y := depthThreeReconstructedX M P V E F₁ F₂
  let W := depthThreeReconstructedU M V E F₀ F₁ F₂
  have hV (j : ℕ) (hj : j<3) : P*M^j*V=0 := by
    have he := polynomialKernelBasisMatrix_mul (observabilityMatrix M P 3) B
    funext i k
    exact congrFun (congrFun he (⟨j,hj⟩,i)) k
  have hpair := depth_three_reconstructed_pair_equations M P V E F₀ F₁ F₂
    (by simpa using hV 0 (by omega)) (by simpa using hV 1 (by omega))
    (hV 2 (by omega)) hrel
  have hz := depth_three_gl_zero_of_terminal_zero M P B R hR hO (X-Y) (U-W)
    (by simp only [Y,Matrix.mul_sub,hPX,hpair.1,sub_self])
    (by
      have hh : M*(X-Y)-(X-Y)*M=(M*X-X*M)-(M*Y-Y*M) := by
        simp only [Matrix.mul_sub,Matrix.sub_mul]; abel
      rw [hh,hcomm,hpair.2,Matrix.sub_mul])
    (by rw [Matrix.sub_mul,hE,depth_three_reconstructed_terminal M P R hR]; exact sub_self _)
  exact ⟨sub_eq_zero.mp hz.1,sub_eq_zero.mp hz.2⟩

theorem exists_depth_three_beta_coefficients {l : Type*}
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P 3))))
    (R : Matrix n (Fin 3 × m) K[X]) (hR : observabilityMatrix M P 3*R=1)
    (E : Matrix l m K[X]) (hEF : E*(P*M^3*polynomialKernelBasisMatrix _ B)=0) :
    ∃ F₀ F₁ F₂ : Matrix l m K[X], E*P*M^3=F₀*P+F₁*(P*M)+F₂*(P*M^2) := by
  have he := observability_beta_relation M P 3 B R hR E hEF
  let C := E*P*M^3*R
  refine ⟨Matrix.of (fun i j => C i (0,j)),Matrix.of (fun i j => C i (1,j)),
    Matrix.of (fun i j => C i (2,j)),?_⟩
  conv_lhs => rw [he]
  funext i j
  simp [C,Matrix.mul_apply,observabilityMatrix,Fintype.sum_prod_type,Fin.sum_univ_succ,
    Finset.mul_sum,Finset.sum_mul,Finset.sum_add_distrib,add_assoc,Matrix.one_apply]

theorem depth_three_gl_normal_form
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P 3))))
    (R : Matrix n (Fin 3 × m) K[X]) (hR : observabilityMatrix M P 3*R=1)
    (hO : Function.Injective (observabilityMatrix M P 4).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (hPX : P*X=0) (hcomm : M*X-X*M=U*P) :
    ∃ E F₀ F₁ F₂ : Matrix r m K[X],
      E*(P*M^3*polynomialKernelBasisMatrix _ B)=0 ∧
      E*P*M^3=F₀*P+F₁*(P*M)+F₂*(P*M^2) ∧
      X=depthThreeReconstructedX M P (polynomialKernelBasisMatrix _ B) E F₁ F₂ ∧
      U=depthThreeReconstructedU M (polynomialKernelBasisMatrix _ B) E F₀ F₁ F₂ := by
  obtain ⟨E,⟨hE,hEF⟩,_⟩ := depth_three_gl_terminal_beta_parameter M P B R hR hO X U hPX hcomm
  obtain ⟨F₀,F₁,F₂,hrel⟩ := exists_depth_three_beta_coefficients M P B R hR E hEF
  exact ⟨E,F₀,F₁,F₂,hEF,hrel,
    depth_three_gl_reconstruction M P B R hR hO X U hPX hcomm E F₀ F₁ F₂ hE hrel⟩

end FD56

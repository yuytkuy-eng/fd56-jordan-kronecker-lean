/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedOneSingleHighWitness

/-! Attaching cubic columns to a polynomial matrix with a split row completion. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K m r q : Type*} [Field K] [Fintype m] [Fintype r] [Fintype q]
  [DecidableEq m] [DecidableEq r] [DecidableEq q]

def cubicRowExtension (G : Matrix m r K[X]) (S : Matrix m q K[X]) :
    Matrix (q ⊕ m) (q ⊕ r) K[X] :=
  Matrix.fromBlocks ((X^3 : K[X]) • 1) 0 (-S) G

def cubicRowExtensionKernel (V : Matrix q m K[X]) (S : Matrix m q K[X]) :
    Matrix q (q ⊕ m) K[X] :=
  Matrix.fromCols (V*S) ((X^3 : K[X]) • V)

def cubicRowExtensionRight (R : Matrix r m K[X]) (W : Matrix q q K[X])
    (V : Matrix q m K[X]) : Matrix (q ⊕ r) (q ⊕ m) K[X] :=
  Matrix.fromBlocks 0 (-(W*V)) 0 R

omit [Fintype r] [DecidableEq m] [DecidableEq r] in
theorem cubicRowExtension_kernel (G : Matrix m r K[X]) (S : Matrix m q K[X])
    (V : Matrix q m K[X]) (hV : V*G=0) :
    cubicRowExtensionKernel V S * cubicRowExtension G S = 0 := by
  simp [cubicRowExtensionKernel, cubicRowExtension, Matrix.fromCols_mul_fromBlocks,
    Matrix.mul_smul, Matrix.smul_mul, hV]

omit [Fintype r] [DecidableEq m] in
theorem cubicRowExtension_right (G : Matrix m r K[X]) (S : Matrix m q K[X])
    (R : Matrix r m K[X]) (V : Matrix q m K[X]) (W : Matrix q q K[X])
    (hRG : R*G=1) (hRS : R*S=0) (hVG : V*G=0) (hW : W*(V*S)=1) :
    cubicRowExtensionRight R W V * cubicRowExtension G S = 1 := by
  simp [cubicRowExtensionRight, cubicRowExtension, Matrix.fromBlocks_multiply,
    Matrix.mul_assoc, hRG, hRS, hVG, hW, Matrix.fromBlocks_one]

omit [DecidableEq r] in
theorem cubicRowExtension_completion (G : Matrix m r K[X]) (S : Matrix m q K[X])
    (R : Matrix r m K[X]) (V : Matrix q m K[X]) (W : Matrix q q K[X])
    (hcomp : G*R+S*W*V=1) (hW : W*(V*S)=1) :
    cubicRowExtension G S * cubicRowExtensionRight R W V +
      Matrix.fromRows (1 : Matrix q q K[X]) (0 : Matrix m q K[X]) * W *
        cubicRowExtensionKernel V S = 1 := by
  have hcomp' : S*(W*V)+G*R=1 := by simpa [Matrix.mul_assoc, add_comm] using hcomp
  simp only [cubicRowExtension, cubicRowExtensionRight, cubicRowExtensionKernel,
    Matrix.fromBlocks_multiply, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
    Matrix.mul_fromCols,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hW,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    zero_add, add_zero, Matrix.mul_neg, Matrix.neg_mul, neg_neg, hcomp']
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;> simp [Matrix.fromRows, Matrix.fromCols, Matrix.fromBlocks,
    Matrix.smul_apply, Matrix.one_apply]

/-- A scalar relation in the old rows loses exactly three degrees once its scalar
is divisible by `X^3`. The completion makes this a polynomial identity. -/
theorem cubicRowExtension_scalar_descent
    (G : Matrix m r K[X]) (S : Matrix m q K[X])
    (R : Matrix r m K[X]) (V : Matrix q m K[X]) (W : Matrix q q K[X])
    (hcomp : G*R+S*W*V=1)
    (E : Matrix (q ⊕ r) (q ⊕ m) K[X]) (c : K[X])
    (hrel : E*cubicRowExtension G S=(-c) • 1)
    (c' : K[X]) (hc : c=X^3*c') :
    ∃ F : Matrix r m K[X],
      (E.submatrix Sum.inr Sum.inr = (X^3 : K[X]) • F) ∧ F*G=(-c') • 1 := by
  let E₁₀ : Matrix r q K[X] := E.submatrix Sum.inr Sum.inl
  let E₁₁ : Matrix r m K[X] := E.submatrix Sum.inr Sum.inr
  have hblocks : E = Matrix.fromBlocks (E.submatrix Sum.inl Sum.inl)
      (E.submatrix Sum.inl Sum.inr) E₁₀ E₁₁ := by
    ext i j
    cases i <;> cases j <;> rfl
  have hold : E₁₁*G=(-c) • (1 : Matrix r r K[X]) := by
    have h := congrArg (fun A : Matrix (q ⊕ r) (q ⊕ r) K[X] =>
      A.submatrix Sum.inr Sum.inr) hrel
    rw [hblocks] at h
    simp only [cubicRowExtension, Matrix.fromBlocks_multiply] at h
    apply Matrix.ext
    intro i j
    simpa [Matrix.submatrix,
      Matrix.fromBlocks, Matrix.smul_apply, Matrix.one_apply] using
      congrArg (fun A : Matrix r r K[X] => A i j) h
  have hsel : E₁₁*S=(X^3 : K[X]) • E₁₀ := by
    have h := congrArg (fun A : Matrix (q ⊕ r) (q ⊕ r) K[X] =>
      A.submatrix Sum.inr Sum.inl) hrel
    have hzero : (X^3 : K[X]) • E₁₀ - E₁₁*S=0 := by
      rw [hblocks] at h
      simp only [cubicRowExtension, Matrix.fromBlocks_multiply] at h
      simpa [Matrix.submatrix,
        Matrix.fromBlocks, Matrix.smul_apply, Matrix.one_apply,
        Matrix.mul_smul, sub_eq_add_neg] using h
    exact (sub_eq_zero.mp hzero).symm
  let F : Matrix r m K[X] := (-c') • R+E₁₀*W*V
  have hfactor : E₁₁=(X^3 : K[X]) • F := by
    calc
      E₁₁ = E₁₁*(G*R+S*W*V) := by rw [hcomp, Matrix.mul_one]
      _ = (E₁₁*G)*R+(E₁₁*S)*W*V := by simp [Matrix.mul_add, Matrix.mul_assoc]
      _ = (X^3 : K[X]) • F := by
        rw [hold, hsel, hc]
        simp [F, Matrix.smul_mul, smul_add, smul_smul, neg_mul]
  refine ⟨F, hfactor, ?_⟩
  have heq : (X^3 : K[X]) • (F*G)=(X^3 : K[X]) • ((-c') • (1 : Matrix r r K[X])) := by
    rw [← Matrix.smul_mul, ← hfactor, hold, hc]
    simp [smul_smul, neg_mul]
  apply Matrix.ext
  intro i j
  exact mul_left_cancel₀ (pow_ne_zero 3 (X_ne_zero : (X : K[X]) ≠ 0))
    (by simpa only [Matrix.smul_apply, smul_eq_mul] using
      congrArg (fun A : Matrix r r K[X] => A i j) heq)

theorem polynomial_cubic_factor_degree (p p' : K[X]) (d : ℕ)
    (h : p=X^3*p') (hd : p.natDegree ≤ d+3) : p'.natDegree ≤ d := by
  by_cases hp : p'=0
  · simp [hp]
  · rw [h, Polynomial.natDegree_X_pow_mul _ hp] at hd
    omega

theorem cubicRowExtension_new_coordinates
    (G : Matrix m r K[X]) (S : Matrix m q K[X])
    (R : Matrix r m K[X]) (V : Matrix q m K[X]) (W : Matrix q q K[X])
    (hcomp : G*R+S*W*V=1)
    (E : Matrix (q ⊕ r) (q ⊕ m) K[X]) (c : K[X])
    (hrel : E*cubicRowExtension G S=(-c) • 1) :
    ∃ Q : Matrix q q K[X], E.submatrix Sum.inl Sum.inr=Q*V ∧
      Q=((X^3 : K[X]) • E.submatrix Sum.inl Sum.inl+c • 1)*W := by
  let E₀₀ : Matrix q q K[X] := E.submatrix Sum.inl Sum.inl
  let E₀₁ : Matrix q m K[X] := E.submatrix Sum.inl Sum.inr
  have hblocks : E=Matrix.fromBlocks E₀₀ E₀₁
      (E.submatrix Sum.inr Sum.inl) (E.submatrix Sum.inr Sum.inr) := by
    ext i j
    cases i <;> cases j <;> rfl
  have hold : E₀₁*G=0 := by
    have h := congrArg (fun A : Matrix (q ⊕ r) (q ⊕ r) K[X] =>
      A.submatrix Sum.inl Sum.inr) hrel
    rw [hblocks] at h
    simp only [cubicRowExtension, Matrix.fromBlocks_multiply] at h
    simpa [Matrix.submatrix, Matrix.fromBlocks, Matrix.smul_apply, Matrix.one_apply] using h
  have hsel : E₀₁*S=(X^3 : K[X]) • E₀₀+c • 1 := by
    have h := congrArg (fun A : Matrix (q ⊕ r) (q ⊕ r) K[X] =>
      A.submatrix Sum.inl Sum.inl) hrel
    rw [hblocks] at h
    simp only [cubicRowExtension, Matrix.fromBlocks_multiply] at h
    apply Matrix.ext
    intro i j
    have hh := congrArg (fun A : Matrix q q K[X] => A i j) h
    simp [Matrix.submatrix, Matrix.fromBlocks, Matrix.smul_apply,
      Matrix.one_apply, Matrix.mul_smul] at hh ⊢
    by_cases hij : i=j <;> simp [hij] at hh ⊢ <;> linear_combination -hh
  refine ⟨E₀₁*S*W, ?_, by rw [hsel]⟩
  calc
    E₀₁ = E₀₁*(G*R+S*W*V) := by rw [hcomp, Matrix.mul_one]
    _ = E₀₁*S*W*V := by simp [Matrix.mul_add, ← Matrix.mul_assoc, hold]

omit [Fintype q] [DecidableEq m] [DecidableEq q] in
theorem cubicRowExtensionKernel_degree (V : Matrix q m K[X]) (S : Matrix m q K[X])
    (b : q → ℕ) (hV : ∀ j x, (V j x).natDegree ≤ b j)
    (hA : ∀ i j, ((V*S) i j).natDegree ≤ 2) :
    ∀ j x, (cubicRowExtensionKernel V S j x).natDegree ≤ b j+3 := by
  intro j x
  cases x with
  | inl x => exact (hA j x).trans (by omega)
  | inr x =>
    change (X^3 * V j x).natDegree ≤ b j+3
    exact Polynomial.natDegree_mul_le.trans (by
      have h := hV j x
      simp only [natDegree_X_pow]
      omega)

omit [DecidableEq m] [DecidableEq q] in
theorem cubicRowExtensionKernel_leading (V : Matrix q m K[X]) (S : Matrix m q K[X])
    (b : q → ℕ)
    (hV : Function.Injective (Matrix.mulVec (fun x j => (V j x).coeff (b j)))) :
    Function.Injective (Matrix.mulVec
      (fun x j => (cubicRowExtensionKernel V S j x).coeff (b j+3))) := by
  intro u v h
  apply hV
  funext x
  simpa [Matrix.mulVec, dotProduct, cubicRowExtensionKernel, Matrix.fromCols,
    Matrix.smul_apply, smul_eq_mul, coeff_X_pow_mul, Nat.add_comm] using
    congrFun h (Sum.inr x)

end FD56

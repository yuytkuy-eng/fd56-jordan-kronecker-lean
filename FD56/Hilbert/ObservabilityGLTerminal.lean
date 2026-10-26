/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityGLReduction
import FD56.Hilbert.ObservabilityGLRecurrence

/-! The actual GL equations determine the terminal auxiliary parameter at any depth. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m r : Type*} [Field K] [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

theorem observability_row_expansion (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (q : ℕ) (A : Matrix n (Fin q × m) K[X]) :
    A * observabilityMatrix M P q =
      ∑ j : Fin q, (Matrix.of fun a b => A a (j,b)) * (P * M ^ j.val) := by
  funext a b
  simp only [Matrix.mul_apply, observabilityMatrix, Fintype.sum_prod_type,
    Matrix.sum_apply, Matrix.of_apply]

theorem observability_right_inverse_block (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (q : ℕ) (R : Matrix n (Fin q × m) K[X]) (hR : observabilityMatrix M P q * R = 1)
    (i j : Fin q) :
    (P * M ^ i.val) * (Matrix.of fun a b => R a (j,b)) = if i = j then 1 else 0 := by
  funext a b
  have he := congrFun (congrFun hR (i,a)) (j,b)
  change ((P * M ^ i.val) * (Matrix.of fun a b => R a (j,b))) a b = _ at he
  by_cases h : i = j <;> simpa [h, Matrix.one_apply, Prod.ext_iff] using he

theorem observability_right_inverse_shift (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (q : ℕ) (R : Matrix n (Fin (q+1) × m) K[X])
    (hR : observabilityMatrix M P (q+1) * R = 1)
    (A : Fin (q+1) → Matrix n m K[X]) (j : Fin q) :
    (∑ i : Fin (q+1), A i * (P * M ^ i.val)) * M * (Matrix.of fun a b => R a (j.succ,b)) =
      A j.castSucc + A (Fin.last q) * (P * M ^ (q+1) * (Matrix.of fun a b => R a (j.succ,b))) := by
  have he (i : Fin (q+1)) :
      (A i * (P * M ^ i.val)) * M * (Matrix.of fun a b => R a (j.succ,b)) =
        A i * (P * M ^ (i.val+1) * (Matrix.of fun a b => R a (j.succ,b))) := by
    rw [pow_succ]
    simp only [Matrix.mul_assoc]
  rw [Matrix.sum_mul, Matrix.sum_mul]
  simp_rw [he]
  rw [Fin.sum_univ_castSucc]
  congr 1
  have hb (i : Fin q) :
      P * M ^ (i.castSucc.val+1) * (Matrix.of fun a b => R a (j.succ,b)) =
        if i = j then 1 else 0 := by
    simpa using observability_right_inverse_block M P (q+1) R hR i.succ j.succ
  simp only [hb]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hbj
    rw [if_neg hbj, Matrix.mul_zero]
  · simp

theorem gl_observability_coefficient_recurrence
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ)
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P (q+1)))))
    (R : Matrix n (Fin (q+1) × m) K[X]) (hR : observabilityMatrix M P (q+1) * R = 1)
    (hO : Function.Injective (observabilityMatrix M P (q+2)).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (hPX : P * X = 0) (hcomm : M * X - X * M = U * P) (j : Fin q) :
    let Rb (i : Fin (q+1)) : Matrix n m K[X] := Matrix.of fun a b => R a (i,b)
    M * (X * Rb j.succ) = X * Rb j.castSucc +
      (X * Rb (Fin.last q)) * (P * M ^ (q+1) * Rb j.succ) := by
  intro Rb
  have hX : X = ∑ i : Fin (q+1), (X * Rb i) * (P * M ^ i.val) := by
    have he := gl_observability_row_factor M P (q+1) B R hR hO X U hPX hcomm
    rw [observability_row_expansion] at he
    exact he
  have hshift := observability_right_inverse_shift M P q R hR (fun i => X * Rb i) j
  rw [← hX] at hshift
  have h0 : P * Rb j.succ = 0 := by
    have he := observability_right_inverse_block M P (q+1) R hR 0 j.succ
    simpa [Fin.ext_iff] using he
  have he := congrArg (fun Y : Matrix n n K[X] => Y * Rb j.succ) hcomm
  dsimp only at he
  rw [Matrix.sub_mul, hshift, Matrix.mul_assoc U P, h0, Matrix.mul_zero] at he
  simpa only [Matrix.mul_assoc] using sub_eq_zero.mp he

theorem gl_finite_recurrence_annihilation
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ)
    (A : Fin (q+1) → Matrix n m K[X]) (D : Fin q → Matrix m m K[X])
    (hPA : ∀ j, P * A j = 0)
    (hrec : ∀ j, M * A j.succ = A j.castSucc + A (Fin.last q) * D j)
    (i : ℕ) (j : Fin (q+1)) (hij : i ≤ j.val) : P * M ^ i * A j = 0 := by
  induction i generalizing j with
  | zero => simpa using hPA j
  | succ i ih =>
    let k : Fin q := ⟨j.val-1, by have := j.isLt; omega⟩
    have hkj : k.succ = j := by apply Fin.ext; dsimp [k]; omega
    have hleft := ih k.castSucc (by dsimp [k]; omega)
    have hright := ih (Fin.last q) (by have := j.isLt; simp; omega)
    rw [← hkj]
    calc
      P * M ^ (i+1) * A k.succ = (P * M ^ i) * (M * A k.succ) := by
        rw [pow_succ]; simp only [Matrix.mul_assoc]
      _ = 0 := by
        rw [hrec, Matrix.mul_add, ← Matrix.mul_assoc (P * M ^ i), hleft,
          hright, Matrix.zero_mul, add_zero]

theorem gl_observability_terminal_factor
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ)
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P (q+1)))))
    (R : Matrix n (Fin (q+1) × m) K[X]) (hR : observabilityMatrix M P (q+1) * R = 1)
    (hO : Function.Injective (observabilityMatrix M P (q+2)).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (hPX : P * X = 0) (hcomm : M * X - X * M = U * P) :
    ∃ E : Matrix r m K[X],
      X * (Matrix.of fun a b => R a (Fin.last q,b)) = polynomialKernelBasisMatrix _ B * E := by
  let Rb (j : Fin (q+1)) : Matrix n m K[X] := Matrix.of fun a b => R a (j,b)
  let A (j : Fin (q+1)) := X * Rb j
  let D (j : Fin q) := P * M ^ (q+1) * Rb j.succ
  have hPA (j) : P * A j = 0 := by
    dsimp only [A]
    rw [← Matrix.mul_assoc, hPX, Matrix.zero_mul]
  have hrec (j) : M * A j.succ = A j.castSucc + A (Fin.last q) * D j :=
    gl_observability_coefficient_recurrence M P q B R hR hO X U hPX hcomm j
  apply matrix_factor_through_kernel_basis _ B (A (Fin.last q))
  funext i j
  change ((P * M ^ i.1.val) * A (Fin.last q)) i.2 j = 0
  exact congrFun (congrFun (gl_finite_recurrence_annihilation M P q A D hPA hrec
    i.1.val (Fin.last q) (by have := i.1.isLt; simp; omega)) i.2) j

theorem gl_observability_terminal_beta_parameter
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ)
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P (q+1)))))
    (R : Matrix n (Fin (q+1) × m) K[X]) (hR : observabilityMatrix M P (q+1) * R = 1)
    (hO : Function.Injective (observabilityMatrix M P (q+2)).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (hPX : P * X = 0) (hcomm : M * X - X * M = U * P) :
    ∃! E : Matrix r m K[X],
      X * (Matrix.of fun a b => R a (Fin.last q,b)) = polynomialKernelBasisMatrix _ B * E ∧
      E * (P * M ^ (q+1) * polynomialKernelBasisMatrix _ B) = 0 := by
  let V := polynomialKernelBasisMatrix (observabilityMatrix M P (q+1)) B
  let Rb (j : Fin (q+1)) : Matrix n m K[X] := Matrix.of fun a b => R a (j,b)
  let A (j : Fin (q+1)) := X * Rb j
  have hV (i : ℕ) (hi : i < q+1) : P * M ^ i * V = 0 := by
    have he := polynomialKernelBasisMatrix_mul (observabilityMatrix M P (q+1)) B
    funext a b
    exact congrFun (congrFun he (⟨i,hi⟩,a)) b
  have hXV : X * V = 0 :=
    gl_annihilates_observability_kernel M P X U V (q+1) hPX hcomm hV hO
  have hXMV : X * M * V = 0 := by
    have he := congrArg (fun Y : Matrix n n K[X] => Y * V) hcomm
    have hPV : P * V = 0 := by simpa using hV 0 (by omega)
    dsimp only at he
    rw [Matrix.sub_mul, Matrix.mul_assoc M X, hXV, Matrix.mul_zero,
      Matrix.mul_assoc U P, hPV, Matrix.mul_zero] at he
    exact (sub_eq_zero.mp he).symm
  have hX : X = ∑ i : Fin (q+1), A i * (P * M ^ i.val) := by
    have he := gl_observability_row_factor M P (q+1) B R hR hO X U hPX hcomm
    rw [observability_row_expansion] at he
    exact he
  have hAF : A (Fin.last q) * (P * M ^ (q+1) * V) = 0 := by
    have he : X * M * V = ∑ i : Fin (q+1), A i * (P * M ^ (i.val+1) * V) := by
      conv_lhs => rw [hX]
      rw [Matrix.sum_mul, Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ]
      simp only [Matrix.mul_assoc]
    rw [Fin.sum_univ_castSucc] at he
    have hz : (∑ i : Fin q, A i.castSucc * (P * M ^ (i.castSucc.val+1) * V)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hV _ (by have := i.isLt; simp only [Fin.coe_castSucc]; omega), Matrix.mul_zero]
    rw [hz, zero_add, hXMV] at he
    exact he.symm
  obtain ⟨E,hE⟩ := gl_observability_terminal_factor M P q B R hR hO X U hPX hcomm
  have hVi := polynomialKernelBasisMatrix_injective (observabilityMatrix M P (q+1)) B
  refine ⟨E,⟨hE,?_⟩,?_⟩
  · apply matrix_left_mul_injective_of_mulVec _ hVi
    change A (Fin.last q) = V * E at hE
    rw [hE] at hAF
    simpa only [V, Matrix.mul_assoc, Matrix.mul_zero] using hAF
  · intro E' hE'
    exact matrix_left_mul_injective_of_mulVec _ hVi (hE'.1.symm.trans hE)

end FD56

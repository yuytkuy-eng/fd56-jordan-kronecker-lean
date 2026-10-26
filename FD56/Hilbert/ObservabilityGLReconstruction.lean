/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityBackwardRows

/-! Polynomial reconstruction of GL stabilizers from the terminal auxiliary coefficient. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m r s : Type*} [Field K]
  [Fintype n] [Fintype m] [Fintype r] [Fintype s]
  [DecidableEq n] [DecidableEq m] [DecidableEq r] [DecidableEq s]

theorem gl_observability_zero_of_terminal_zero
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ)
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P (q+1)))))
    (R : Matrix n (Fin (q+1) × m) K[X]) (hR : observabilityMatrix M P (q+1) * R = 1)
    (hO : Function.Injective (observabilityMatrix M P (q+2)).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (hPX : P * X = 0) (hcomm : M * X - X * M = U * P)
    (hzero : X * (Matrix.of fun a b => R a (Fin.last q,b)) = 0) : X = 0 ∧ U = 0 := by
  let Rb (j : Fin (q+1)) : Matrix n m K[X] := Matrix.of fun a b => R a (j,b)
  have hz (j : Fin (q+1)) : X * Rb j = 0 := by
    induction j using Fin.reverseInduction with
    | last => exact hzero
    | cast j ih =>
      have he := gl_observability_coefficient_recurrence M P q Bv R hR hO X U hPX hcomm j
      change M * (X * Rb j.succ) = X * Rb j.castSucc +
        (X * Rb (Fin.last q)) * (P * M ^ (q+1) * Rb j.succ) at he
      rw [ih, Matrix.mul_zero, hzero, Matrix.zero_mul, add_zero] at he
      exact he.symm
  have hX : X = 0 := by
    have he := gl_observability_row_factor M P (q+1) Bv R hR hO X U hPX hcomm
    rw [observability_row_expansion] at he
    have hx : X = ∑ j : Fin (q+1), (X * Rb j) * (P * M ^ j.val) := he
    simpa only [hz, Matrix.zero_mul, Finset.sum_const_zero] using hx
  refine ⟨hX,?_⟩
  rw [hX, Matrix.mul_zero, Matrix.zero_mul, sub_self] at hcomm
  have he := congrArg (fun Y : Matrix n n K[X] => Y * Rb 0) hcomm
  have hPR := observability_right_inverse_block M P (q+1) R hR 0 0
  simp only [Fin.val_zero, pow_zero, Matrix.mul_one, if_true] at hPR
  change P * Rb 0 = 1 at hPR
  simpa only [Matrix.zero_mul, Matrix.mul_assoc, hPR, Matrix.mul_one] using he.symm

theorem structured_observability_terminal
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ)
    (R : Matrix n (Fin (q+1) × m) K[X]) (hR : observabilityMatrix M P (q+1) * R = 1)
    (V : Matrix n r K[X]) (C : Matrix r s K[X])
    (H : ℕ → Matrix s n K[X]) (D : ℕ → Matrix s m K[X]) (T : Matrix s m K[X])
    (hstep : ∀ i < q, H (i+1) * M = H i + D (i+1) * P) (hend : H q = T * P) :
    (∑ i ∈ Finset.range (q+1), M ^ i * V * C * H i) *
      (Matrix.of fun a b => R a (Fin.last q,b)) = V * C * T := by
  let B : Matrix n m K[X] := Matrix.of fun a b => R a (Fin.last q,b)
  have hB (j : ℕ) (hj : j ≤ q) : P * M ^ j * B = if j = q then 1 else 0 := by
    simpa only [Fin.ext_iff, Fin.val_last] using
      observability_right_inverse_block M P (q+1) R hR ⟨j,by omega⟩ (Fin.last q)
  have hH (i : ℕ) (hi : i ≤ q) : H i * B = if i = 0 then T else 0 := by
    simpa only [pow_zero, Matrix.mul_one, eq_comm] using
      backward_rows_terminal_recovery M P H D T q B hstep hend hB i hi 0 (Nat.zero_le i)
  change (∑ i ∈ Finset.range (q+1), M ^ i * V * C * H i) * B = _
  rw [Matrix.sum_mul, Finset.sum_eq_single 0]
  · rw [Matrix.mul_assoc, hH 0 (by omega)]
    simp
  · intro i hi hne
    rw [Matrix.mul_assoc, hH i (by have := Finset.mem_range.mp hi; omega), if_neg hne,
      Matrix.mul_zero]
  · simp

theorem gl_observability_structured_reconstruction
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ)
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P (q+1)))))
    (R : Matrix n (Fin (q+1) × m) K[X]) (hR : observabilityMatrix M P (q+1) * R = 1)
    (hO : Function.Injective (observabilityMatrix M P (q+2)).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (hPX : P * X = 0) (hcomm : M * X - X * M = U * P)
    (C : Matrix r s K[X]) (H : ℕ → Matrix s n K[X])
    (D : ℕ → Matrix s m K[X]) (T : Matrix s m K[X])
    (hzero : H 0 * M = D 0 * P)
    (hstep : ∀ i < q, H (i+1) * M = H i + D (i+1) * P) (hend : H q = T * P)
    (hE : X * (Matrix.of fun a b => R a (Fin.last q,b)) = polynomialKernelBasisMatrix _ Bv * C * T) :
    let V := polynomialKernelBasisMatrix _ Bv
    X = ∑ i ∈ Finset.range (q+1), M ^ i * V * C * H i ∧
      U = M ^ (q+1) * V * C * T - ∑ i ∈ Finset.range (q+1), M ^ i * V * C * D i := by
  intro V
  let Y := ∑ i ∈ Finset.range (q+1), M ^ i * V * C * H i
  let W := M ^ (q+1) * V * C * T - ∑ i ∈ Finset.range (q+1), M ^ i * V * C * D i
  have hV (i : ℕ) (hi : i < q+1) : P * M ^ i * V = 0 := by
    have he := polynomialKernelBasisMatrix_mul (observabilityMatrix M P (q+1)) Bv
    funext a b
    exact congrFun (congrFun he (⟨i,hi⟩,a)) b
  have hpair := structured_kernel M P V C H D T q hzero hstep hend hV
  have hz := gl_observability_zero_of_terminal_zero M P q Bv R hR hO (X-Y) (U-W)
    (by simp only [Y, Matrix.mul_sub, hPX, hpair.1, sub_self])
    (by
      have he : M * (X-Y) - (X-Y) * M = (M*X-X*M) - (M*Y-Y*M) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
      rw [he, hcomm, hpair.2]
      simp only [W, Matrix.sub_mul])
    (by
      rw [Matrix.sub_mul, hE, structured_observability_terminal M P q R hR V C H D T hstep hend]
      exact sub_self _)
  exact ⟨sub_eq_zero.mp hz.1, sub_eq_zero.mp hz.2⟩

end FD56

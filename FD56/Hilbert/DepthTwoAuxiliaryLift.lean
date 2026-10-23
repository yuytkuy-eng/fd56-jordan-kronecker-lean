/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthTwoRowLifting

/-! Two bounded lifts realize an arbitrary terminal matrix while preserving
the kernel of the depth-two stack. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K m n r : Type*} [Field K]
  [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq n]

omit [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq n] in
theorem depthTwo_auxiliary_lift_of_coefficient_surjective
    (P Q : Matrix m n K[X]) (V : Matrix n r K[X]) (a : r → ℕ)
    (hP : DegreeBound P 1) (hQ : DegreeBound Q 2)
    (hV : ∀ x j, (V x j).natDegree ≤ a j)
    (hstack : ∀ j, Function.Surjective
      (weightedCoefficientMatrix (depthTwoStack P Q) (fun _ => a j + 1)
        (fun i => a j + 1 + depthTwoRowDegree i)).mulVec)
    (hrow : Function.Surjective (weightedCoefficientMatrix V.transpose
      (fun _ => 1) (fun j => a j + 1)).mulVec)
    (F : Matrix m r K[X]) (hF : ∀ x j, (F x j).natDegree ≤ a j + 3) :
    ∃ M : Matrix n n K[X], DegreeBound M 1 ∧ P * M * V = 0 ∧ Q * M * V = F := by
  have hcolumns (j : r) : ∃ v : n → K[X],
      (∀ x, (v x).natDegree ≤ a j + 1) ∧
      depthTwoStack P Q *ᵥ v = Sum.elim (fun _ => 0) (fun x => F x j) := by
    have hdeg : ∀ i x, (depthTwoStack P Q i x).natDegree + (a j + 1) ≤
        a j + 1 + depthTwoRowDegree i := by
      intro i x
      have h := depthTwo_stack_degree P Q hP hQ i x
      omega
    apply weighted_coefficient_surjective_lift (depthTwoStack P Q)
      (fun _ => a j + 1) (fun i => a j + 1 + depthTwoRowDegree i) hdeg (hstack j)
    intro i
    cases i with
    | inl i => simp
    | inr i => simpa [depthTwoRowDegree, Nat.add_assoc] using hF i j
  choose v hv he using hcolumns
  let W : Matrix n r K[X] := fun x j => v j x
  have hrows (x : n) : ∃ w : n → K[X], (∀ y, (w y).natDegree ≤ 1) ∧
      V.transpose *ᵥ w = W x := by
    apply weighted_coefficient_surjective_lift V.transpose (fun _ => 1)
      (fun j => a j + 1) (fun j y => Nat.add_le_add_right (hV y j) 1) hrow
    exact fun j => hv j x
  choose w hw hew using hrows
  let M : Matrix n n K[X] := fun x y => w x y
  have hMV : M * V = W := by
    funext x j
    have h := congrFun (hew x) j
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      mul_comm, M] using h
  refine ⟨M, fun x y => hw x y, ?_, ?_⟩
  · rw [Matrix.mul_assoc, hMV]
    funext x j
    exact congrFun (he j) (Sum.inl x)
  · rw [Matrix.mul_assoc, hMV]
    funext x j
    exact congrFun (he j) (Sum.inr x)

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
theorem depthTwo_affine_preimage_of_coefficient_surjective
    (P Q : Matrix m n K[X]) (hP : DegreeBound P 1) (hQ : DegreeBound Q 2)
    (hPsurj : Function.Surjective
      (weightedCoefficientMatrix P (fun _ => 1) (fun _ => 2)).mulVec) :
    ∃ M : Matrix n n K[X], DegreeBound M 1 ∧ P * M = Q := by
  have hcolumns (j : n) : ∃ v : n → K[X],
      (∀ x, (v x).natDegree ≤ 1) ∧ P *ᵥ v = fun i => Q i j := by
    apply weighted_coefficient_surjective_lift P (fun _ => 1) (fun _ => 2)
      (fun i x => by dsimp; have := hP i x; omega) hPsurj
    exact fun i => hQ i j
  choose v hv he using hcolumns
  refine ⟨fun x j => v j x, fun x j => hv j x, ?_⟩
  funext i j
  exact congrFun (he j) i

omit [Fintype r] [DecidableEq m] in
theorem depthTwo_terminal_of_factor (P Q : Matrix m n K[X])
    (M : Matrix n n K[X]) (V : Matrix n r K[X])
    (A D : Matrix m m K[X]) (hfactor : P * M = A * P + D * Q)
    (hzero : P * M * V = 0) :
    P * M ^ 2 * V = D * (Q * M * V) := by
  rw [pow_two, ← Matrix.mul_assoc P, hfactor, Matrix.add_mul, Matrix.add_mul]
  simp only [Matrix.mul_assoc] at hzero ⊢
  rw [hzero, Matrix.mul_zero, zero_add]

end FD56

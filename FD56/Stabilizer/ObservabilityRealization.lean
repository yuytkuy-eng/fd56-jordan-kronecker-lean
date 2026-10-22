/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ObservabilityMatrix
import FD56.Hilbert.WeightedSurjectivity

/-! An affine simultaneous preimage for each column realizes a polynomial
matrix family as successive observability blocks. The required surjectivity
is an explicit hypothesis; no generic rank assertion is made here. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K m n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- The first `q` blocks of a family with `q + 1` blocks. -/
def observabilityRealizationPrefix {q : ℕ}
    (R : Fin (q + 1) → Matrix m n K[X]) : Matrix (Fin q × m) n K[X] :=
  fun ij k => R ij.1.castSucc ij.2 k

/-- The affine input coefficient map for simultaneous multiplication by the
prefix. Block `i` has output degree bound `i + 2`. -/
def observabilityRealizationCoefficientMatrix {q : ℕ}
    (R : Fin (q + 1) → Matrix m n K[X]) :
    Matrix (Σ ij : Fin q × m, Fin (ij.1.val + 3)) (Σ _ : n, Fin 2) K :=
  weightedCoefficientMatrix (observabilityRealizationPrefix R)
    (fun _ => 1) (fun ij => ij.1.val + 2)

theorem matrix_family_eq_powers {q : ℕ}
    (R : Fin (q + 1) → Matrix m n K[X]) (M : Matrix n n K[X])
    (hstep : ∀ i : Fin q, R i.castSucc * M = R i.succ) :
    ∀ i, R i = R 0 * M ^ i.val := by
  have hp : ∀ k (hk : k < q + 1), R ⟨k, hk⟩ = R 0 * M ^ k := by
    intro k
    induction k with
    | zero =>
        intro hk
        simp
    | succ k ih =>
        intro hk
        have h : k < q := by omega
        calc
          R ⟨k + 1, hk⟩ = R (Fin.castSucc ⟨k, h⟩) * M := (hstep ⟨k, h⟩).symm
          _ = (R 0 * M ^ k) * M :=
            congrArg (fun A : Matrix m n K[X] => A * M) (ih (by omega))
          _ = R 0 * M ^ (k + 1) := by rw [pow_succ, Matrix.mul_assoc]
  intro i
  exact hp i.val i.isLt

theorem observabilityMatrix_eq_of_matrix_family_recurrence {q : ℕ}
    (R : Fin (q + 1) → Matrix m n K[X]) (M : Matrix n n K[X])
    (hstep : ∀ i : Fin q, R i.castSucc * M = R i.succ) :
    observabilityMatrix M (R 0) (q + 1) = fun ij k => R ij.1 ij.2 k := by
  funext ij k
  exact congrArg (fun A : Matrix m n K[X] => A ij.2 k)
    (matrix_family_eq_powers R M hstep ij.1).symm

/-- Realize the block recurrence by lifting the next block column by column. -/
theorem affine_observability_realization_of_preimages {q : ℕ}
    (R : Fin (q + 1) → Matrix m n K[X])
    (hR : ∀ i x j, (R i x j).natDegree ≤ i.val + 1)
    (hlift : ∀ w : Fin q → m → K[X],
      (∀ i x, (w i x).natDegree ≤ i.val + 2) →
      ∃ v : n → K[X], (∀ j, (v j).natDegree ≤ 1) ∧
        ∀ i, R i.castSucc *ᵥ v = w i) :
    ∃ M : Matrix n n K[X], DegreeBound M 1 ∧
      (∀ i : Fin q, R i.castSucc * M = R i.succ) ∧
      ∀ i, R i = R 0 * M ^ i.val := by
  have hcol (j : n) : ∃ v : n → K[X], (∀ x, (v x).natDegree ≤ 1) ∧
      ∀ i : Fin q, R i.castSucc *ᵥ v = fun x => R i.succ x j := by
    apply hlift (fun i x => R i.succ x j)
    intro i x
    simpa only [Fin.val_succ, Nat.add_assoc] using hR i.succ x j
  choose v hv he using hcol
  let M : Matrix n n K[X] := fun x j => v j x
  have hM : DegreeBound M 1 := fun x j => hv j x
  have hstep (i : Fin q) : R i.castSucc * M = R i.succ := by
    funext x j
    exact congrFun (he j i) x
  exact ⟨M, hM, hstep, matrix_family_eq_powers R M hstep⟩

/-- A concrete finite weighted coefficient map supplies the simultaneous
affine preimages needed for observability realization. -/
theorem affine_observability_realization_of_coefficient_surjective {q : ℕ}
    (R : Fin (q + 1) → Matrix m n K[X])
    (hR : ∀ i x j, (R i x j).natDegree ≤ i.val + 1)
    (hs : Function.Surjective (observabilityRealizationCoefficientMatrix R).mulVec) :
    ∃ M : Matrix n n K[X], DegreeBound M 1 ∧
      (∀ i : Fin q, R i.castSucc * M = R i.succ) ∧
      ∀ i, R i = R 0 * M ^ i.val := by
  apply affine_observability_realization_of_preimages R hR
  intro w hw
  have hprefix : ∀ ij j,
      (observabilityRealizationPrefix R ij j).natDegree + 1 ≤ ij.1.val + 2 := by
    intro ij j
    have h := hR ij.1.castSucc ij.2 j
    change (R ij.1.castSucc ij.2 j).natDegree + 1 ≤ ij.1.val + 2
    change (R ij.1.castSucc ij.2 j).natDegree ≤ ij.1.val + 1 at h
    omega
  obtain ⟨v, hv, he⟩ := weighted_coefficient_surjective_lift
    (observabilityRealizationPrefix R) (fun _ => 1) (fun ij => ij.1.val + 2)
    hprefix hs (fun ij => w ij.1 ij.2) (fun ij => hw ij.1 ij.2)
  refine ⟨v, hv, ?_⟩
  intro i
  funext x
  exact congrFun he (i, x)

end FD56

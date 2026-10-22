/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.RectangularBlocks
import FD56.Arithmetic.RectangularArithmetic

/-! A balanced rectangular pencil realizes maximal coefficient rank in every degree. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

def rectangularBlockLengths (n s : ℕ) : Fin (n % s) ⊕ Fin (s - n % s) → ℕ :=
  Sum.elim (fun _ => n / s + 1) (fun _ => n / s)

abbrev RectangularRows (n s : ℕ) :=
  Σ i, Fin (rectangularBlockLengths n s i)

abbrev RectangularColumns (n s : ℕ) :=
  Σ i, Fin (rectangularBlockLengths n s i + 1)

theorem rectangular_rows_card (n s : ℕ) (hs : 0 < s) :
    Fintype.card (RectangularRows n s) = n := by
  simpa [RectangularRows, Fintype.card_sigma, Fintype.sum_sum_type,
    rectangularBlockLengths] using (rectangular_balanced_rows n s hs).symm

theorem rectangular_columns_card (n s : ℕ) (hs : 0 < s) :
    Fintype.card (RectangularColumns n s) = n + s := by
  simpa [RectangularColumns, Fintype.card_sigma, Fintype.sum_sum_type,
    rectangularBlockLengths, Nat.add_assoc] using (rectangular_balanced_columns n s hs).symm

variable {K a b : Type*} [Field K] [Fintype a] [Fintype b]

def balancedRowEquiv (hab : Fintype.card a < Fintype.card b) :
    a ≃ RectangularRows (Fintype.card a) (Fintype.card b - Fintype.card a) :=
  Fintype.equivOfCardEq (by rw [rectangular_rows_card _ _ (by omega)])

def balancedColumnEquiv (hab : Fintype.card a < Fintype.card b) :
    b ≃ RectangularColumns (Fintype.card a) (Fintype.card b - Fintype.card a) :=
  Fintype.equivOfCardEq (by rw [rectangular_columns_card _ _ (by omega)]; omega)

def balancedRectangularWitness (hab : Fintype.card a < Fintype.card b) : Matrix a b K[X] :=
  (rectangularBlockPencil (rectangularBlockLengths (Fintype.card a)
    (Fintype.card b - Fintype.card a))).submatrix (balancedRowEquiv hab) (balancedColumnEquiv hab)

theorem balancedRectangularWitness_degree (hab : Fintype.card a < Fintype.card b) :
    DegreeBound (balancedRectangularWitness (K := K) hab) 1 := by
  intro i j
  exact rectangularBlockPencil_degree _ _ _

theorem balancedRectangularWitness_hilbert (hab : Fintype.card a < Fintype.card b) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (balancedRectangularWitness (K := K) hab) d) =
      (Fintype.card b - Fintype.card a) * (d + 1) - Fintype.card a := by
  classical
  rw [balancedRectangularWitness, reindex_kernel_hilbert, rectangularBlockPencil_kernel_hilbert]
  simpa [Fintype.sum_sum_type, rectangularBlockLengths] using
    rectangular_balanced_hilbert_sizes (Fintype.card a)
      (Fintype.card b - Fintype.card a) d (by omega)

theorem balancedRectangularWitness_coefficient_injective
    (hab : Fintype.card a < Fintype.card b) (d : ℕ)
    (hd : (Fintype.card b - Fintype.card a) * (d + 1) ≤ Fintype.card a) :
    Function.Injective (polynomialCoefficientMatrix (balancedRectangularWitness (K := K) hab) d).mulVec := by
  classical
  apply coefficient_injective_of_kernel_finrank_zero _ d (balancedRectangularWitness_degree hab)
  rw [balancedRectangularWitness_hilbert hab d, Nat.sub_eq_zero_of_le hd]

theorem balancedRectangularWitness_coefficient_surjective
    (hab : Fintype.card a < Fintype.card b) (d : ℕ)
    (hd : Fintype.card a ≤ (Fintype.card b - Fintype.card a) * (d + 1)) :
    Function.Surjective (polynomialCoefficientMatrix (balancedRectangularWitness (K := K) hab) d).mulVec := by
  classical
  apply coefficient_surjective_of_kernel_finrank _ d (balancedRectangularWitness_degree hab)
  rw [balancedRectangularWitness_hilbert hab d]
  have he := Nat.sub_add_cancel hd
  have hs : Fintype.card b = Fintype.card a + (Fintype.card b - Fintype.card a) := by omega
  nlinarith

end FD56

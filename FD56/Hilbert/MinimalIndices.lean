/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.Basis
import FD56.Hilbert.HilbertRecovery
import FD56.Stabilizer.GenericRectangular

/-! Hilbert functions determine the degree multiset of a reduced polynomial
kernel basis. For generic rectangular rows, that multiset is balanced. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem listHilbert_nat (xs : List ℕ) (d : ℕ) :
    listHilbert xs d = ((xs.map (fun e => d + 1 - e)).sum : ℕ) := by
  induction xs with
  | nil => simp [listHilbert]
  | cons e xs ih =>
    simp only [listHilbert, List.map_cons, List.sum_cons, Nat.cast_add] at ih ⊢
    rw [ih]
    congr 1
    omega

theorem listHilbert_ofFn {r : ℕ} (e : Fin r → ℕ) (d : ℕ) :
    listHilbert (List.ofFn e) d = ((∑ j, (d + 1 - e j) : ℕ) : ℤ) := by
  rw [listHilbert_nat, List.map_ofFn, List.sum_ofFn]
  rfl

theorem finite_profile_determines_indices {r s : ℕ} (e : Fin r → ℕ) (f : Fin s → ℕ)
    (h : ∀ d : ℕ, (∑ j, (d + 1 - e j)) = ∑ j, (d + 1 - f j)) :
    (List.ofFn e).Perm (List.ofFn f) := by
  apply listHilbert_determines_indices
  intro d
  rw [listHilbert_ofFn, listHilbert_ofFn, h d]

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_rows_reduced_basis_degrees
    (hmn : Fintype.card m < Fintype.card n) (r : ℕ)
    (B : Basis (Fin r) (Polynomial (AffineCoefficientField K (MatrixParameters n m)))
      (LinearMap.ker (Matrix.toLin' (genericAffineRows K n m))))
    (e : Fin r → ℕ)
    (hZ : ∀ i j, (polynomialKernelBasisMatrix (genericAffineRows K n m) B i j).natDegree ≤ e j)
    (hlead : Function.Injective (Matrix.mulVec (fun i j =>
      (polynomialKernelBasisMatrix (genericAffineRows K n m) B i j).coeff (e j)))) :
    (List.ofFn e).Perm
      (List.replicate (Fintype.card m % (Fintype.card n - Fintype.card m))
        (Fintype.card m / (Fintype.card n - Fintype.card m) + 1) ++
      List.replicate ((Fintype.card n - Fintype.card m) -
        Fintype.card m % (Fintype.card n - Fintype.card m))
        (Fintype.card m / (Fintype.card n - Fintype.card m))) := by
  apply listHilbert_determines_indices
  intro d
  rw [listHilbert_ofFn, listHilbert_nat]
  simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
    smul_eq_mul]
  have hh := polynomial_kernel_basis_hilbert (genericAffineRows K n m) B e d hZ hlead
  rw [generic_rows_kernel_hilbert hmn d] at hh
  have hb := rectangular_balanced_hilbert_sizes (Fintype.card m)
    (Fintype.card n - Fintype.card m) d (by omega)
  exact_mod_cast hh.symm.trans hb.symm

end FD56

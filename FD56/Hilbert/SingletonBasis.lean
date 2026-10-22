/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericMinimal

/-! A singleton minimal degree list gives a normalized one-column kernel basis. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K a b : Type*} [Field K] [Fintype b] [DecidableEq b]

theorem singleton_minimal_kernel_basis (A : Matrix a b K[X]) (e : ℕ)
    (h : HasMinimalKernelDegrees A [e]) :
    ∃ B : Basis (Fin 1) K[X] (LinearMap.ker (Matrix.toLin' A)),
      (∀ i j, (polynomialKernelBasisMatrix A B i j).natDegree ≤ e) ∧
      Function.Injective (Matrix.mulVec
        (show Matrix b (Fin 1) K from fun i j => (polynomialKernelBasisMatrix A B i j).coeff e)) := by
  obtain ⟨r, B, f, hB, hL, hp⟩ := h
  have hr : r = 1 := by simpa using hp.length_eq
  subst r
  have hf : ∀ j, f j = e := by
    intro j
    have hj : f j ∈ List.ofFn f := List.mem_ofFn.mpr ⟨j, rfl⟩
    have hl : List.ofFn f = [e] := List.perm_singleton.mp hp
    rw [hl] at hj
    exact List.mem_singleton.mp hj
  refine ⟨B, ?_, ?_⟩
  · simpa only [hf] using hB
  · simpa only [hf] using hL

theorem generic_one_more_column_kernel_basis
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (hnm : Fintype.card n = Fintype.card m + 1) :
    ∃ B : Basis (Fin 1) (Polynomial (AffineCoefficientField K (MatrixParameters n m)))
      (LinearMap.ker (Matrix.toLin' (genericAffineRows K n m))),
      (∀ i j, (polynomialKernelBasisMatrix (genericAffineRows K n m) B i j).natDegree ≤
        Fintype.card m) ∧
      Function.Injective (Matrix.mulVec (show Matrix n (Fin 1)
        (AffineCoefficientField K (MatrixParameters n m)) from fun i j =>
          (polynomialKernelBasisMatrix (genericAffineRows K n m) B i j).coeff (Fintype.card m))) := by
  apply singleton_minimal_kernel_basis
  have h := generic_rows_minimal_degrees (K := K) (n := n) (m := m) (by omega)
  simpa [balancedDegreeList, hnm, Nat.mod_one] using h

end FD56

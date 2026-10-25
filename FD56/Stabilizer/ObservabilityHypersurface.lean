/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericDimension
import FD56.LinearAlgebra.PrincipalQuotientField
import FD56.LinearAlgebra.FullKrylovBound
import FD56.LinearAlgebra.MatrixGeneratorObstructions

/-! Dimension obstructions for observability on a principal hypersurface. -/

noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
namespace FD56
open Matrix
variable {K n m : Type*} [Field K] [Fintype n] [DecidableEq n] [Fintype m]

def quotientStateMatrix (g : MvPolynomial (MatrixParameters n m) K) :
    Matrix n n (PrincipalQuotientField g) :=
  (universalSquare K n m).map (principalQuotientFieldMap g).toRingHom

def quotientOutputMatrix (g : MvPolynomial (MatrixParameters n m) K) :
    Matrix m n (PrincipalQuotientField g) :=
  (universalRows K n m).map (principalQuotientFieldMap g).toRingHom

omit [Fintype n] [DecidableEq n] [Fintype m] in
theorem quotient_matrix_entries_generate (g : MvPolynomial (MatrixParameters n m) K)
    [(Ideal.span ({g} : Set (MvPolynomial (MatrixParameters n m) K))).IsPrime] :
    IntermediateField.adjoin K (Set.range
      (matrixEntryGenerators (quotientStateMatrix g) (quotientOutputMatrix g))) = ⊤ := by
  have he : matrixEntryGenerators (quotientStateMatrix g) (quotientOutputMatrix g) =
      fun i => principalQuotientFieldMap g (MvPolynomial.X i) := by
    funext i
    cases i <;> rfl
  rw [he]
  exact principal_quotient_field_coordinates_generate g

theorem quotient_observability_krylov_dependent
    (g : MvPolynomial (MatrixParameters n m) K)
    [(Ideal.span ({g} : Set (MvPolynomial (MatrixParameters n m) K))).IsPrime]
    (hg : g ≠ 0) (hu : ¬IsUnit g) (q : ℕ)
    (hn : Fintype.card n < q * Fintype.card m)
    (v : n → PrincipalQuotientField g) (c : n) (hv : v c = 1)
    (hker : ∀ j : Fin q,
      quotientOutputMatrix g *ᵥ (quotientStateMatrix g ^ j.val *ᵥ v) = 0) :
    ¬ LinearIndependent (PrincipalQuotientField g)
      (fun j : Fin q => quotientStateMatrix g ^ j.val *ᵥ v) := by
  classical
  intro hlin
  obtain ⟨i, hi⟩ := principal_quotient_field_remaining_coordinates_independent g hg hu
  have hb := card_algebraicIndependent_le_fullKrylov_bound hi
    (quotientStateMatrix g) (quotientOutputMatrix g) v c hv hlin hker
    (quotient_matrix_entries_generate g)
  have hc : Fintype.card {j : MatrixParameters n m // j ≠ i} =
      Fintype.card n ^ 2 + Fintype.card m * Fintype.card n - 1 := by
    simp [MatrixParameters, Fintype.card_subtype_compl, pow_two]
  rw [hc] at hb
  have hqn : q ≤ Fintype.card n := by
    simpa using hlin.fintype_card_le_finrank
  have hp : 0 < Fintype.card n := Fintype.card_pos_iff.mpr ⟨c⟩
  have hs := Nat.sub_add_cancel hqn
  have hbig : 0 < Fintype.card n ^ 2 + Fintype.card m * Fintype.card n := by
    nlinarith
  have hb' : Fintype.card n ^ 2 + Fintype.card m * Fintype.card n ≤
      Fintype.card n ^ 2 + Fintype.card n + Fintype.card m * (Fintype.card n - q) := by
    omega
  nlinarith

theorem quotient_no_invariant_output_kernel
    (g : MvPolynomial (MatrixParameters n m) K)
    [(Ideal.span ({g} : Set (MvPolynomial (MatrixParameters n m) K))).IsPrime]
    (hg : g ≠ 0) (hu : ¬IsUnit g) (hm : 2 ≤ Fintype.card m)
    (W : Submodule (PrincipalQuotientField g) (n → PrincipalQuotientField g))
    (hW : W ≠ ⊥)
    (hinv : ∀ w ∈ W, quotientStateMatrix g *ᵥ w ∈ W)
    (hker : ∀ w ∈ W, quotientOutputMatrix g *ᵥ w = 0) : False := by
  classical
  obtain ⟨i, hi⟩ := principal_quotient_field_remaining_coordinates_independent g hg hu
  apply no_invariant_output_kernel_of_large_independent_family hi ?_ hm
    (quotientStateMatrix g) (quotientOutputMatrix g) (quotient_matrix_entries_generate g)
    W hW hinv hker
  simp [MatrixParameters, Fintype.card_subtype_compl, pow_two]
end FD56


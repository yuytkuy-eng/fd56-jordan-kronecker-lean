/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.OutputVariableChange
import FD56.LinearAlgebra.MaximalMinorColumnOperations
import FD56.Stabilizer.DiagonalObservabilityMinors

/-! Wide maximal minors for a constant matrix with distinct diagonal eigenvalues. -/

noncomputable section
namespace FD56
open Matrix MvPolynomial
open scoped BigOperators

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

omit [Fintype m] [DecidableEq m] in
theorem observabilityMatrix_intertwine {R : Type*} [CommRing R]
    (M D S : Matrix n n R) (P : Matrix m n R) (q : ℕ) (hMS : M*S = S*D) :
    observabilityMatrix M P q * S = observabilityMatrix D (P*S) q := by
  have hp : ∀ k : ℕ, M^k*S = S*D^k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ',Matrix.mul_assoc,ih,← Matrix.mul_assoc,hMS,Matrix.mul_assoc,← pow_succ']
  ext ij j
  change ((P * M^ij.1.val)*S) ij.2 j = ((P*S)*D^ij.1.val) ij.2 j
  rw [Matrix.mul_assoc,hp,Matrix.mul_assoc]

theorem diagonalizable_wide_observability_common_divisor_isUnit
    (M S T : Matrix n n K) (hST : S*T = 1) (hTS : T*S = 1)
    (ev : n → K) (hev : Function.Injective ev) (hMS : M*S = S*(Matrix.diagonal ev))
    (q : ℕ) (hn : q*Fintype.card m < Fintype.card n)
    (d : MvPolynomial (m × n) K)
    (hd : ∀ r : (Fin q × m) → n,
      d ∣ ((observabilityMatrix (M.map MvPolynomial.C)
        (Matrix.of fun a j => MvPolynomial.X (a,j)) q).submatrix id r).det) : IsUnit d := by
  let P : Matrix m n (MvPolynomial (m × n) K) := Matrix.of fun a j => MvPolynomial.X (a,j)
  let D : Matrix n n (MvPolynomial (m × n) K) := (Matrix.diagonal ev).map MvPolynomial.C
  let e := outputVariableChange (m := m) S T hST hTS
  have heD : D.map e.toRingHom = D := by
    funext i j
    exact outputVariableChangeHom_C S _
  have heP : P.map e.toRingHom = P * S.map MvPolynomial.C := outputVariableChangeHom_rows S
  have hc : M.map MvPolynomial.C * S.map MvPolynomial.C = S.map MvPolynomial.C * D := by
    simpa only [D,← Matrix.map_mul] using congrArg (fun A => A.map MvPolynomial.C) hMS
  have heO : (observabilityMatrix D P q).map e.toRingHom =
      observabilityMatrix (M.map MvPolynomial.C) P q * S.map MvPolynomial.C := by
    rw [observabilityMatrix_map,heD,heP]
    exact (observabilityMatrix_intertwine _ _ _ _ q hc).symm
  have hd' := maximal_column_minors_dvd_mul_right
    (observabilityMatrix (M.map MvPolynomial.C) P q) (S.map MvPolynomial.C) d hd
  have hu : IsUnit (e.symm d) := by
    apply diagonal_generic_observability_common_divisor_isUnit ev hev q hn
    intro r
    have hh := map_dvd e.symm.toRingHom (hd' r)
    rw [← heO] at hh
    have heq : e.symm (((observabilityMatrix D P q).map e.toRingHom).submatrix id r).det =
        ((diagonalGenericObservability ev q).submatrix id r).det := by
      have hmap : ((observabilityMatrix D P q).map e.toRingHom).submatrix id r =
          ((observabilityMatrix D P q).submatrix id r).map e.toRingHom := rfl
      have hdet : e (((observabilityMatrix D P q).submatrix id r).det) =
          (((observabilityMatrix D P q).submatrix id r).map e.toRingHom).det := e.toRingHom.map_det _
      rw [hmap,← hdet]
      simp only [RingEquiv.coe_toRingHom,RingEquiv.symm_apply_apply]
      congr 1
      rw [diagonalGenericObservability_eq]
      funext i j
      simp [D,Matrix.diagonal_apply]
      rfl
    change e.symm d ∣ e.symm (((observabilityMatrix D P q).map e.toRingHom).submatrix id r).det at hh
    rwa [heq] at hh
  have hh := hu.map e.toRingHom
  change IsUnit (e (e.symm d)) at hh
  simpa only [RingEquiv.apply_symm_apply] using hh

end FD56

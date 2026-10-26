/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.CyclicObservabilitySpecialization
import FD56.Stabilizer.GenericDimension

/-! Universal wide observability minors have no nonunit divisor in the state variables alone. -/

noncomputable section
namespace FD56
open Matrix
variable {K : Type*} [Field K] {n m : ℕ}

def universalOutputSubstitution
    (P : Matrix (Fin m) (Fin (n+1)) (MvPolynomial (Fin (n+1) × Fin (n+1)) K)) :
    MvPolynomial (MatrixParameters (Fin (n+1)) (Fin m)) K →+*
      MvPolynomial (Fin (n+1) × Fin (n+1)) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Sum.elim MvPolynomial.X (fun ij => P ij.1 ij.2))

theorem universalOutputSubstitution_state
    (P : Matrix (Fin m) (Fin (n+1)) (MvPolynomial (Fin (n+1) × Fin (n+1)) K))
    (p : MvPolynomial (Fin (n+1) × Fin (n+1)) K) :
    universalOutputSubstitution P (MvPolynomial.rename Sum.inl p) = p := by
  have h : (universalOutputSubstitution P).comp
      (MvPolynomial.rename (Sum.inl : (Fin (n+1) × Fin (n+1)) →
        MatrixParameters (Fin (n+1)) (Fin m))).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [universalOutputSubstitution]
    · intro i; simp [universalOutputSubstitution]
  exact RingHom.congr_fun h p

theorem universalOutputSubstitution_pair
    (P : Matrix (Fin m) (Fin (n+1)) (MvPolynomial (Fin (n+1) × Fin (n+1)) K)) :
    (universalSquare K (Fin (n+1)) (Fin m)).map (universalOutputSubstitution P) =
      cyclicVariableMatrix id ∧
    (universalRows K (Fin (n+1)) (Fin m)).map (universalOutputSubstitution P) = P := by
  constructor <;> funext i j <;>
    simp [Matrix.map_apply,universalOutputSubstitution,universalSquare,universalRows,
      cyclicVariableMatrix]

theorem universal_observability_state_divisor_isUnit (q : ℕ) (h : q*m ≤ n+1)
    (d : MvPolynomial (Fin (n+1) × Fin (n+1)) K)
    (hd : ∀ r : Fin q × Fin m → Fin (n+1),
      MvPolynomial.rename Sum.inl d ∣
        ((observabilityMatrix (universalSquare K (Fin (n+1)) (Fin m))
          (universalRows K (Fin (n+1)) (Fin m)) q).submatrix id r).det) : IsUnit d := by
  apply universal_state_common_divisor_isUnit q m h d
  intro P r
  have hh := map_dvd (universalOutputSubstitution P) (hd r)
  rw [universalOutputSubstitution_state,RingHom.map_det] at hh
  have hp := universalOutputSubstitution_pair P
  have he : (((observabilityMatrix (universalSquare K (Fin (n+1)) (Fin m))
      (universalRows K (Fin (n+1)) (Fin m)) q).submatrix id r).map
      (universalOutputSubstitution P)) =
      (observabilityMatrix (cyclicVariableMatrix id) P q).submatrix id r := by
    rw [← Matrix.submatrix_map,observabilityMatrix_map,hp.1,hp.2]
  change _ ∣ (((observabilityMatrix (universalSquare K (Fin (n+1)) (Fin m))
    (universalRows K (Fin (n+1)) (Fin m)) q).submatrix id r).map
    (universalOutputSubstitution P)).det at hh
  rwa [he] at hh

end FD56

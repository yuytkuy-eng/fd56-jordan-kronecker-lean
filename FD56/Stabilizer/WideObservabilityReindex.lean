/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericWideObservabilityCoprime
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Wide observability coprimality is independent of the finite coordinate types. -/

noncomputable section
namespace FD56
open Matrix
variable {K n m n' m' : Type*} [Field K]
  [Fintype n] [Fintype m] [Fintype n'] [Fintype m']
  [DecidableEq n] [DecidableEq m] [DecidableEq n'] [DecidableEq m']

omit [Fintype m] [Fintype m'] [DecidableEq m] [DecidableEq m'] in
theorem observabilityMatrix_submatrix_equiv {R : Type*} [CommRing R]
    (M : Matrix n n R) (P : Matrix m n R) (q : ℕ) (en : n' ≃ n) (em : m' ≃ m) :
    observabilityMatrix (M.submatrix en en) (P.submatrix em en) q =
      (observabilityMatrix M P q).submatrix ((Equiv.refl (Fin q)).prodCongr em) en := by
  have hp (k : ℕ) : (M.submatrix en en)^k = (M^k).submatrix en en := by
    exact (map_pow (Matrix.reindexAlgEquiv R R en.symm) M k).symm
  funext ij j
  change ((P.submatrix em en)*(M.submatrix en en)^ij.1.val) ij.2 j = _
  rw [hp,Matrix.submatrix_mul_equiv]
  rfl

theorem universal_wide_observability_coprime_fin {a b : ℕ} (q : ℕ) (h : q*b < a)
    (g : MvPolynomial (MatrixParameters (Fin a) (Fin b)) K)
    (hd : ∀ r : Fin q × Fin b → Fin a,
      g ∣ ((observabilityMatrix (universalSquare K (Fin a) (Fin b))
        (universalRows K (Fin a) (Fin b)) q).submatrix id r).det) : IsUnit g := by
  cases a with
  | zero => omega
  | succ a => exact universal_wide_observability_common_divisor_isUnit q h g hd

theorem universal_wide_observability_coprime (q : ℕ)
    (hn : q*Fintype.card m < Fintype.card n)
    (g : MvPolynomial (MatrixParameters n m) K)
    (hd : ∀ r : Fin q × m → n,
      g ∣ ((observabilityMatrix (universalSquare K n m) (universalRows K n m) q).submatrix id r).det) :
    IsUnit g := by
  classical
  let en := Fintype.equivFin n
  let em := Fintype.equivFin m
  let er := (Equiv.refl (Fin q)).prodCongr em
  let ep := Equiv.sumCongr (en.prodCongr en) (em.prodCongr en)
  let e := MvPolynomial.renameEquiv K ep
  have hM : (universalSquare K n m).map e.toRingHom =
      (universalSquare K (Fin (Fintype.card n)) (Fin (Fintype.card m))).submatrix en en := by
    funext i j
    simp [universalSquare,e,ep,MvPolynomial.renameEquiv]
  have hP : (universalRows K n m).map e.toRingHom =
      (universalRows K (Fin (Fintype.card n)) (Fin (Fintype.card m))).submatrix em en := by
    funext i j
    simp [universalRows,e,ep,MvPolynomial.renameEquiv]
  have hO : (observabilityMatrix (universalSquare K n m) (universalRows K n m) q).map e.toRingHom =
      (observabilityMatrix (universalSquare K (Fin (Fintype.card n)) (Fin (Fintype.card m)))
        (universalRows K (Fin (Fintype.card n)) (Fin (Fintype.card m))) q).submatrix er en := by
    rw [observabilityMatrix_map,hM,hP,observabilityMatrix_submatrix_equiv]
  have hu : IsUnit (e g) := by
    apply universal_wide_observability_coprime_fin q hn
    intro r
    let r' : Fin q × m → n := fun i => en.symm (r (er i))
    have hh := map_dvd e.toRingHom (hd r')
    have heq : e (((observabilityMatrix (universalSquare K n m) (universalRows K n m) q).submatrix id r').det) =
        ((observabilityMatrix (universalSquare K (Fin (Fintype.card n)) (Fin (Fintype.card m)))
          (universalRows K (Fin (Fintype.card n)) (Fin (Fintype.card m))) q).submatrix id r).det := by
      change e.toRingHom (((observabilityMatrix (universalSquare K n m) (universalRows K n m) q).submatrix id r').det) = _
      rw [e.toRingHom.map_det]
      change (((observabilityMatrix (universalSquare K n m) (universalRows K n m) q).submatrix id r').map e.toRingHom).det = _
      rw [← Matrix.submatrix_map,hO]
      have he : ((observabilityMatrix (universalSquare K (Fin (Fintype.card n)) (Fin (Fintype.card m)))
          (universalRows K (Fin (Fintype.card n)) (Fin (Fintype.card m))) q).submatrix er en).submatrix id r' =
          ((observabilityMatrix (universalSquare K (Fin (Fintype.card n)) (Fin (Fintype.card m)))
          (universalRows K (Fin (Fintype.card n)) (Fin (Fintype.card m))) q).submatrix id r).submatrix er er := by
        funext i j
        simp [Matrix.submatrix_apply,r']
      rw [he,Matrix.det_submatrix_equiv_self]
    change e g ∣ e _ at hh
    rwa [heq] at hh
  have hh := hu.map e.symm.toRingHom
  change IsUnit (e.symm (e g)) at hh
  simpa using hh

end FD56

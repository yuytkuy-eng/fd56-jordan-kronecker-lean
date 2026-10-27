/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLCompanionDeterminant
import FD56.Stabilizer.GLRectangularBasisChange
import FD56.Stabilizer.ObservabilityMatrix

/-! An invertible square observability stack computes the actual GL determinant. -/

noncomputable section
namespace FD56
open Matrix

variable {R m : Type*} [CommRing R] [Fintype m] [DecidableEq m]

theorem observability_coordinates_first_row (q : ℕ)
    (M : Matrix (Fin (q+1) × m) (Fin (q+1) × m) R)
    (P : Matrix m (Fin (q+1) × m) R)
    (S : Matrix (Fin (q+1) × m) (Fin (q+1) × m) R)
    (hOS : observabilityMatrix M P (q+1)*S=1) : P*S=blockFirstRow q := by
  funext a ⟨j,b⟩
  have h := congrFun (congrFun hOS (0,a)) (j,b)
  change (∑ k, observabilityMatrix M P (q+1) (0,a) k*S k (j,b))=_ at h
  simpa [observabilityMatrix,Matrix.mul_apply,Matrix.one_apply,blockFirstRow,Prod.mk.injEq,
    ite_and,eq_comm] using h

theorem observability_coordinates_companion (q : ℕ)
    (M : Matrix (Fin (q+1) × m) (Fin (q+1) × m) R)
    (P : Matrix m (Fin (q+1) × m) R)
    (S : Matrix (Fin (q+1) × m) (Fin (q+1) × m) R)
    (hOS : observabilityMatrix M P (q+1)*S=1)
    (i : Fin q) (a : m) (k : Fin (q+1)) (b : m) :
    (observabilityMatrix M P (q+1)*M*S) (i.castSucc,a) (k,b)=
      if k=i.succ then (1 : Matrix m m R) a b else 0 := by
  let O := observabilityMatrix M P (q+1)
  have hshift (j : Fin (q+1) × m) : (O*M) (i.castSucc,a) j=O (i.succ,a) j := by
    change ((P*M^i.val)*M) a j=(P*M^(i.val+1)) a j
    rw [pow_succ,Matrix.mul_assoc]
  calc
    _ = (O*S) (i.succ,a) (k,b) := by
      change (∑ j, (O*M) (i.castSucc,a) j*S j (k,b))=∑ j, O (i.succ,a) j*S j (k,b)
      simp_rw [hshift]
    _ = _ := by
      change (observabilityMatrix M P (q+1)*S) (i.succ,a) (k,b)=_
      rw [hOS]
      simp [Matrix.one_apply,Prod.mk.injEq,ite_and,eq_comm]

theorem glKirillovMatrix_det_observability_inverse (q : ℕ)
    (M : Matrix (Fin (q+1) × m) (Fin (q+1) × m) R)
    (P : Matrix m (Fin (q+1) × m) R)
    (S : Matrix (Fin (q+1) × m) (Fin (q+1) × m) R)
    (hOS : observabilityMatrix M P (q+1)*S=1)
    (hSO : S*observabilityMatrix M P (q+1)=1) :
    (glKirillovMatrix M P).det=(observabilityMatrix M P (q+1)).det^(2*Fintype.card m) := by
  let O := observabilityMatrix M P (q+1)
  have hnorm : (glKirillovMatrix (O*M*S) (P*S)).det=1 := by
    rw [observability_coordinates_first_row q M P S hOS]
    exact glKirillovMatrix_companion_det q _ (observability_coordinates_companion q M P S hOS)
  have hcov := glKirillovMatrix_det_basis_change S O M (1 : Matrix m m R) P hSO hOS
  simp only [Matrix.one_mul,Matrix.det_one,one_pow,mul_one] at hcov
  have hds : O.det*S.det=1 := by rw [← Matrix.det_mul,hOS,Matrix.det_one]
  calc
    (glKirillovMatrix M P).det=(O.det^Fintype.card m*S.det^Fintype.card m)^2*
        (glKirillovMatrix M P).det := by rw [← mul_pow,hds,one_pow,one_pow,one_mul]
    _ = (O.det^Fintype.card m)^2*((S.det^Fintype.card m)^2*(glKirillovMatrix M P).det) := by ring
    _ = (O.det^Fintype.card m)^2 := by rw [← hcov,hnorm,mul_one]
    _ = _ := by rw [← pow_mul]; congr 1; omega

theorem glKirillovMatrix_det_observability_isUnit (q : ℕ)
    (M : Matrix (Fin (q+1) × m) (Fin (q+1) × m) R)
    (P : Matrix m (Fin (q+1) × m) R)
    (hO : IsUnit (observabilityMatrix M P (q+1)).det) :
    (glKirillovMatrix M P).det=(observabilityMatrix M P (q+1)).det^(2*Fintype.card m) :=
  glKirillovMatrix_det_observability_inverse q M P _
    (Matrix.mul_nonsing_inv _ hO) (Matrix.nonsing_inv_mul _ hO)

theorem glKirillovMatrix_det_observability_of_map {E : Type*} [CommRing E]
    (phi : R →+* E) (hphi : Function.Injective phi) (q : ℕ)
    (M : Matrix (Fin (q+1) × m) (Fin (q+1) × m) R)
    (P : Matrix m (Fin (q+1) × m) R)
    (hO : IsUnit (observabilityMatrix (M.map phi) (P.map phi) (q+1)).det) :
    (glKirillovMatrix M P).det=(observabilityMatrix M P (q+1)).det^(2*Fintype.card m) := by
  have hmap : (glKirillovMatrix M P).map phi=glKirillovMatrix (M.map phi) (P.map phi) := by
    simp only [glKirillovMatrix,← Matrix.submatrix_map,glEquationMatrix_map]
  apply hphi
  rw [map_pow,RingHom.map_det,RingHom.map_det]
  change ((glKirillovMatrix M P).map phi).det=
    ((observabilityMatrix M P (q+1)).map phi).det^(2*Fintype.card m)
  rw [hmap,observabilityMatrix_map]
  exact glKirillovMatrix_det_observability_isUnit q _ _ hO

theorem glKirillovMatrix_det_observability_ne_zero [IsDomain R] (q : ℕ)
    (M : Matrix (Fin (q+1) × m) (Fin (q+1) × m) R)
    (P : Matrix m (Fin (q+1) × m) R)
    (hO : (observabilityMatrix M P (q+1)).det≠0) :
    (glKirillovMatrix M P).det=(observabilityMatrix M P (q+1)).det^(2*Fintype.card m) := by
  let phi := algebraMap R (FractionRing R)
  apply glKirillovMatrix_det_observability_of_map phi (IsFractionRing.injective _ _) q M P
  apply isUnit_iff_ne_zero.mpr
  rw [← observabilityMatrix_map]
  change (phi.mapMatrix (observabilityMatrix M P (q+1))).det≠0
  rw [← RingHom.map_det]
  exact fun h => hO ((IsFractionRing.injective R (FractionRing R)) (h.trans (map_zero phi).symm))

end FD56

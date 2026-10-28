/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.TwoColumnUniversalFrame

/-! Coefficient evaluation realizes every pair within the prescribed column
degree bounds, using an algebra hom on the original polynomial ring. -/

noncomputable section
namespace FD56
open Polynomial

variable {K L n : Type*} [Field K] [Field L] [Algebra K L]

def twoColumnCoefficientEvaluation (a b : ℕ) (u v : n → L[X]) :
    TwoColumnCoefficientRing K n a b →ₐ[K] L :=
  MvPolynomial.aeval (Sum.elim (fun ik => (u ik.1).coeff ik.2.val)
    (fun ik => (v ik.1).coeff ik.2.val))

theorem twoColumnCoefficientEvaluation_U (a b : ℕ) (u v : n → L[X])
    (hu : ∀ i, (u i).natDegree≤a) (i : n) :
    (twoColumnUniversalU K n a b i).map
      (twoColumnCoefficientEvaluation (K:=K) a b u v).toRingHom=u i := by
  apply Polynomial.ext
  intro k
  by_cases hk : k≤a
  · rw [coeff_map,twoColumnUniversalU_coeff K n a b i ⟨k,by omega⟩]
    simp [twoColumnCoefficientEvaluation]
  · have hleft : ((twoColumnUniversalU K n a b i).map
        (twoColumnCoefficientEvaluation (K:=K) a b u v).toRingHom).natDegree≤a :=
      natDegree_map_le.trans (twoColumnUniversalU_degree K n a b i)
    rw [coeff_eq_zero_of_natDegree_lt (hleft.trans_lt (by omega)),
      coeff_eq_zero_of_natDegree_lt ((hu i).trans_lt (by omega))]

theorem twoColumnCoefficientEvaluation_V (a b : ℕ) (u v : n → L[X])
    (hv : ∀ i, (v i).natDegree≤b) (i : n) :
    (twoColumnUniversalV K n a b i).map
      (twoColumnCoefficientEvaluation (K:=K) a b u v).toRingHom=v i := by
  apply Polynomial.ext
  intro k
  by_cases hk : k≤b
  · rw [coeff_map,twoColumnUniversalV_coeff K n a b i ⟨k,by omega⟩]
    simp [twoColumnCoefficientEvaluation]
  · have hleft : ((twoColumnUniversalV K n a b i).map
        (twoColumnCoefficientEvaluation (K:=K) a b u v).toRingHom).natDegree≤b :=
      natDegree_map_le.trans (twoColumnUniversalV_degree K n a b i)
    rw [coeff_eq_zero_of_natDegree_lt (hleft.trans_lt (by omega)),
      coeff_eq_zero_of_natDegree_lt ((hv i).trans_lt (by omega))]

theorem twoColumnCoefficientEvaluation_minor (a b : ℕ) (u v : n → L[X])
    (hu : ∀ i, (u i).natDegree≤a) (hv : ∀ i, (v i).natDegree≤b) (i j : n) :
    (twoColumnUniversalU K n a b i*twoColumnUniversalV K n a b j-
      twoColumnUniversalU K n a b j*twoColumnUniversalV K n a b i).map
      (twoColumnCoefficientEvaluation (K:=K) a b u v).toRingHom=u i*v j-u j*v i := by
  rw [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_mul,
    twoColumnCoefficientEvaluation_U a b u v hu i,twoColumnCoefficientEvaluation_U a b u v hu j,
    twoColumnCoefficientEvaluation_V a b u v hv i,twoColumnCoefficientEvaluation_V a b u v hv j]

theorem twoColumnCoefficientEvaluation_minor_coeff (a b : ℕ) (u v : n → L[X])
    (hu : ∀ i, (u i).natDegree≤a) (hv : ∀ i, (v i).natDegree≤b) (i j : n) (k : ℕ) :
    twoColumnCoefficientEvaluation (K:=K) a b u v
      ((twoColumnUniversalU K n a b i*twoColumnUniversalV K n a b j-
        twoColumnUniversalU K n a b j*twoColumnUniversalV K n a b i).coeff k)=
      (u i*v j-u j*v i).coeff k := by
  have h := congrArg (fun p : L[X] => p.coeff k)
    (twoColumnCoefficientEvaluation_minor (K:=K) a b u v hu hv i j)
  simpa only [coeff_map] using h

end FD56

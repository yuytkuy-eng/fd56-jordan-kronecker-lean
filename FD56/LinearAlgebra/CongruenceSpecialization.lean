/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.ClearDenominators

/-! Simultaneous fraction-field congruences specialize away from one denominator. -/

noncomputable section
namespace FD56
open Matrix

private theorem map_scalar_matrix {R S a : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (d : R) (A : Matrix a a R) :
    (d • A).map φ = φ d • A.map φ := by
  ext i j
  exact map_mul φ d (A i j)

variable {R F n b ι : Type*} [CommRing R] [IsDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F]
  [Fintype n] [Fintype b] [DecidableEq n] [DecidableEq b]

theorem simultaneous_congruence_clear_denominators
    (A : ι → Matrix n n R) (J : ι → Matrix b b R)
    (T : Matrix n b F) (S : Matrix b n F)
    (hTS : T*S=1) (hST : S*T=1)
    (hform : ∀ i, T.transpose * (A i).map (algebraMap R F) * T =
      (J i).map (algebraMap R F)) :
    ∃ (d : R) (U : Matrix n b R) (V : Matrix b n R),
      d ≠ 0 ∧ U*V=d^2 • 1 ∧ V*U=d^2 • 1 ∧
      ∀ i, U.transpose * A i * U = d^2 • J i := by
  let z : (n × b) ⊕ (b × n) → F := Sum.elim (fun ij => T ij.1 ij.2) (fun ij => S ij.1 ij.2)
  obtain ⟨d,w,hd,hw⟩ := vector_clear_denominators (R := R) z
  let U : Matrix n b R := fun i j => w (Sum.inl (i,j))
  let V : Matrix b n R := fun i j => w (Sum.inr (i,j))
  have hU : U.map (algebraMap R F) = algebraMap R F d • T := by
    ext i j
    exact hw (Sum.inl (i,j))
  have hV : V.map (algebraMap R F) = algebraMap R F d • S := by
    ext i j
    exact hw (Sum.inr (i,j))
  refine ⟨d,U,V,hd,?_,?_,?_⟩
  · apply Matrix.map_injective (IsFractionRing.injective R F)
    change (U * V).map (algebraMap R F) = (d^2 • (1 : Matrix n n R)).map (algebraMap R F)
    rw [Matrix.map_mul,hU,hV,map_scalar_matrix]
    simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,hTS,pow_two,map_mul,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · apply Matrix.map_injective (IsFractionRing.injective R F)
    change (V * U).map (algebraMap R F) = (d^2 • (1 : Matrix b b R)).map (algebraMap R F)
    rw [Matrix.map_mul,hU,hV,map_scalar_matrix]
    simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,hST,pow_two,map_mul,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · intro i
    apply Matrix.map_injective (IsFractionRing.injective R F)
    change (U.transpose * A i * U).map (algebraMap R F) = (d^2 • J i).map (algebraMap R F)
    rw [Matrix.map_mul,Matrix.map_mul,Matrix.transpose_map,hU,map_scalar_matrix]
    simp only [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hform,pow_two,map_mul]

omit [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F] in
theorem simultaneous_congruence_specialize_certificate {E : Type*} [Field E]
    (A : ι → Matrix n n R) (J : ι → Matrix b b R)
    (d : R) (U : Matrix n b R) (V : Matrix b n R)
    (hUV : U*V=d^2 • 1) (hVU : V*U=d^2 • 1)
    (hform : ∀ i, U.transpose * A i * U = d^2 • J i)
    (φ : R →+* E) (hd : φ d ≠ 0) :
    ∃ (T : Matrix n b E) (S : Matrix b n E),
      T*S=1 ∧ S*T=1 ∧ ∀ i, T.transpose * (A i).map φ * T=(J i).map φ := by
  let T := (φ d)⁻¹ • U.map φ
  let S := (φ d)⁻¹ • V.map φ
  have hcancel : (φ d)⁻¹ * (φ d)⁻¹ * (φ d)^2 = 1 := by
    rw [← pow_two, ← mul_pow, inv_mul_cancel₀ hd, one_pow]
  have hUV' : U.map φ * V.map φ = (φ d)^2 • (1 : Matrix n n E) := by
    rw [← Matrix.map_mul,hUV,map_scalar_matrix,map_pow,Matrix.map_one φ (map_zero φ) (map_one φ)]
  have hVU' : V.map φ * U.map φ = (φ d)^2 • (1 : Matrix b b E) := by
    rw [← Matrix.map_mul,hVU,map_scalar_matrix,map_pow,Matrix.map_one φ (map_zero φ) (map_one φ)]
  refine ⟨T,S,?_,?_,?_⟩
  · simp only [T,S,Matrix.smul_mul,Matrix.mul_smul,hUV',smul_smul,← mul_assoc,hcancel,one_smul]
  · simp only [T,S,Matrix.smul_mul,Matrix.mul_smul,hVU',smul_smul,← mul_assoc,hcancel,one_smul]
  · intro i
    have h : (U.map φ).transpose * (A i).map φ * U.map φ = (φ d)^2 • (J i).map φ := by
      rw [← Matrix.transpose_map,← Matrix.map_mul,← Matrix.map_mul,hform,map_scalar_matrix,map_pow]
    simp only [T,Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,h,smul_smul,← mul_assoc,hcancel,one_smul]

end FD56

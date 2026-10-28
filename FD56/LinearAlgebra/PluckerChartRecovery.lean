/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PluckerLinearizedRelations
import FD56.LinearAlgebra.TwoColumnPluckerDominance

/-! A nonzero base minor and two rows determine all Plucker coordinates.
Faithful universal coefficient evaluation supplies a nonzero base minor. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem plucker_matrix_eq_of_two_rows {R n : Type*} [CommRing R] [IsDomain R]
    (F G : Matrix n n R) (i₀ i₁ : n) (hbase : F i₀ i₁≠0)
    (hfirst : ∀ j, F i₀ j=G i₀ j) (hsecond : ∀ j, F i₁ j=G i₁ j)
    (hF : ∀ i j, pluckerQuadraticRelation F i₀ i₁ i j=0)
    (hG : ∀ i j, pluckerQuadraticRelation G i₀ i₁ i j=0) : F=G := by
  funext i j
  apply mul_left_cancel₀ hbase
  have hf := hF i j
  have hg := hG i j
  dsimp only [pluckerQuadraticRelation] at hf hg
  rw [← hfirst i₁,← hfirst i,← hsecond j,← hfirst j,← hsecond i] at hg
  linear_combination hf-hg

theorem two_column_faithful_base_minor_ne_zero {K L n : Type*}
    [Field K] [Field L] [Algebra K L] [Fintype n]
    (a b : ℕ) (u v : n → L[X]) (hu : ∀ i, (u i).natDegree≤a)
    (hv : ∀ i, (v i).natDegree≤b)
    (hfaithful : Function.Injective (twoColumnMinorSpecialization a b
      (twoColumnCoefficientEvaluation (K:=K) a b u v)))
    (i₀ i₁ : n) (hi : i₀≠i₁) : u i₀*v i₁-u i₁*v i₀≠0 := by
  classical
  let U := twoColumnUniversalU K n a b
  let V := twoColumnUniversalV K n a b
  let A := twoColumnMinorCoefficientAlgebra K U V
  let x : A := ⟨(U i₀*V i₁-U i₁*V i₀).coeff 0,
    Algebra.subset_adjoin (Set.mem_range_self (i₀,i₁,0))⟩
  have hx : x≠0 := by
    intro hz
    have h := congrArg Subtype.val hz
    change (U i₀*V i₁-U i₁*V i₀).coeff 0=0 at h
    have hU (i : n) : (U i).coeff 0=MvPolynomial.X (Sum.inl (i,(0:Fin (a+1)))) :=
      twoColumnUniversalU_coeff K n a b i 0
    have hV (i : n) : (V i).coeff 0=MvPolynomial.X (Sum.inr (i,(0:Fin (b+1)))) :=
      twoColumnUniversalV_coeff K n a b i 0
    simp only [Polynomial.coeff_sub,Polynomial.mul_coeff_zero,hU,hV] at h
    let value : TwoColumnCoefficientIndex n a b → K :=
      Sum.elim (fun ik => if ik.1=i₀ then 1 else 0) (fun ik => if ik.1=i₁ then 1 else 0)
    have hh := congrArg (MvPolynomial.eval value) h
    simpa [value,hi,Ne.symm hi] using hh
  intro hz
  apply hx
  apply hfaithful
  change twoColumnCoefficientEvaluation (K:=K) a b u v x.val =
    twoColumnMinorSpecialization a b (twoColumnCoefficientEvaluation (K:=K) a b u v) 0
  rw [map_zero]
  change twoColumnCoefficientEvaluation (K:=K) a b u v
    ((twoColumnUniversalU K n a b i₀*twoColumnUniversalV K n a b i₁-
      twoColumnUniversalU K n a b i₁*twoColumnUniversalV K n a b i₀).coeff 0)=0
  rw [twoColumnCoefficientEvaluation_minor_coeff a b u v hu hv,hz,Polynomial.coeff_zero]

end FD56

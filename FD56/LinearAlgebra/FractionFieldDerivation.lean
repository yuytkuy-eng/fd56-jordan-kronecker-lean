/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.RingTheory.Localization.FractionRing

/-! Derivations extend to a fraction field. In particular, arbitrary velocities
of independent polynomial parameters extend to their rational function field. -/

noncomputable section
namespace FD56
set_option maxHeartbeats 1000000

variable {K R F : Type*} [CommRing K] [CommRing R] [IsDomain R] [Field F]
  [Algebra K R] [Algebra R F] [Algebra K F] [IsScalarTower K R F] [IsFractionRing R F]

theorem derivation_extends_fraction_field (D : Derivation K R F) :
    ∃ E : Derivation K F F, ∀ a : R, E (algebraMap R F a)=D a := by
  let g : R →+* TrivSqZeroExt F F :=
    { toFun := fun a => ⟨algebraMap R F a,D a⟩
      map_one' := by ext <;> simp
      map_mul' := by
        intro a b
        ext
        · exact map_mul (algebraMap R F) a b
        · simp [Derivation.leibniz,Algebra.smul_def,smul_eq_mul,mul_comm]
      map_zero' := by ext <;> simp
      map_add' := by intro a b; ext <;> simp }
  have hg (a : nonZeroDivisors R) : IsUnit (g a) := by
    apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
    apply isUnit_iff_ne_zero.mpr
    change algebraMap R F a≠0
    exact fun h => nonZeroDivisors.ne_zero a.property
      ((IsFractionRing.injective R F) (h.trans (map_zero _).symm))
  let L : F →+* TrivSqZeroExt F F := IsLocalization.lift hg
  have hL (a : R) : L (algebraMap R F a)=g a := IsLocalization.lift_eq hg a
  have hfst (x : F) : (L x).fst=x := by
    have he : (TrivSqZeroExt.fstHom F F F).toRingHom.comp L=RingHom.id F := by
      apply IsLocalization.ringHom_ext (M:=nonZeroDivisors R)
      ext a
      change (L (algebraMap R F a)).fst=algebraMap R F a
      rw [hL]
      rfl
    exact RingHom.congr_fun he x
  have hscalar (c : K) : (L (algebraMap K F c)).snd=0 := by
    rw [IsScalarTower.algebraMap_apply K R F,hL]
    change D (algebraMap K R c)=0
    exact D.map_algebraMap c
  let E : Derivation K F F :=
    { toFun := fun x => (L x).snd
      map_add' := by intro x y; simp
      map_smul' := by
        intro c x
        rw [Algebra.smul_def,map_mul,TrivSqZeroExt.snd_mul]
        simp [hfst,hscalar,Algebra.smul_def,smul_eq_mul]
      map_one_eq_zero' := by simp
      leibniz' := by
        intro x y
        change (L (x*y)).snd=x*(L y).snd+y*(L x).snd
        rw [map_mul,TrivSqZeroExt.snd_mul,hfst,hfst]
        simp only [smul_eq_mul,op_smul_eq_smul] }
  refine ⟨E,?_⟩
  intro a
  change (L (algebraMap R F a)).snd=D a
  rw [hL]
  rfl

theorem rational_parameter_derivation_exists {σ : Type*} (K₀ : Type*) [Field K₀]
    (v : σ → FractionRing (MvPolynomial σ K₀)) :
    ∃ D : Derivation K₀ (FractionRing (MvPolynomial σ K₀))
        (FractionRing (MvPolynomial σ K₀)),
      ∀ i, D (algebraMap (MvPolynomial σ K₀) (FractionRing (MvPolynomial σ K₀))
        (MvPolynomial.X i))=v i := by
  letI : IsDomain (MvPolynomial σ K₀) :=
    inferInstanceAs (IsDomain (AddMonoidAlgebra K₀ (σ →₀ ℕ)))
  obtain ⟨D,hD⟩ := derivation_extends_fraction_field (MvPolynomial.mkDerivation K₀ v)
  refine ⟨D,?_⟩
  intro i
  rw [hD,MvPolynomial.mkDerivation_X]

end FD56

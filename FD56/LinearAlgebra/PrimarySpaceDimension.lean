/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.SelfAdjointFitting
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Algebra.Polynomial.RingDivision

/-! Characteristic root multiplicities equal the dimensions of the corresponding primary spaces. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem matrix_charpoly_sub_scalar {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (a : K) :
    (A-a•1).charpoly=A.charpoly.comp (X+C a) := by
  let φ := Polynomial.compRingHom (X+C a)
  have he : (A-a•1).charmatrix=A.charmatrix.map φ := by
    funext i j
    by_cases h : i=j
    · subst j
      simp [Matrix.charmatrix_apply,Matrix.one_apply,φ,sub_eq_add_neg,add_assoc,add_comm,
        add_left_comm]
    · simp [Matrix.charmatrix_apply,Matrix.one_apply,h,φ]
  rw [Matrix.charpoly,he]
  exact (φ.map_det A.charmatrix).symm

theorem linearMap_charpoly_sub_scalar {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) (a : K) :
    (f-a•1).charpoly=f.charpoly.comp (X+C a) := by
  let b := Module.finBasis K V
  rw [← LinearMap.charpoly_toMatrix _ b,← LinearMap.charpoly_toMatrix f b]
  simp only [map_sub,map_smul,LinearMap.toMatrix_one]
  exact matrix_charpoly_sub_scalar _ a

theorem primary_space_finrank_eq_rootMultiplicity {K V : Type*}
    [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (a : K) :
    Module.finrank K (f.maxGenEigenspace a)=rootMultiplicity a f.charpoly := by
  have he : (f-a•1).maxGenEigenspace 0=f.maxGenEigenspace a := by
    simp [Module.End.maxGenEigenspace,Module.End.genEigenspace]
  rw [← he,LinearMap.finrank_maxGenEigenspace,linearMap_charpoly_sub_scalar,
    ← Polynomial.rootMultiplicity_eq_natTrailingDegree]

theorem primary_kernel_finrank_eq_rootMultiplicity {K V : Type*}
    [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (a : K) :
    Module.finrank K (LinearMap.ker ((f-a•1)^Module.finrank K V))=
      rootMultiplicity a f.charpoly := by
  rw [← Module.End.genEigenspace_nat,← Module.End.maxGenEigenspace_eq_genEigenspace_finrank]
  exact primary_space_finrank_eq_rootMultiplicity f a

end FD56

/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.RingTheory.Localization.Integral
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! A finite family of polynomials over a fraction field has a common scalar denominator. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators nonZeroDivisors
variable {R F ι : Type*} [CommRing R] [IsDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F] [Fintype ι]

theorem polynomial_family_clear_denominators (p : ι → F[X]) :
    ∃ (d : R) (w : ι → R[X]), d≠0 ∧
      ∀ i, (w i).map (algebraMap R F)=C (algebraMap R F d)*p i := by
  classical
  choose b hb using fun i => IsLocalization.integerNormalization_map_to_map R⁰ (p i)
  let d : R := ∏ i, (b i : R)
  let c (i : ι) : R := ∏ j∈Finset.univ.erase i, (b j : R)
  let w (i : ι) : R[X] := C (c i)*IsLocalization.integerNormalization R⁰ (p i)
  have hd : d≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => nonZeroDivisors.ne_zero (b i).property)
  refine ⟨d,w,hd,?_⟩
  intro i
  have hn : (IsLocalization.integerNormalization R⁰ (p i)).map (algebraMap R F)=
      C (algebraMap R F (b i))*p i := by
    rw [hb i,← IsScalarTower.algebraMap_smul F,Polynomial.smul_eq_C_mul]
  have hcb : c i*(b i : R)=d := by
    exact Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  simp only [w,Polynomial.map_mul,Polynomial.map_C,hn,← mul_assoc,← map_mul,hcb]

end FD56

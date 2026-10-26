/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeSeventeenFiveSyzygyData
import FD56.LinearAlgebra.RankSpecialization

/-! The exact terminal relation matrix has minimal degrees twelve, thirteen, thirteen. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

theorem seventeenFive_terminal_eval_one :
    (seventeenFiveF (K := K)).map (Polynomial.evalRingHom 1) =
      ![![6,8],![14,13],![-2,-1],![18,19],![4,2]] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [seventeenFiveF,seventeenFiveTerminalCoefficients,integerPolynomial]

variable [CharZero K]

theorem seventeenFive_terminal_nullity :
    Module.finrank (FractionRing K[X]) (LinearMap.ker (Matrix.toLin'
      ((seventeenFiveF (K := K)).transpose.map (algebraMap K[X] (FractionRing K[X]))))) = 3 := by
  let A := (seventeenFiveF (K := K)).transpose
  let R : Matrix (Fin 5) (Fin 2) K :=
    ![![-13/34,7/17],![4/17,-3/17],![0,0],![0,0],![0,0]]
  have hR : A.map (Polynomial.evalRingHom 1) * R = 1 := by
    dsimp only [A]
    rw [Matrix.transpose_map,seventeenFive_terminal_eval_one]
    funext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [R,Matrix.mul_apply,Fin.sum_univ_succ]
  have hsurj : Function.Surjective (A.map (Polynomial.evalRingHom 1)).mulVec := by
    intro v
    refine ⟨R *ᵥ v, ?_⟩
    rw [Matrix.mulVec_mulVec,hR,Matrix.one_mulVec]
  have hs := matrix_surjective_of_specialization Polynomial.C (Polynomial.evalRingHom (1 : K))
    (by intro c; simp) (algebraMap K[X] (FractionRing K[X]))
    (IsFractionRing.injective K[X] (FractionRing K[X])) A hsurj
  have hd := (Matrix.toLin' (A.map (algebraMap K[X] (FractionRing K[X])))).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs] at hd
  simp only [finrank_top,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at hd
  change Module.finrank (FractionRing K[X]) (LinearMap.ker (Matrix.toLin'
    (A.map (algebraMap K[X] (FractionRing K[X]))))) = 3
  omega

theorem seventeenFive_syzygy_left_inverse :
    ∃ L : Matrix (Fin 3) (Fin 5) K[X], L * seventeenFiveSyzygy (K := K) = 1 := by
  let E : Fin 10 → Matrix (Fin 3) (Fin 5) K[X] := fun i =>
    (1 : Matrix (Fin 5) (Fin 5) K[X]).submatrix (seventeenFiveMinorRows i) id
  have hE (i : Fin 10) : E i * seventeenFiveSyzygy =
      (seventeenFiveSyzygy (K := K)).submatrix (seventeenFiveMinorRows i) id := by
    simpa only [E,Equiv.refl_apply,Function.id_comp] using
      Matrix.one_submatrix_mul (seventeenFiveMinorRows i) (Equiv.refl (Fin 5))
        (seventeenFiveSyzygy (K := K))
  let δ : K := 129656897160136956545278754681170029565868690544945253826037143923671360
  have hδ : δ ≠ 0 := by norm_num [δ]
  apply left_inverse_of_bezout seventeenFiveSyzygy E
    (fun i => C δ⁻¹ * seventeenFiveBezout i)
  simp_rw [hE,seventeenFive_syzygy_minor]
  calc
    _ = C δ⁻¹ * integerPolynomial [70749800997046548362597663733543613664] *
        (∑ i : Fin 10, seventeenFiveBezout (K := K) i * seventeenFiveMinor i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 1 := by
      rw [seventeenFive_minor_bezout,integerPolynomial_singleton,integerPolynomial_singleton]
      rw [← Polynomial.C_eq_intCast (R := K) (70749800997046548362597663733543613664 : ℤ),
        ← Polynomial.C_eq_intCast (R := K) (1832611474985625555424493152821990 : ℤ),
        ← map_mul,← map_mul]
      have hprod : ((70749800997046548362597663733543613664 : ℤ) : K) *
          ((1832611474985625555424493152821990 : ℤ) : K) = δ := by norm_num [δ]
      rw [mul_assoc,hprod,inv_mul_cancel₀ hδ,map_one]

theorem seventeenFive_terminal_minimal_degrees :
    HasMinimalKernelDegrees (seventeenFiveF (K := K)).transpose [12,13,13] := by
  obtain ⟨L,hL⟩ := seventeenFive_syzygy_left_inverse (K := K)
  have hh := minimal_degrees_of_left_inverse_and_nullity
    (algebraMap K[X] (FractionRing K[X])) (IsFractionRing.injective K[X] (FractionRing K[X]))
    (seventeenFiveF (K := K)).transpose seventeenFiveSyzygy L hL
    seventeenFive_syzygy_relation seventeenFive_terminal_nullity seventeenFiveSyzygyDegrees
    seventeenFive_syzygy_degree seventeenFive_syzygy_leading_injective
  simpa [seventeenFiveSyzygyDegrees,List.ofFn_succ] using hh

theorem seventeenFive_terminal_hilbert (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (seventeenFiveF (K := K)).transpose d) =
      (d+1-12) + 2*(d+1-13) := by
  rw [(hasMinimalKernelDegrees_iff_hilbert _ _).mp seventeenFive_terminal_minimal_degrees d]
  simp
  omega

end FD56

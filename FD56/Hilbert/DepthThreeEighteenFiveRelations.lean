/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeEighteenFiveSyzygyData
import FD56.LinearAlgebra.RankSpecialization

/-! The exact terminal relation matrix has minimal degrees twenty-one, twenty-one. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

theorem eighteenFive_terminal_eval_one :
    (eighteenFiveF (K := K)).map (Polynomial.evalRingHom 1) =
      ![![-220,-96,-230], ![20,0,190], ![20,-20,40], ![-140,-116,-160], ![-100,-96,30]] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [eighteenFiveF,eighteenFiveTerminalCoefficients,integerPolynomial]

variable [CharZero K]

theorem eighteenFive_terminal_nullity :
    Module.finrank (FractionRing K[X]) (LinearMap.ker (Matrix.toLin'
      ((eighteenFiveF (K := K)).transpose.map (algebraMap K[X] (FractionRing K[X]))))) = 2 := by
  let A := (eighteenFiveF (K := K)).transpose
  let R : Matrix (Fin 5) (Fin 3) K :=
    ![![-19/5160,-1/344,1/2580], ![-211/25800,7/1720,79/12900], ![19/1075,-31/860,-2/1075], ![0,0,0], ![0,0,0]]
  have hR : A.map (Polynomial.evalRingHom 1) * R = 1 := by
    dsimp only [A]
    rw [Matrix.transpose_map,eighteenFive_terminal_eval_one]
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
    (A.map (algebraMap K[X] (FractionRing K[X]))))) = 2
  omega

theorem eighteenFive_syzygy_left_inverse :
    ∃ L : Matrix (Fin 2) (Fin 5) K[X], L * eighteenFiveSyzygy (K := K) = 1 := by
  let E : Fin 10 → Matrix (Fin 2) (Fin 5) K[X] := fun i =>
    (1 : Matrix (Fin 5) (Fin 5) K[X]).submatrix (eighteenFiveMinorRows i) id
  have hE (i : Fin 10) : E i * eighteenFiveSyzygy =
      (eighteenFiveSyzygy (K := K)).submatrix (eighteenFiveMinorRows i) id := by
    simpa only [E,Equiv.refl_apply,Function.id_comp] using
      Matrix.one_submatrix_mul (eighteenFiveMinorRows i) (Equiv.refl (Fin 5))
        (eighteenFiveSyzygy (K := K))
  let δ : K := 116224703013891832250905540767025900515905466090343388494891960750331430503050853305909281276181629489576263896351349992932603593302694104698098092219983296316672
  have hδ : δ ≠ 0 := by norm_num [δ]
  apply left_inverse_of_bezout eighteenFiveSyzygy E
    (fun i => C δ⁻¹ * eighteenFiveBezout i)
  simp_rw [hE,eighteenFive_syzygy_minor]
  calc
    _ = C δ⁻¹ * integerPolynomial [1216962839281442206506917666128505963619611749611221853420166489870929928017600676548] *
        (∑ i : Fin 10, eighteenFiveBezout (K := K) i * eighteenFiveMinor i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 1 := by
      rw [eighteenFive_minor_bezout,integerPolynomial_singleton,integerPolynomial_singleton]
      rw [← Polynomial.C_eq_intCast (R := K) (1216962839281442206506917666128505963619611749611221853420166489870929928017600676548 : ℤ),
        ← Polynomial.C_eq_intCast (R := K) (95503904689905656671371976338539704503619566401237449229699165250516761171264 : ℤ),
        ← map_mul,← map_mul]
      have hprod : ((1216962839281442206506917666128505963619611749611221853420166489870929928017600676548 : ℤ) : K) *
          ((95503904689905656671371976338539704503619566401237449229699165250516761171264 : ℤ) : K) = δ := by norm_num [δ]
      rw [mul_assoc,hprod,inv_mul_cancel₀ hδ,map_one]

theorem eighteenFive_terminal_minimal_degrees :
    HasMinimalKernelDegrees (eighteenFiveF (K := K)).transpose [21,21] := by
  obtain ⟨L,hL⟩ := eighteenFive_syzygy_left_inverse (K := K)
  have hh := minimal_degrees_of_left_inverse_and_nullity
    (algebraMap K[X] (FractionRing K[X])) (IsFractionRing.injective K[X] (FractionRing K[X]))
    (eighteenFiveF (K := K)).transpose eighteenFiveSyzygy L hL
    eighteenFive_syzygy_relation eighteenFive_terminal_nullity eighteenFiveSyzygyDegrees
    eighteenFive_syzygy_degree eighteenFive_syzygy_leading_injective
  simpa [eighteenFiveSyzygyDegrees,List.ofFn_succ] using hh

theorem eighteenFive_terminal_hilbert (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (eighteenFiveF (K := K)).transpose d) =
      2*(d+1-21) := by
  rw [(hasMinimalKernelDegrees_iff_hilbert _ _).mp eighteenFive_terminal_minimal_degrees d]
  simp
  omega

end FD56

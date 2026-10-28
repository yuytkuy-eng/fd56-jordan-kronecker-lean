/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FourOutputInteriorMinors
import FD56.Hilbert.FourOutputMinorDegrees
import FD56.Hilbert.ObservabilityTerminalLeading
import FD56.Hilbert.PrimitiveRowDegreeBudget
import FD56.LinearAlgebra.PluckerActionRowModule

/-! Explicit Cauchy--Binet certificates make the six terminal minors and their
signed polar row primitive. A nonzero top coefficient gives the exact kernel
length and total degree. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem fourOutputPlucker_cauchyBinet {R : Type*} [CommRing R]
    (G : Matrix (Fin 4) (Fin 2) R) (L : Matrix (Fin 2) (Fin 4) R) :
    (∑ i : Fin 6, fourOutputPluckerVector G i*fourOutputPluckerVector L.transpose i)=
      (L*G).det := by
  simp [fourOutputPluckerVector,fourOutputPluckerRows,pluckerMinorVector,
    Matrix.det_fin_two,Matrix.mul_apply,Fin.sum_univ_succ]
  ring

theorem fourOutputPlucker_row_right_inverse {R : Type*} [CommRing R]
    (G : Matrix (Fin 4) (Fin 2) R) (L : Matrix (Fin 2) (Fin 4) R) (hLG : L*G=1) :
    (show Matrix Unit (Fin 6) R from fun _ => fourOutputPluckerVector G)*
      (show Matrix (Fin 6) Unit R from fun i _ => fourOutputPluckerVector L.transpose i)=1 := by
  funext i j
  cases i
  cases j
  change (∑ i : Fin 6, fourOutputPluckerVector G i*fourOutputPluckerVector L.transpose i)=1
  rw [fourOutputPlucker_cauchyBinet,hLG,Matrix.det_one]

theorem pluckerPolarRow_right_inverse {R : Type*} [CommRing R]
    (F : Fin 6 → R) (V : Matrix (Fin 6) Unit R)
    (hV : (show Matrix Unit (Fin 6) R from fun _ => F)*V=1) :
    ∃ S : Matrix (Fin 6) Unit R,pluckerPolarRow F*S=1 := by
  refine ⟨fun i _ => ![V 5 (),-V 4 (),V 3 (),V 2 (),-V 1 (),V 0 ()] i,?_⟩
  funext i j
  cases i
  cases j
  have h := congrFun (congrFun hV ()) ()
  simp [pluckerPolarRow,Matrix.mul_apply,Fin.sum_univ_succ] at h ⊢
  linear_combination h

variable {K : Type*} [Field K]

theorem generic_four_output_minors_right_inverse (q : ℕ)
    (B : Basis (Fin 2)
      (AffineCoefficientField K (MatrixParameters (Fin (4*q+2)) (Fin 4)))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
        (genericAffineRows K (Fin (4*q+2)) (Fin 4)) q)))) :
    ∃ S : Matrix (Fin 6) Unit
      (AffineCoefficientField K (MatrixParameters (Fin (4*q+2)) (Fin 4)))[X],
      ((show Matrix Unit (Fin 6)
        (AffineCoefficientField K (MatrixParameters (Fin (4*q+2)) (Fin 4)))[X]
        from fun _ => genericFourOutputInteriorMinors (K:=K) q)*S : Matrix Unit Unit
          (AffineCoefficientField K (MatrixParameters (Fin (4*q+2)) (Fin 4)))[X])=1 := by
  let M := genericAffineSquare K (Fin (4*q+2)) (Fin 4)
  let P := genericAffineRows K (Fin (4*q+2)) (Fin 4)
  let G := P*M^q*polynomialKernelBasisMatrix (observabilityMatrix M P q) B
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse
    (K:=K) (n:=Fin (4*q+2)) (m:=Fin 4) q (by simp only [Fintype.card_fin]; omega)
  obtain ⟨L,hL⟩ := generic_terminal_kernel_left_inverse
    (K:=K) (n:=Fin (4*q+2)) (m:=Fin 4) q (by simp)
    (by simp only [Fintype.card_fin]; omega) (by simp only [Fintype.card_fin]; omega) B
  change L*G=1 at hL
  obtain ⟨c,hc,hcF⟩ := fourOutputInteriorMinors_common_scalar q M P R hR B
  refine ⟨fun i _ => C c⁻¹*fourOutputPluckerVector L.transpose i,?_⟩
  funext i j
  cases i
  cases j
  change (∑ i, genericFourOutputInteriorMinors (K:=K) q i*
    (C c⁻¹*fourOutputPluckerVector L.transpose i))=1
  have hF (i : Fin 6) : genericFourOutputInteriorMinors (K:=K) q i=
      C c*fourOutputPluckerVector G i := hcF i
  simp_rw [hF]
  have hcancel (i : Fin 6) : C c*fourOutputPluckerVector G i*
      (C c⁻¹*fourOutputPluckerVector L.transpose i)=
      fourOutputPluckerVector G i*fourOutputPluckerVector L.transpose i := by
    calc
      _ = (C c*C c⁻¹)*(fourOutputPluckerVector G i*fourOutputPluckerVector L.transpose i) := by ring
      _ = _ := by rw [← Polynomial.C_mul,mul_inv_cancel₀ hc,Polynomial.C_1,one_mul]
  simp_rw [hcancel]
  rw [fourOutputPlucker_cauchyBinet,hL,Matrix.det_one]

theorem pluckerPolarRow_minimal_degree_budget
    (F : Fin 6 → K[X]) (S : Matrix (Fin 6) Unit K[X])
    (hS : (show Matrix Unit (Fin 6) K[X] from fun _ => F)*S=1)
    (W : ℕ) (hdegree : ∀ i, (F i).natDegree≤W) (hcoeff : (F 0).coeff W≠0)
    (xs : List ℕ) (hmin : HasMinimalKernelDegrees (pluckerPolarRow F) xs) :
    xs.length=5 ∧ xs.sum=W := by
  obtain ⟨T,hT⟩ := pluckerPolarRow_right_inverse F S hS
  have hrow : ∀ (_ : Unit) j, ((pluckerPolarRow F) () j).natDegree≤W := by
    intro i j
    fin_cases j
    · exact hdegree 5
    · simpa [pluckerPolarRow] using hdegree 4
    · exact hdegree 3
    · exact hdegree 2
    · simpa [pluckerPolarRow] using hdegree 1
    · exact hdegree 0
  have hlead : Function.Surjective (show Matrix Unit (Fin 6) K from
      fun i j => ((pluckerPolarRow F) i j).coeff W).mulVec := by
    intro v
    refine ⟨Pi.single 5 (v ()/(F 0).coeff W),?_⟩
    funext i
    cases i
    rw [Matrix.mulVec_single]
    change (F 0).coeff W*(v ()/(F 0).coeff W)=v ()
    field_simp
  obtain ⟨hlen,hsum⟩ := minimal_degree_budget_of_right_inverse_and_leading
    (pluckerPolarRow F) T hT (fun _ => W) hrow hlead xs hmin
  simpa using And.intro hlen hsum

theorem generic_four_output_polar_minimal_degree_budget (q : ℕ)
    (B : Basis (Fin 2)
      (AffineCoefficientField K (MatrixParameters (Fin (4*q+2)) (Fin 4)))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
        (genericAffineRows K (Fin (4*q+2)) (Fin 4)) q))))
    (xs : List ℕ)
    (hmin : HasMinimalKernelDegrees
      (pluckerPolarRow (genericFourOutputInteriorMinors (K:=K) q)) xs) :
    xs.length=5 ∧ xs.sum=2*(q+1)^2 := by
  obtain ⟨S,hS⟩ := generic_four_output_minors_right_inverse q B
  have hcoeff : (genericFourOutputInteriorMinors (K:=K) q 0).coeff (2*(q+1)^2)≠0 := by
    rw [← generic_four_output_first_minor_degree (K:=K) q,Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr (generic_four_output_first_minor_ne_zero (K:=K) q)
  exact pluckerPolarRow_minimal_degree_budget _ S hS _
    (generic_four_output_minors_degree (K:=K) q) hcoeff xs hmin

end FD56

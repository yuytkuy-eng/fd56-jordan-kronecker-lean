/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericInteriorDegreeBalance
import FD56.LinearAlgebra.TwoColumnPluckerDominance

/-! Actual generic observability minors with remainder two faithfully
specialize the universal balanced two-column minor coefficient algebra. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000

private theorem plucker_two_columns {R m : Type*} [CommRing R]
    (G : Matrix m (Fin 2) R) (row : Fin 2 → m) :
    pluckerMinorVector G row=G (row 0) 0*G (row 1) 1-G (row 1) 0*G (row 0) 1 := by
  simp only [pluckerMinorVector,Matrix.det_fin_two,Matrix.submatrix_apply,id_eq]
  rw [mul_comm (G (row 0) 1) (G (row 1) 0)]

private theorem orient_two_columns {L m : Type*} [Field L]
    (G : Matrix m (Fin 2) L[X]) (d : Fin 2 → ℕ) (c : L)
    (hG : ∀ i j, (G i j).natDegree≤d j) (hbal : ∀ i j, d i≤d j+1) :
    ∃ (a b : ℕ) (u v : m → L[X]), (b=a ∨ b=a+1) ∧ a+b=d 0+d 1 ∧
      (∀ i, (u i).natDegree≤a) ∧ (∀ i, (v i).natDegree≤b) ∧
      ∀ i j, C c*(G i 0*G j 1-G j 0*G i 1)=u i*v j-u j*v i := by
  by_cases ho : d 0≤d 1
  · refine ⟨d 0,d 1,(fun i => C c*G i 0),(fun i => G i 1),?_,rfl,?_,?_,?_⟩
    · have := hbal 1 0; omega
    · intro i; exact (natDegree_C_mul_le _ _).trans (hG i 0)
    · exact fun i => hG i 1
    · intro i j; ring
  · refine ⟨d 1,d 0,(fun i => -(C c*G i 1)),(fun i => G i 0),?_,by omega,?_,?_,?_⟩
    · have := hbal 0 1; omega
    · intro i
      simpa only [natDegree_neg] using (natDegree_C_mul_le c (G i 1)).trans (hG i 1)
    · exact fun i => hG i 0
    · intro i j; ring

variable {K : Type*} [Field K] [CharZero K]
variable (s q : ℕ) [NeZero s]

private abbrev TwoColumnActualField :=
  AffineCoefficientField K (MatrixParameters (Fin ((2+s)*q+2)) (Fin (2+s)))

def genericTwoColumnSelectedRows (z : Option (Fin 2 × Fin s)) : Fin (2+s) × Fin (2+s) :=
  (interiorTerminalRow 2 s z 0,interiorTerminalRow 2 s z 1)

private theorem faithful_realization_of_basis (hq : 0<q)
    (B : Basis (Fin 2) (TwoColumnActualField (K:=K) s q)[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K (Fin ((2+s)*q+2)) (Fin (2+s)))
        (genericAffineRows K (Fin ((2+s)*q+2)) (Fin (2+s))) q))))
    (e : Fin 2 → ℕ)
    (hV : ∀ i j, (polynomialKernelBasisMatrix _ B i j).natDegree≤e j)
    (hVL : Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix _ B i j).coeff (e j)))) :
    ∃ (a b : ℕ) (u v : Fin (2+s) → (TwoColumnActualField (K:=K) s q)[X]),
      (b=a ∨ b=a+1) ∧ 2*(a+b)=(2+s)*q*(q+1)+4*(q+1) ∧
      (∀ i, (u i).natDegree≤a) ∧ (∀ i, (v i).natDegree≤b) ∧
      (∀ z, genericInteriorMinorVector (K:=K) 2 s q z=
        u (genericTwoColumnSelectedRows s z).1*v (genericTwoColumnSelectedRows s z).2-
        u (genericTwoColumnSelectedRows s z).2*v (genericTwoColumnSelectedRows s z).1) ∧
      Function.Injective (twoColumnMinorSpecialization a b
        (twoColumnCoefficientEvaluation (K:=K) a b u v)) := by
  classical
  let L := TwoColumnActualField (K:=K) s q
  let M := genericAffineSquare K (Fin ((2+s)*q+2)) (Fin (2+s))
  let P := genericAffineRows K (Fin ((2+s)*q+2)) (Fin (2+s))
  let O := observabilityMatrix M P q
  let V := polynomialKernelBasisMatrix O B
  let G := P*M^q*V
  let d : Fin 2 → ℕ := fun i => e i+q+1
  let W := (∑ i, e i)+(q+1)*2
  have hs : 0<s := NeZero.pos s
  have hm : 2≤Fintype.card (Fin (2+s)) := by simp
  have hlo : q*Fintype.card (Fin (2+s))<Fintype.card (Fin ((2+s)*q+2)) := by
    simp only [Fintype.card_fin]; nlinarith
  have hhi : Fintype.card (Fin ((2+s)*q+2))<(q+1)*Fintype.card (Fin (2+s)) := by
    simp only [Fintype.card_fin]; nlinarith
  have hmin : HasMinimalKernelDegrees O (List.ofFn e) := ⟨2,B,e,hV,hVL,List.Perm.refl _⟩
  have hbudget := (generic_observability_kernel_degree_budget q hlo _ hmin).2
  simp only [List.sum_ofFn,Fintype.card_fin] at hbudget
  have hW : 2*W=(2+s)*q*(q+1)+2*(q+1)*2 := by dsimp [W]; nlinarith
  have hsum : (∑ i, d i)=W := by
    simp only [d,W,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    ring
  have hGdegree := (generic_terminal_kernel_degree_and_leading q hhi.le B e hV hVL).1
  change ∀ i j, (G i j).natDegree≤d j at hGdegree
  obtain ⟨LG,hLG⟩ := generic_terminal_kernel_left_inverse q hm hlo hhi B
  change LG*G=1 at hLG
  have hGinj : Function.Injective G.mulVec := by
    intro x y h
    have hh := congrArg LG.mulVec h
    simpa only [Matrix.mulVec_mulVec,hLG,Matrix.one_mulVec] using hh
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse (K:=K) q hlo
  obtain ⟨c,_,hc⟩ := interior_selected_minors_common_scalar 2 s q M P R hR B
  have hminor : genericInteriorMinorVector (K:=K) 2 s q=
      fun z => C c*pluckerMinorVector G (interiorTerminalRow 2 s z) := funext hc
  have hlower := generic_interior_minor_derivation_rank_lower_of_weight (K:=K) 2 s q hq W hW
  have hbal : ∀ i j, d i≤d j+1 := by
    apply polynomial_derivation_selected_plucker_degrees_balanced (K:=K)
      (interiorTerminalRow 2 s) c G d hGdegree hGinj (by simp)
    rw [← hminor]
    simpa only [Fintype.card_fin,hsum,Nat.add_sub_cancel_left,Nat.mul_comm s 2,
      Nat.add_assoc] using hlower
  obtain ⟨a,b,u,v,hab,hsum',hu,hv,huv⟩ := orient_two_columns G d c hGdegree hbal
  have habW : a+b=W := by
    rw [← hsum]
    simpa [Fin.sum_univ_succ] using hsum'
  have hp : ∀ z, genericInteriorMinorVector (K:=K) 2 s q z=
      u (genericTwoColumnSelectedRows s z).1*v (genericTwoColumnSelectedRows s z).2-
      u (genericTwoColumnSelectedRows s z).2*v (genericTwoColumnSelectedRows s z).1 := by
    intro z
    rw [hminor]
    change C c*pluckerMinorVector G (interiorTerminalRow 2 s z)=_
    rw [plucker_two_columns]
    exact huv (interiorTerminalRow 2 s z 0) (interiorTerminalRow 2 s z 1)
  refine ⟨a,b,u,v,hab,by rw [habW]; nlinarith,hu,hv,hp,?_⟩
  apply two_column_coefficient_evaluation_faithful a b hab
    (0 : Fin (2+s)) (1 : Fin (2+s)) (by simp; omega) u v hu hv (genericTwoColumnSelectedRows s)
  rw [← funext hp]
  have hbound : Fintype.card (Fin (2+s))*(a+b+2)-3=(2+s)*W+2*s+1 := by
    simp only [Fintype.card_fin,habW]
    have he : (2+s)*(W+2)=(2+s)*W+2*s+4 := by ring
    omega
  rw [hbound]
  exact hlower

theorem generic_two_column_plucker_specialization_faithful (hq : 0<q) :
    ∃ (a b : ℕ) (u v : Fin (2+s) → (TwoColumnActualField (K:=K) s q)[X]),
      (b=a ∨ b=a+1) ∧ 2*(a+b)=(2+s)*q*(q+1)+4*(q+1) ∧
      (∀ i, (u i).natDegree≤a) ∧ (∀ i, (v i).natDegree≤b) ∧
      (∀ z, genericInteriorMinorVector (K:=K) 2 s q z=
        u (genericTwoColumnSelectedRows s z).1*v (genericTwoColumnSelectedRows s z).2-
        u (genericTwoColumnSelectedRows s z).2*v (genericTwoColumnSelectedRows s z).1) ∧
      Function.Injective (twoColumnMinorSpecialization a b
        (twoColumnCoefficientEvaluation (K:=K) a b u v)) := by
  let O := observabilityMatrix
    (genericAffineSquare K (Fin ((2+s)*q+2)) (Fin (2+s)))
    (genericAffineRows K (Fin ((2+s)*q+2)) (Fin (2+s))) q
  have hlo : q*Fintype.card (Fin (2+s))<Fintype.card (Fin ((2+s)*q+2)) := by
    simp only [Fintype.card_fin]; nlinarith
  obtain ⟨k,B,e,hV,hVL,_,_⟩ := polynomial_kernel_has_minimal_basis O
  have hmin : HasMinimalKernelDegrees O (List.ofFn e) := ⟨k,B,e,hV,hVL,List.Perm.refl _⟩
  have hk := (generic_observability_kernel_degree_budget (K:=K) q hlo _ hmin).1
  simp only [List.length_ofFn,Fintype.card_fin] at hk
  have hk' : k=2 := by nlinarith
  subst k
  exact faithful_realization_of_basis s q hq B e hV hVL

end FD56

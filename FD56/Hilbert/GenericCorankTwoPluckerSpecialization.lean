/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericInteriorDegreeBalance
import FD56.Hilbert.InteriorFullGradients
import FD56.LinearAlgebra.TwoColumnPluckerDominance
import FD56.LinearAlgebra.PolynomialDerivationScaling

/-! Generic interior minors of corank two faithfully realize the universal
balanced two-column minor algebra, with complementary permutation signs. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 3000000

def corankTwoRowSign {K : Type*} [Field K] {r : ℕ}
    (row : Fin r ⊕ Fin 2 ≃ Fin (r+2)) : K :=
  ((Equiv.Perm.sign (row.trans finSumFinEquiv.symm) : ℤ) : K)

private theorem corankTwoRowSign_ne_zero {K : Type*} [Field K] {r : ℕ}
    (row : Fin r ⊕ Fin 2 ≃ Fin (r+2)) : corankTwoRowSign (K:=K) row ≠ 0 := by
  exact (IsUnit.map (Int.castRingHom K)
    (Units.isUnit (Equiv.Perm.sign (row.trans finSumFinEquiv.symm)))).ne_zero

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
variable (r q : ℕ) [NeZero r]

private abbrev CorankTwoActualField :=
  AffineCoefficientField K (MatrixParameters (Fin ((r+2)*q+r)) (Fin (r+2)))

private theorem faithful_realization_of_bases (hq : 0<q)
    (Bv : Basis (Fin r) (CorankTwoActualField (K:=K) r q)[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K (Fin ((r+2)*q+r)) (Fin (r+2)))
        (genericAffineRows K (Fin ((r+2)*q+r)) (Fin (r+2))) q))))
    (Bt : Basis (Fin 2) (CorankTwoActualField (K:=K) r q)[X]
      (LinearMap.ker (Matrix.toLin'
        (genericAffineRows K (Fin ((r+2)*q+r)) (Fin (r+2)) *
          (genericAffineSquare K (Fin ((r+2)*q+r)) (Fin (r+2)))^q *
          polynomialKernelBasisMatrix _ Bv).transpose)))
    (av : Fin r → ℕ) (bt : Fin 2 → ℕ)
    (hV : ∀ i j, (polynomialKernelBasisMatrix _ Bv i j).natDegree≤av j)
    (hT : ∀ i j, (polynomialKernelBasisMatrix _ Bt i j).natDegree≤bt j)
    (hVL : Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix _ Bv i j).coeff (av j))))
    (hTL : Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix _ Bt i j).coeff (bt j)))) :
    ∃ (a b : ℕ) (u v : Fin (r+2) → (CorankTwoActualField (K:=K) r q)[X]),
      (b=a ∨ b=a+1) ∧ 2*(a+b)=(r+2)*q*(q+1)+2*(q+1)*r ∧
      (∀ i, (u i).natDegree≤a) ∧ (∀ i, (v i).natDegree≤b) ∧
      (∀ row : Fin r ⊕ Fin 2 ≃ Fin (r+2),
        interiorFullMinor r 2 q (genericAffineSquare K _ _) (genericAffineRows K _ _)
            (fun i => row (Sum.inl i)) =
          C (algebraMap K _ (corankTwoRowSign (K:=K) row)) *
            (u (row (Sum.inr 0))*v (row (Sum.inr 1))-
              u (row (Sum.inr 1))*v (row (Sum.inr 0)))) ∧
      Function.Injective (twoColumnMinorSpecialization a b
        (twoColumnCoefficientEvaluation (K:=K) a b u v)) := by
  classical
  let L := CorankTwoActualField (K:=K) r q
  let M := genericAffineSquare K (Fin ((r+2)*q+r)) (Fin (r+2))
  let P := genericAffineRows K (Fin ((r+2)*q+r)) (Fin (r+2))
  let O := observabilityMatrix M P q
  let G := P*M^q*polynomialKernelBasisMatrix O Bv
  let T := polynomialKernelBasisMatrix G.transpose Bt
  let W := (∑ i, av i)+(q+1)*r
  have hr : 0<r := NeZero.pos r
  have hm : 2≤Fintype.card (Fin (r+2)) := by simp
  have hlo : q*Fintype.card (Fin (r+2))<Fintype.card (Fin ((r+2)*q+r)) := by
    simp only [Fintype.card_fin]; nlinarith
  have hhi : Fintype.card (Fin ((r+2)*q+r))<(q+1)*Fintype.card (Fin (r+2)) := by
    simp only [Fintype.card_fin]; nlinarith
  have hminV : HasMinimalKernelDegrees O (List.ofFn av) :=
    ⟨r,Bv,av,hV,hVL,List.Perm.refl _⟩
  have hminT : HasMinimalKernelDegrees G.transpose (List.ofFn bt) :=
    ⟨2,Bt,bt,hT,hTL,List.Perm.refl _⟩
  have hbudget := (generic_observability_kernel_degree_budget q hlo _ hminV).2
  simp only [List.sum_ofFn,Fintype.card_fin] at hbudget
  have hW : 2*W=(r+2)*q*(q+1)+2*(q+1)*r := by dsimp [W]; nlinarith
  have hsumT : (∑ i, bt i)=W := by
    simpa only [List.sum_ofFn,Fintype.card_fin] using
      (generic_terminal_kernel_degree_budget q hm hlo hhi Bv av hV hVL _ hminT).2
  have hbal := (generic_interior_auxiliary_degrees_balanced r 2 q hq
    Bv Bt av bt hV hT hVL hTL).2
  obtain ⟨LG,hLG⟩ := generic_terminal_kernel_left_inverse q hm hlo hhi Bv
  change LG*G=1 at hLG
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse (K:=K) q hlo
  obtain ⟨c,_,hc⟩ := interiorFullMinor_common_scalar r 2 q M P R hR Bv
  let e : Fin (r+2) ≃ Fin r ⊕ Fin 2 := finSumFinEquiv.symm
  obtain ⟨cT,_,hcT⟩ := polynomial_dual_basis_selected_complementary_minors
    (K:=K) G LG hLG Bt e (fun row : Fin r ⊕ Fin 2 ≃ Fin (r+2) => row)
  obtain ⟨a,b,u,v,hab,hsum,hu,hv,huv⟩ := orient_two_columns T bt (c*cT) hT hbal
  have habW : a+b=W := by
    rw [← hsumT]
    simpa [Fin.sum_univ_succ] using hsum
  have hp : ∀ row : Fin r ⊕ Fin 2 ≃ Fin (r+2),
      interiorFullMinor r 2 q M P (fun i => row (Sum.inl i)) =
        C (algebraMap K L (corankTwoRowSign (K:=K) row)) *
          (u (row (Sum.inr 0))*v (row (Sum.inr 1))-
            u (row (Sum.inr 1))*v (row (Sum.inr 0))) := by
    intro row
    rw [hc]
    change C c*(G.submatrix (fun i => row (Sum.inl i)) id).det=_
    rw [hcT row]
    simp only [Matrix.det_fin_two,Matrix.submatrix_apply,id_eq]
    rw [← huv]
    dsimp only [corankTwoRowSign,e]
    rw [Polynomial.C_mul]
    ring
  refine ⟨a,b,u,v,hab,by rw [habW]; exact hW,hu,hv,hp,?_⟩
  let rows := interiorTerminalRowEquiv r 2
  let pair : Option (Fin r × Fin 2) → Fin (r+2) × Fin (r+2) :=
    fun z => (rows z (Sum.inr 0),rows z (Sum.inr 1))
  let sign : Option (Fin r × Fin 2) → K := fun z => corankTwoRowSign (rows z)
  let p : Option (Fin r × Fin 2) → L[X] :=
    fun z => u (pair z).1*v (pair z).2-u (pair z).2*v (pair z).1
  have hselected : genericInteriorMinorVector (K:=K) r 2 q =
      fun z => C (algebraMap K L (sign z))*p z := by
    funext z
    have ht := hp (rows z)
    have hrow : (fun i => rows z (Sum.inl i))=interiorTerminalRow r 2 z := by
      funext i
      exact interiorTerminalRowEquiv_inl r 2 z i
    rw [hrow] at ht
    simpa only [interiorFullMinor,interiorFullRow_selected,genericInteriorMinorVector]
      using ht
  apply two_column_coefficient_evaluation_faithful a b hab
    (0 : Fin (r+2)) (1 : Fin (r+2)) (by simp) u v hu hv pair
  have hlower := generic_interior_minor_derivation_rank_lower_of_weight
    (K:=K) r 2 q hq W hW
  rw [hselected,polynomial_derivation_coordinate_scaling_rank sign
    (fun z => corankTwoRowSign_ne_zero (rows z)) p] at hlower
  have hb : Fintype.card (Fin (r+2))*(a+b+2)-3=(r+2)*W+r*2+1 := by
    simp only [Fintype.card_fin,habW]
    have he : (r+2)*(W+2)=(r+2)*W+r*2+4 := by ring
    omega
  rw [hb]
  exact hlower

theorem generic_corank_two_plucker_specialization_faithful (hq : 0<q) :
    ∃ (a b : ℕ) (u v : Fin (r+2) → (CorankTwoActualField (K:=K) r q)[X]),
      (b=a ∨ b=a+1) ∧ 2*(a+b)=(r+2)*q*(q+1)+2*(q+1)*r ∧
      (∀ i, (u i).natDegree≤a) ∧ (∀ i, (v i).natDegree≤b) ∧
      (∀ row : Fin r ⊕ Fin 2 ≃ Fin (r+2),
        interiorFullMinor r 2 q (genericAffineSquare K _ _) (genericAffineRows K _ _)
            (fun i => row (Sum.inl i)) =
          C (algebraMap K _ (corankTwoRowSign (K:=K) row)) *
            (u (row (Sum.inr 0))*v (row (Sum.inr 1))-
              u (row (Sum.inr 1))*v (row (Sum.inr 0)))) ∧
      Function.Injective (twoColumnMinorSpecialization a b
        (twoColumnCoefficientEvaluation (K:=K) a b u v)) := by
  let O := observabilityMatrix
    (genericAffineSquare K (Fin ((r+2)*q+r)) (Fin (r+2)))
    (genericAffineRows K (Fin ((r+2)*q+r)) (Fin (r+2))) q
  have hr := NeZero.pos r
  have hm : 2≤Fintype.card (Fin (r+2)) := by simp
  have hlo : q*Fintype.card (Fin (r+2))<Fintype.card (Fin ((r+2)*q+r)) := by
    simp only [Fintype.card_fin]; nlinarith
  have hhi : Fintype.card (Fin ((r+2)*q+r))<(q+1)*Fintype.card (Fin (r+2)) := by
    simp only [Fintype.card_fin]; nlinarith
  obtain ⟨k,Bv,av,hV,hVL,_,_⟩ := polynomial_kernel_has_minimal_basis O
  have hminV : HasMinimalKernelDegrees O (List.ofFn av) := ⟨k,Bv,av,hV,hVL,List.Perm.refl _⟩
  have hk := (generic_observability_kernel_degree_budget q hlo _ hminV).1
  simp only [List.length_ofFn,Fintype.card_fin] at hk
  have hk' : k=r := by nlinarith
  subst k
  let G := genericAffineRows K (Fin ((r+2)*q+r)) (Fin (r+2)) *
    (genericAffineSquare K (Fin ((r+2)*q+r)) (Fin (r+2)))^q *
    polynomialKernelBasisMatrix O Bv
  obtain ⟨l,Bt,bt,hT,hTL,_,_⟩ := polynomial_kernel_has_minimal_basis G.transpose
  have hminT : HasMinimalKernelDegrees G.transpose (List.ofFn bt) :=
    ⟨l,Bt,bt,hT,hTL,List.Perm.refl _⟩
  have hl := (generic_terminal_kernel_degree_budget q hm hlo hhi Bv av hV hVL _ hminT).1
  simp only [List.length_ofFn,Fintype.card_fin] at hl
  have hl' : l=2 := by omega
  subst l
  exact faithful_realization_of_bases r q hq Bv Bt av bt hV hT hVL hTL

end FD56

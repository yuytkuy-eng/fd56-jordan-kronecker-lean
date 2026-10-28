/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericInteriorDegreeBalance
import FD56.Hilbert.BalancedDegreeProfile
import FD56.Hilbert.GenericNondivisibleGLStructure

/-! The two balanced auxiliary degree lists determine every strictly
nondivisible generic GL pencil at positive depth, over every field. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000

def interiorGLDegreeList (r s q : ℕ) : List ℕ :=
  (degreeConvolution
    (balancedDegreeList ((r+s)*(q+1)*(q+2)/2) r)
    (balancedDegreeList ((r+s)*(q+1)*(q+2)/2+(q+2)*r) s)).map (fun e => e+q)

variable {K : Type*} [Field K]
variable (r s : ℕ) [NeZero r] [NeZero s]

theorem generic_interior_gl_minimal_degrees (q : ℕ) :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin ((r+s)*(q+1)+r)) (Fin (r+s)))
      (genericAffineRows K (Fin ((r+s)*(q+1)+r)) (Fin (r+s))))
      (interiorGLDegreeList r s q) := by
  have hr : 0<r := NeZero.pos r
  have hs : 0<s := NeZero.pos s
  let M := genericAffineSquare K (Fin ((r+s)*(q+1)+r)) (Fin (r+s))
  let P := genericAffineRows K (Fin ((r+s)*(q+1)+r)) (Fin (r+s))
  let O := observabilityMatrix M P (q+1)
  have hlo : (q+1)*Fintype.card (Fin (r+s))<Fintype.card (Fin ((r+s)*(q+1)+r)) := by
    simp only [Fintype.card_fin]
    nlinarith
  have hhi : Fintype.card (Fin ((r+s)*(q+1)+r))<(q+1+1)*Fintype.card (Fin (r+s)) := by
    simp only [Fintype.card_fin]
    nlinarith
  obtain ⟨k,Bv,a,hV,hVL,_,_⟩ := polynomial_kernel_has_minimal_basis O
  have hAlpha : HasMinimalKernelDegrees O (List.ofFn a) :=
    ⟨k,Bv,a,hV,hVL,List.Perm.refl _⟩
  obtain ⟨hk,ha⟩ := generic_observability_kernel_degree_budget (K:=K)
    (q+1) hlo (List.ofFn a) hAlpha
  simp only [List.length_ofFn,List.sum_ofFn,Fintype.card_fin] at hk ha
  have hkr : k=r := by nlinarith
  subst k
  let G := P*M^(q+1)*polynomialKernelBasisMatrix O Bv
  obtain ⟨l,Bt,b,hT,hTL,_,_⟩ := polynomial_kernel_has_minimal_basis G.transpose
  have hBeta : HasMinimalKernelDegrees G.transpose (List.ofFn b) :=
    ⟨l,Bt,b,hT,hTL,List.Perm.refl _⟩
  obtain ⟨hl,hb⟩ := generic_terminal_kernel_degree_budget (K:=K) (q+1)
    (by simp only [Fintype.card_fin]; omega) hlo hhi Bv a hV hVL (List.ofFn b) hBeta
  simp only [List.length_ofFn,List.sum_ofFn,Fintype.card_fin] at hl hb
  have hls : l=s := by omega
  subst l
  obtain ⟨hba,hbb⟩ := generic_interior_auxiliary_degrees_balanced (K:=K)
    r s (q+1) (by omega) Bv Bt a b hV hT hVL hTL
  have haSum : (∑ i, a i)=(r+s)*(q+1)*(q+2)/2 := by
    change 2*(∑ i, a i)=(r+s)*(q+1)*(q+2) at ha
    rw [← ha,Nat.mul_div_cancel_left _ (by decide : 0<2)]
  have hbSum : (∑ j, b j)=(r+s)*(q+1)*(q+2)/2+(q+2)*r := by
    rw [hb,haSum]
  have hpa := pairwise_balanced_degrees_perm hr a hba
  have hpb := pairwise_balanced_degrees_perm hs b hbb
  rw [haSum] at hpa
  rw [hbSum] at hpb
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse (K:=K) (q+1) hlo
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [generic_observability_gl_kernel_hilbert_of_bases q hlo.le hhi.le
    Bv Bt R hR a b hV hT hVL hTL d]
  simpa only [interiorGLDegreeList,degreeConvolution,List.map_flatMap,List.map_map,
    Function.comp_def,show ∀ x y : ℕ, x+y+1+q=x+y+q+1 by omega] using
    sum_pairs_of_permuted_degrees a b _ _ hpa hpb (fun x y => d+1-(x+y+q+1))

theorem generic_interior_gl_kronecker (q : ℕ) :
    HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K (Fin ((r+s)*(q+1)+r)) (Fin (r+s)))
      (genericAffineRows K (Fin ((r+s)*(q+1)+r)) (Fin (r+s))))
      (interiorGLDegreeList r s q) := by
  have hr : 0<r := NeZero.pos r
  have hs : 0<s := NeZero.pos s
  have hdvd : 2 ∣ (r+s)*(q+1)*(q+2) := by
    rw [Nat.mul_assoc]
    exact dvd_mul_of_dvd_right (Nat.even_mul_succ_self (q+1)).two_dvd (r+s)
  have hS : 2*((r+s)*(q+1)*(q+2)/2)=(r+s)*(q+1)*(q+2) :=
    Nat.mul_div_cancel' hdvd
  have hdim := observability_gl_dimension_budget (r+s) ((r+s)*(q+1)+r) q
    (balancedDegreeList ((r+s)*(q+1)*(q+2)/2) r)
    (balancedDegreeList ((r+s)*(q+1)*(q+2)/2+(q+2)*r) s)
    (by rw [balancedDegreeList_length _ _ hr,balancedDegreeList_length _ _ hs])
    (by rw [balancedDegreeList_length _ _ hr]; ring)
    (by rw [balancedDegreeList_sum _ _ hr]; exact hS)
    (by rw [balancedDegreeList_sum _ _ hr,balancedDegreeList_sum _ _ hs,
      balancedDegreeList_length _ _ hr])
  apply glKirillovMatrix_kronecker _ _ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
    (generic_interior_gl_minimal_degrees (K:=K) r s q)
  rw [show ((interiorGLDegreeList r s q).map (fun e => 2*e+1)).sum=
    ((r+s)*(q+1)+r)*((r+s)*(q+1)+r+(r+s)) from hdim]
  simp only [SLInput,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  ring

end FD56

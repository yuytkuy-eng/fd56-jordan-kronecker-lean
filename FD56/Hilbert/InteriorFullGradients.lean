/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.InteriorSelectedMinorFactorization
import FD56.Stabilizer.GenericMinorDifferentialImage
import FD56.Hilbert.ResidueOneAllDepthFrame

/-! Arbitrary terminal row choices give actual observability minors and
SL kernel gradients. The common scalar and degree bound are uniform in
the terminal selector, including complementary minor coordinates. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000

variable (r s q : ℕ) [NeZero r] [NeZero s]

def interiorFullRow (row : Fin r → Fin (r+s)) : Fin ((r+s)*q+r) → Fin (r+s) :=
  fun k => Sum.elim (fun t : Fin q × Fin (r+s) => t.2) row
    (interiorPrefixEquiv r s q k)

private theorem interiorFullLevel_prefix (t : Fin q) (a : Fin (r+s)) :
    interiorLevel r s q ((interiorPrefixEquiv r s q).symm (Sum.inl (t,a)))=t.val := by
  change ((r+s)*t.val+a.val)/(r+s)=t.val
  rw [Nat.mul_add_div (by have := NeZero.pos r; omega),
    Nat.div_eq_of_lt a.isLt,Nat.add_zero]

theorem interiorFullRow_lower_closed (row : Fin r → Fin (r+s)) :
    ∀ k t, t < interiorLevel r s q k → ∀ a, ∃ l,
      interiorLevel r s q l=t ∧ interiorFullRow r s q row l=a := by
  apply interior_lower_closed r s q
  intro k hk
  simp only [interiorFullRow,interiorPrefixEquiv,Equiv.coe_fn_mk,hk,↓reduceDIte,
    Sum.elim_inl,interiorBaseRow]

theorem interior_full_matrix_fromRows {R : Type*} [CommRing R]
    (M : Matrix (Fin ((r+s)*q+r)) (Fin ((r+s)*q+r)) R)
    (P : Matrix (Fin (r+s)) (Fin ((r+s)*q+r)) R) (row : Fin r → Fin (r+s)) :
    observabilitySelectedMatrix M P (interiorLevel r s q) (interiorFullRow r s q row)=
      (Matrix.fromRows (observabilityMatrix M P q)
        ((P*M^q).submatrix row id)).submatrix (interiorPrefixEquiv r s q) id := by
  funext k j
  obtain ⟨w,rfl⟩ := (interiorPrefixEquiv r s q).symm.surjective k
  rcases w with ⟨t,a⟩|a
  · simp only [observabilitySelectedMatrix,interiorFullRow,Equiv.apply_symm_apply,
      Sum.elim_inl,interiorFullLevel_prefix,Matrix.submatrix_apply,
      Matrix.fromRows_apply_inl,observabilityMatrix,id_eq]
  · simp only [observabilitySelectedMatrix,interiorFullRow,Equiv.apply_symm_apply,
      Sum.elim_inr,interiorPrefixEquiv_symm_inr,interiorLevel_missing,
      interiorPrefixEquiv_missing,Matrix.submatrix_apply,Matrix.fromRows_apply_inr,id_eq]

theorem interiorFullRow_selected (z : Option (Fin r × Fin s)) :
    interiorFullRow r s q (interiorTerminalRow r s z)=interiorSelectorRow r s q z := by
  funext k
  obtain ⟨w,rfl⟩ := (interiorPrefixEquiv r s q).symm.surjective k
  rcases w with ⟨t,a⟩|a
  · have hn (b : Fin r) : (interiorPrefixEquiv r s q).symm (Sum.inl (t,a))≠
        interiorMissing r s q b := by
      intro he
      have hh := congrArg Fin.val he
      dsimp [interiorPrefixEquiv,interiorMissing] at hh
      nlinarith [t.isLt,a.isLt]
    have hbase : interiorBaseRow r s q
        ((interiorPrefixEquiv r s q).symm (Sum.inl (t,a)))=a := by
      apply Fin.ext
      simp [interiorBaseRow,interiorPrefixEquiv,Nat.add_mod,Nat.mod_eq_of_lt a.isLt]
    cases z with
    | none => simpa [interiorFullRow,interiorSelectorRow] using hbase.symm
    | some ab => simpa [interiorFullRow,interiorSelectorRow,interiorSwapRow,hn] using hbase.symm
  · simp only [interiorFullRow,Equiv.apply_symm_apply,Sum.elim_inr,
      interiorPrefixEquiv_symm_inr,interiorSelectorRow_terminal,interiorPrefixEquiv_missing]

def interiorFullMinor {R : Type*} [CommRing R]
    (M : Matrix (Fin ((r+s)*q+r)) (Fin ((r+s)*q+r)) R)
    (P : Matrix (Fin (r+s)) (Fin ((r+s)*q+r)) R) (row : Fin r → Fin (r+s)) : R :=
  (observabilitySelectedMatrix M P (interiorLevel r s q) (interiorFullRow r s q row)).det

def interiorFullGradient {R : Type*} [CommRing R]
    (M : Matrix (Fin ((r+s)*q+r)) (Fin ((r+s)*q+r)) R)
    (P : Matrix (Fin (r+s)) (Fin ((r+s)*q+r)) R) (row : Fin r → Fin (r+s)) :
    SLInput (Fin ((r+s)*q+r)) (Fin (r+s)) → R :=
  observabilityScalarLift M P (interiorLevel r s q) (interiorFullRow r s q row)

theorem interiorFullGradient_kernel {K : Type*} [Field K]
    (M : Matrix (Fin ((r+s)*q+r)) (Fin ((r+s)*q+r)) K[X])
    (P : Matrix (Fin (r+s)) (Fin ((r+s)*q+r)) K[X])
    (row : Fin r → Fin (r+s)) (i₀ : Fin ((r+s)*q+r)) :
    slEquationMatrix M P i₀ *ᵥ interiorFullGradient r s q M P row=0 :=
  observabilityScalarLift_sl_kernel M P (interiorLevel r s q)
    (interiorFullRow r s q row) (interiorFullRow_lower_closed r s q row) i₀

theorem interiorFullMinor_common_scalar {K : Type*} [Field K]
    (M : Matrix (Fin ((r+s)*q+r)) (Fin ((r+s)*q+r)) K[X])
    (P : Matrix (Fin (r+s)) (Fin ((r+s)*q+r)) K[X])
    (R : Matrix (Fin ((r+s)*q+r)) (Fin q × Fin (r+s)) K[X])
    (hR : observabilityMatrix M P q*R=1)
    (B : Basis (Fin r) K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q)))) :
    ∃ c : K, c≠0 ∧ ∀ row : Fin r → Fin (r+s),
      interiorFullMinor r s q M P row=
        C c*pluckerMinorVector (P*M^q*polynomialKernelBasisMatrix _ B) row := by
  obtain ⟨c,hc,h⟩ := selected_augmented_minors_common_scalar_equiv
    (interiorPrefixEquiv r s q) (observabilityMatrix M P q) R hR B (P*M^q)
  refine ⟨c,hc,?_⟩
  intro row
  simpa only [interiorFullMinor,interior_full_matrix_fromRows] using h row

def interiorFullWeight : ℕ := ((r+s)*q*(q+1)+2*r*(q+1))/2

theorem interior_full_row_weight :
    (∑ k : Fin ((r+s)*q+r), (interiorLevel r s q k+1))=interiorFullWeight r s q := by
  have hs : 2*(∑ k : Fin ((r+s)*q+r), (interiorLevel r s q k+1))=
      (r+s)*q*(q+1)+2*r*(q+1) := by
    simp only [interiorLevel]
    rw [Fin.sum_univ_add]
    simp only [Fin.coe_castAdd,Fin.coe_natAdd]
    have ht (i : Fin r) : ((r+s)*q+i.val)/(r+s)=q := by
      rw [Nat.mul_add_div (by have := NeZero.pos r; omega),
        Nat.div_eq_of_lt (by have := i.isLt; omega),Nat.add_zero]
    simp_rw [ht]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    letI : NeZero (r+s) := ⟨by have := NeZero.pos r; omega⟩
    nlinarith [residueOne_prefix_row_weight (r+s) q]
  unfold interiorFullWeight
  omega

theorem interiorFullWeight_pos : 0 < interiorFullWeight r s q := by
  have hr := NeZero.pos r
  unfold interiorFullWeight
  have : 2≤(r+s)*q*(q+1)+2*r*(q+1) := by
    nlinarith [Nat.zero_le (r*q),Nat.zero_le ((r+s)*q*(q+1))]
  omega

theorem interiorFullGradient_degree {K : Type*} [Field K]
    (M : Matrix (Fin ((r+s)*q+r)) (Fin ((r+s)*q+r)) K[X])
    (P : Matrix (Fin (r+s)) (Fin ((r+s)*q+r)) K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (row : Fin r → Fin (r+s)) :
    ∀ k, (interiorFullGradient r s q M P row k).natDegree ≤ interiorFullWeight r s q-1 := by
  intro k
  have he : (∑ k : Fin ((r+s)*q+r), (interiorLevel r s q k+1))=
      interiorFullWeight r s q-1+1 := by
    rw [interior_full_row_weight]
    have := interiorFullWeight_pos r s q
    omega
  obtain ⟨hX,hU,_⟩ := observability_adjugate_solution_degree M P hM hP
    (interiorLevel r s q) (interiorFullRow r s q row) (interiorFullWeight r s q-1) he
  rcases k with ab|ab
  · exact hX ab.1 ab.2
  · exact hU ab.1 ab.2

theorem generic_interior_full_gradient_derivation {K : Type*} [Field K]
    (t : SLInput (Fin ((r+s)*q+r)) (Fin (r+s))) :
    ∃ D : Derivation K (AffineCoefficientField K
        (MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s))))
        (AffineCoefficientField K (MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s)))),
      ∀ row, polynomialCoefficientDerivation D
          (interiorFullMinor r s q (genericAffineSquare K _ _) (genericAffineRows K _ _) row)=
        interiorFullGradient r s q (genericAffineSquare K _ _) (genericAffineRows K _ _) row t := by
  classical
  let L := AffineCoefficientField K (MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s)))
  obtain ⟨D,hD⟩ := generic_minor_derivation_realizes_affine_pairing (K:=K)
    (fun _ : Fin r → Fin (r+s) => interiorLevel r s q)
    (interiorFullRow r s q) (Pi.single t (1:L)) 0
  refine ⟨D,?_⟩
  intro row
  simpa [interiorFullMinor,interiorFullGradient,Pi.single_apply,dotProduct] using hD row

end FD56

/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.Basis
import FD56.Hilbert.BetaKernel
import FD56.Stabilizer.StructuredLeading

/-! In the first middle range, actual auxiliary polynomial kernel bases
give a full basis of the GL stabilizer kernel. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m r s : Type*} [Field K]
  [Fintype n] [Fintype m] [Fintype r] [Fintype s]
  [DecidableEq n] [DecidableEq m] [DecidableEq r] [DecidableEq s]

theorem polynomialKernelBasisMatrix_injective {a b k : Type*}
    [Fintype b] [DecidableEq b] [Fintype k]
    (A : Matrix a b K[X]) (B : Basis k K[X] (LinearMap.ker (Matrix.toLin' A))) :
    Function.Injective (polynomialKernelBasisMatrix A B).mulVec := by
  intro c d h
  rw [polynomialKernelBasisMatrix_mulVec, polynomialKernelBasisMatrix_mulVec] at h
  exact B.equivFun.symm.injective (Subtype.ext h)

theorem matrix_left_mul_injective_of_mulVec {R a b c : Type*} [Semiring R]
    [Fintype b] (A : Matrix a b R) (hA : Function.Injective A.mulVec) :
    Function.Injective (fun Z : Matrix b c R => A * Z) := by
  intro Z W h
  funext i j
  have hh : (fun i => Z i j) = (fun i => W i j) := by
    apply hA
    funext x
    exact congrFun (congrFun h x) j
  exact congrFun hh i

theorem matrix_factor_through_kernel_basis {a b c k : Type*}
    [Fintype b] [DecidableEq b] [Fintype k]
    (A : Matrix a b K[X]) (B : Basis k K[X] (LinearMap.ker (Matrix.toLin' A)))
    (Y : Matrix b c K[X]) (hY : A * Y = 0) :
    ∃ C : Matrix k c K[X], Y = polynomialKernelBasisMatrix A B * C := by
  let y : c → LinearMap.ker (Matrix.toLin' A) := fun j =>
    ⟨fun i => Y i j, by funext i; exact congrFun (congrFun hY i) j⟩
  refine ⟨fun i j => B.equivFun (y j) i, ?_⟩
  funext i j
  have hh := polynomialKernelBasisMatrix_mulVec A B (B.equivFun (y j))
  rw [B.equivFun.symm_apply_apply] at hh
  exact (congrFun hh i).symm

def middleGLColumns (M : Matrix n n K[X]) (V : Matrix n r K[X])
    (P : Matrix m n K[X]) (T D : Matrix s m K[X]) :
    Matrix (SLInput n m) (r × s) K[X] :=
  structuredColumns M V (fun _ => T * P) (fun _ => D) T 0

omit [DecidableEq r] [DecidableEq s] in
theorem tensorColumns_mulVec {R a b : Type*} [CommRing R]
    (A : Matrix a r R) (H : Matrix s b R) (c : r × s → R) :
    (show Matrix (a × b) (r × s) R from fun xy kj => A xy.1 kj.1 * H kj.2 xy.2) *ᵥ c =
      (fun xy => (A * (show Matrix r s R from fun i j => c (i,j)) * H) xy.1 xy.2) := by
  funext xy
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [DecidableEq m] [DecidableEq r] [DecidableEq s] in
theorem middleGLColumns_mulVec (M : Matrix n n K[X]) (V : Matrix n r K[X])
    (P : Matrix m n K[X]) (T D : Matrix s m K[X]) (c : r × s → K[X]) :
    matrixPairEquiv K[X] K[X] n m (middleGLColumns M V P T D *ᵥ c) =
      (V * (show Matrix r s K[X] from fun i j => c (i,j)) * T * P,
        M * V * (show Matrix r s K[X] from fun i j => c (i,j)) * T -
          V * (show Matrix r s K[X] from fun i j => c (i,j)) * D) := by
  apply Prod.ext
  · funext x y
    simp only [matrixPairEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk,
      AddHom.coe_mk, middleGLColumns, structuredColumns, structuredXColumns,
      Matrix.mulVec, dotProduct, Sum.elim_inl, Nat.zero_add, Finset.range_one,
      Finset.sum_singleton, pow_zero, Matrix.one_mul]
    change (∑ k, (V x k.1 * (T * P) k.2 y) * c k) = _
    have hh := congrFun (tensorColumns_mulVec V (T * P) c) (x,y)
    simpa only [Matrix.mulVec, dotProduct, Matrix.mul_assoc] using hh
  · funext x y
    simp only [matrixPairEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk,
      AddHom.coe_mk, middleGLColumns, structuredColumns, Sum.elim_inr,
      Matrix.mulVec, dotProduct, Nat.zero_add, Finset.range_one, Finset.sum_singleton,
      pow_zero, pow_one, Matrix.one_mul]
    change (∑ k, ((M * V) x k.1 * T k.2 y - V x k.1 * D k.2 y) * c k) = _
    simp only [sub_mul, Finset.sum_sub_distrib, Matrix.sub_apply]
    exact congrArg₂ (fun a b : K[X] => a - b)
      (congrFun (tensorColumns_mulVec (M * V) T c) (x,y))
      (congrFun (tensorColumns_mulVec V D c) (x,y))

theorem middleGLColumns_equations (M : Matrix n n K[X]) (V : Matrix n r K[X])
    (P : Matrix m n K[X]) (T D : Matrix s m K[X])
    (hPV : P * V = 0) (hDP : T * P * M = D * P) :
    glEquationMatrix M P * middleGLColumns M V P T D = 0 := by
  apply structuredColumns_gl_equations M P V (fun _ => T * P) (fun _ => D) T 0 hDP
  · intro i hi; omega
  · rfl
  · intro i hi
    have hi0 : i = 0 := by omega
    simpa [hi0] using hPV

def middleGLMap (M : Matrix n n K[X]) (V : Matrix n r K[X])
    (P : Matrix m n K[X]) (T D : Matrix s m K[X])
    (hPV : P * V = 0) (hDP : T * P * M = D * P) :
    (r × s → K[X]) →ₗ[K[X]] LinearMap.ker (Matrix.toLin' (glEquationMatrix M P)) :=
  (Matrix.toLin' (middleGLColumns M V P T D)).codRestrict _ (by
    intro c
    change glEquationMatrix M P *ᵥ (middleGLColumns M V P T D *ᵥ c) = 0
    rw [Matrix.mulVec_mulVec, middleGLColumns_equations M V P T D hPV hDP,
      Matrix.zero_mulVec])

theorem middleGLMap_bijective
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (Bt : Basis s K[X] (LinearMap.ker (Matrix.toLin'
      (P * M * polynomialKernelBasisMatrix P Bv).transpose)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (D : Matrix s m K[X])
    (hDP : (polynomialKernelBasisMatrix _ Bt).transpose * P * M = D * P)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P Bv).mulVec) :
    Function.Bijective (middleGLMap M (polynomialKernelBasisMatrix P Bv) P
      (polynomialKernelBasisMatrix _ Bt).transpose D (polynomialKernelBasisMatrix_mul P Bv) hDP) := by
  let V := polynomialKernelBasisMatrix P Bv
  let T := (polynomialKernelBasisMatrix (P * M * V).transpose Bt).transpose
  have hV := polynomialKernelBasisMatrix_injective P Bv
  have hT : Function.Injective T.transpose.mulVec := by
    simpa [T] using polynomialKernelBasisMatrix_injective (P * M * V).transpose Bt
  have hPV : P * V = 0 := polynomialKernelBasisMatrix_mul P Bv
  constructor
  · intro c d h
    have hp := congrArg (fun z : LinearMap.ker (Matrix.toLin' (glEquationMatrix M P)) =>
      matrixPairEquiv K[X] K[X] n m z.val) h
    change matrixPairEquiv _ _ _ _ (middleGLColumns M V P T D *ᵥ c) =
      matrixPairEquiv _ _ _ _ (middleGLColumns M V P T D *ᵥ d) at hp
    rw [middleGLColumns_mulVec, middleGLColumns_mulVec] at hp
    have hx := congrArg Prod.fst hp
    have hx' := congrArg (fun Z : Matrix n n K[X] => Z * R) hx
    simp only [Matrix.mul_assoc, hPR, Matrix.mul_one] at hx'
    have hc := matrix_left_mul_injective_of_mulVec V hV hx'
    have ht := congrArg Matrix.transpose hc
    simp only [Matrix.transpose_mul] at ht
    have he := matrix_left_mul_injective_of_mulVec T.transpose hT ht
    funext k
    exact congrFun (congrFun he k.2) k.1
  · intro z
    let X := (matrixPairEquiv K[X] K[X] n m z.val).1
    let U := (matrixPairEquiv K[X] K[X] n m z.val).2
    obtain ⟨hPX, hres⟩ := (glEquationMatrix_kernel_iff M P z.val).mp z.property
    change P * X = 0 at hPX
    change M * X - X * M - U * P = 0 at hres
    have hcomm : M * X - X * M = U * P := sub_eq_zero.mp hres
    obtain ⟨C, hC⟩ := matrix_factor_through_kernel_basis P Bv X hPX
    change X = V * C at hC
    have hGC : (P * M * V) * (C * V) = 0 := by
      have hh := congrArg (fun Z : Matrix n n K[X] => P * Z * V) hcomm
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hPV,
        Matrix.mul_zero] at hh
      rw [← Matrix.mul_assoc P X, hPX, Matrix.zero_mul, sub_zero] at hh
      simpa only [hC, Matrix.mul_assoc] using hh
    have hCV : C * V = 0 := matrix_left_mul_injective_of_mulVec _ hG
      (hGC.trans (Matrix.mul_zero _).symm)
    have hCP : C = (C * R) * P := row_factor_through_of_kernel_basis P Bv R hPR C hCV
    let E := C * R
    have hXE : X = V * E * P := by rw [hC, hCP]; simp only [E, Matrix.mul_assoc]
    have hEG : E * (P * M * V) = 0 := by
      have hh := congrArg (fun Z : Matrix n n K[X] => Z * V) hcomm
      simp only [Matrix.sub_mul, Matrix.mul_assoc, hPV, Matrix.mul_zero] at hh
      have hXV : X * V = 0 := by rw [hXE]; simp [Matrix.mul_assoc, hPV]
      rw [hXV, Matrix.mul_zero, zero_sub, neg_eq_zero] at hh
      have hv : V * (E * (P * M * V)) = 0 := by
        simpa only [hXE, Matrix.mul_assoc] using hh
      exact matrix_left_mul_injective_of_mulVec V hV (hv.trans (Matrix.mul_zero _).symm)
    have hEt : (P * M * V).transpose * E.transpose = 0 := by
      simpa only [Matrix.transpose_mul, Matrix.transpose_zero] using congrArg Matrix.transpose hEG
    obtain ⟨Q, hQ⟩ := matrix_factor_through_kernel_basis (P * M * V).transpose Bt E.transpose hEt
    have hE : E = Q.transpose * T := by
      have hh := congrArg Matrix.transpose hQ
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using hh
    let c : r × s → K[X] := fun k => Q k.2 k.1
    have hx : V * (show Matrix r s K[X] from fun i j => c (i,j)) * T * P = X := by
      change V * Q.transpose * T * P = X
      rw [Matrix.mul_assoc V, ← hE, ← hXE]
    have hu : M * V * (show Matrix r s K[X] from fun i j => c (i,j)) * T -
        V * (show Matrix r s K[X] from fun i j => c (i,j)) * D = U := by
      have hp : (M * V * Q.transpose * T - V * Q.transpose * D) * P = U * P := by
        rw [Matrix.sub_mul]
        have hfirst : M * V * Q.transpose * T * P = M * X := by
          rw [← hx]; simp only [Matrix.mul_assoc]; rfl
        have hsecond : V * Q.transpose * D * P = X * M := by
          rw [Matrix.mul_assoc, ← hDP, ← hx]
          simp only [Matrix.mul_assoc]
          rfl
        rw [hfirst, hsecond, hcomm]
      have hh := congrArg (fun Z : Matrix n n K[X] => Z * R) hp
      simpa only [Matrix.mul_assoc, hPR, Matrix.mul_one] using hh
    refine ⟨c, ?_⟩
    apply Subtype.ext
    apply (matrixPairEquiv K[X] K[X] n m).injective
    change matrixPairEquiv _ _ _ _ (middleGLColumns M V P T D *ᵥ c) = _
    rw [middleGLColumns_mulVec, hx, hu]

def middleGLKernelBasis
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (Bt : Basis s K[X] (LinearMap.ker (Matrix.toLin'
      (P * M * polynomialKernelBasisMatrix P Bv).transpose)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (D : Matrix s m K[X])
    (hDP : (polynomialKernelBasisMatrix _ Bt).transpose * P * M = D * P)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P Bv).mulVec) :
    Basis (r × s) K[X] (LinearMap.ker (Matrix.toLin' (glEquationMatrix M P))) :=
  (Pi.basisFun K[X] (r × s)).map (LinearEquiv.ofBijective
    (middleGLMap M (polynomialKernelBasisMatrix P Bv) P
      (polynomialKernelBasisMatrix _ Bt).transpose D (polynomialKernelBasisMatrix_mul P Bv) hDP)
    (middleGLMap_bijective M P Bv Bt R hPR D hDP hG))

theorem polynomialKernelBasisMatrix_middleGL
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (Bt : Basis s K[X] (LinearMap.ker (Matrix.toLin'
      (P * M * polynomialKernelBasisMatrix P Bv).transpose)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (D : Matrix s m K[X])
    (hDP : (polynomialKernelBasisMatrix _ Bt).transpose * P * M = D * P)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P Bv).mulVec) :
    polynomialKernelBasisMatrix (glEquationMatrix M P)
      (middleGLKernelBasis M P Bv Bt R hPR D hDP hG) =
      middleGLColumns M (polynomialKernelBasisMatrix P Bv) P
        (polynomialKernelBasisMatrix _ Bt).transpose D := by
  funext i j
  change (middleGLColumns M (polynomialKernelBasisMatrix P Bv) P
    (polynomialKernelBasisMatrix _ Bt).transpose D *ᵥ (Pi.basisFun K[X] (r × s) j)) i = _
  simp [Pi.basisFun_apply, Matrix.mulVec_single]

omit [DecidableEq r] [DecidableEq s] in
theorem tensorColumns_injective {R a b : Type*} [CommRing R]
    [Fintype b] (A : Matrix a r R) (H : Matrix s b R)
    (hA : Function.Injective A.mulVec) (hH : Function.Injective H.transpose.mulVec) :
    Function.Injective (Matrix.mulVec
      (show Matrix (a × b) (r × s) R from fun xy kj => A xy.1 kj.1 * H kj.2 xy.2)) := by
  intro c d h
  rw [tensorColumns_mulVec, tensorColumns_mulVec] at h
  have hm : A * (show Matrix r s R from fun i j => c (i,j)) * H =
      A * (show Matrix r s R from fun i j => d (i,j)) * H := by
    funext x y
    exact congrFun h (x,y)
  simp only [Matrix.mul_assoc] at hm
  have hh := congrArg Matrix.transpose (matrix_left_mul_injective_of_mulVec A hA hm)
  simp only [Matrix.transpose_mul] at hh
  have he := matrix_left_mul_injective_of_mulVec H.transpose hH hh
  funext k
  exact congrFun (congrFun he k.2) k.1

omit [Fintype r] [Fintype s] [DecidableEq m] [DecidableEq r] [DecidableEq s] in
theorem middleGLColumns_degree
    (M : Matrix n n K[X]) (V : Matrix n r K[X])
    (P : Matrix m n K[X]) (T D : Matrix s m K[X]) (a : r → ℕ) (b : s → ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x k, (V x k).natDegree ≤ a k)
    (hT : ∀ j y, (T j y).natDegree ≤ b j)
    (hDP : T * P * M = D * P)
    (hPlead : Function.Injective (matrixCoeff P 1).transpose.mulVec) :
    ∀ xy kj, (middleGLColumns M V P T D xy kj).natDegree ≤ a kj.1 + b kj.2 + 1 := by
  have hH := matrix_mul_row_degree T P b 1 hT hP
  have hprod := matrix_mul_row_degree (T * P) M (fun j => b j + 1) 1 hH hM
  rw [hDP] at hprod
  have hDb := row_coordinates_degree_bound P D (fun _ => 1) (fun j => b j + 1 + 1)
    hP hPlead hprod
  have hD : ∀ j y, (D j y).natDegree ≤ b j + 1 := by
    intro j y
    rcases hDb j y with hz | ⟨_, hb⟩
    · simp [hz]
    · change (D j y).natDegree ≤ b j + 1 + 1 - 1 at hb
      omega
  simpa only [middleGLColumns, Nat.add_zero, Nat.sub_zero] using
    structuredColumns_degree M V (fun _ => T * P) (fun _ => D) T 0 a b hM hV
      (by
        intro i hi j y
        have hi0 : i = 0 := by omega
        simpa [hi0] using hH j y)
      (by
        intro i hi j y
        have hi0 : i = 0 := by omega
        simpa [hi0] using hD j y) hT

omit [DecidableEq m] [DecidableEq r] [DecidableEq s] in
theorem middleGLColumns_leading_injective
    (M : Matrix n n K[X]) (V : Matrix n r K[X])
    (P : Matrix m n K[X]) (T D : Matrix s m K[X]) (a : r → ℕ) (b : s → ℕ)
    (hP : DegreeBound P 1) (hV : ∀ x k, (V x k).natDegree ≤ a k)
    (hT : ∀ j y, (T j y).natDegree ≤ b j)
    (hVlead : Function.Injective (Matrix.mulVec (fun x k => (V x k).coeff (a k))))
    (hTlead : Function.Injective (Matrix.mulVec (fun y j => (T j y).coeff (b j))))
    (hPlead : Function.Injective (matrixCoeff P 1).transpose.mulVec) :
    Function.Injective (Matrix.mulVec (fun xy kj =>
      (middleGLColumns M V P T D xy kj).coeff (a kj.1 + b kj.2 + 1))) := by
  let V₀ : Matrix n r K := fun x k => (V x k).coeff (a k)
  let T₀ : Matrix s m K := fun j y => (T j y).coeff (b j)
  let H₀ : Matrix s n K := T₀ * matrixCoeff P 1
  have hH : Function.Injective H₀.transpose.mulVec := by
    intro c d h
    change ((T₀ * matrixCoeff P 1).transpose) *ᵥ c = _ at h
    rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h
    exact hTlead (hPlead h)
  have hi := tensorColumns_injective V₀ H₀ hVlead hH
  have hprod : ∀ j y, ((T * P) j y).natDegree ≤ b j + 1 :=
    matrix_mul_row_degree T P b 1 hT hP
  have hcoeff (j : s) (y : n) : ((T * P) j y).coeff (b j + 1) = H₀ j y := by
    simp only [H₀, T₀, Matrix.mul_apply, Polynomial.finset_sum_coeff, matrixCoeff]
    apply Finset.sum_congr rfl
    intro z _
    exact Polynomial.coeff_mul_add_eq_of_natDegree_le (hT j z) (hP z y)
  intro c d h
  apply hi
  funext xy
  have hh := congrFun h (Sum.inl xy)
  have he (kj : r × s) :
      (middleGLColumns M V P T D (Sum.inl xy) kj).coeff (a kj.1 + b kj.2 + 1) =
        V₀ xy.1 kj.1 * H₀ kj.2 xy.2 := by
    simp only [middleGLColumns, structuredColumns, Sum.elim_inl, structuredXColumns,
      Nat.zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, Matrix.one_mul]
    rw [show a kj.1 + b kj.2 + 1 = a kj.1 + (b kj.2 + 1) by omega,
      Polynomial.coeff_mul_add_eq_of_natDegree_le (hV xy.1 kj.1) (hprod kj.2 xy.2), hcoeff]
  simpa only [Matrix.mulVec, dotProduct, he] using hh

theorem middle_gl_kernel_hilbert
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (Bt : Basis s K[X] (LinearMap.ker (Matrix.toLin'
      (P * M * polynomialKernelBasisMatrix P Bv).transpose)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (D : Matrix s m K[X])
    (hDP : (polynomialKernelBasisMatrix _ Bt).transpose * P * M = D * P)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P Bv).mulVec)
    (a : r → ℕ) (b : s → ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x k, (polynomialKernelBasisMatrix P Bv x k).natDegree ≤ a k)
    (hT : ∀ y j, (polynomialKernelBasisMatrix _ Bt y j).natDegree ≤ b j)
    (hVlead : Function.Injective (Matrix.mulVec
      (fun x k => (polynomialKernelBasisMatrix P Bv x k).coeff (a k))))
    (hTlead : Function.Injective (Matrix.mulVec
      (fun y j => (polynomialKernelBasisMatrix _ Bt y j).coeff (b j))))
    (hPlead : Function.Injective (matrixCoeff P 1).transpose.mulVec) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d) =
      ∑ kj : r × s, (d + 1 - (a kj.1 + b kj.2 + 1)) := by
  apply polynomial_kernel_basis_hilbert (glEquationMatrix M P)
    (middleGLKernelBasis M P Bv Bt R hPR D hDP hG) (fun kj => a kj.1 + b kj.2 + 1) d
  · rw [polynomialKernelBasisMatrix_middleGL]
    exact middleGLColumns_degree M _ P _ D a b hM hP hV (fun j y => hT y j) hDP hPlead
  · rw [polynomialKernelBasisMatrix_middleGL]
    exact middleGLColumns_leading_injective M _ P _ D a b hP hV (fun j y => hT y j)
      hVlead hTlead hPlead

theorem middle_gl_kernel_hilbert_of_bases
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (Bt : Basis s K[X] (LinearMap.ker (Matrix.toLin'
      (P * M * polynomialKernelBasisMatrix P Bv).transpose)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P Bv).mulVec)
    (a : r → ℕ) (b : s → ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x k, (polynomialKernelBasisMatrix P Bv x k).natDegree ≤ a k)
    (hT : ∀ y j, (polynomialKernelBasisMatrix _ Bt y j).natDegree ≤ b j)
    (hVlead : Function.Injective (Matrix.mulVec
      (fun x k => (polynomialKernelBasisMatrix P Bv x k).coeff (a k))))
    (hTlead : Function.Injective (Matrix.mulVec
      (fun y j => (polynomialKernelBasisMatrix _ Bt y j).coeff (b j))))
    (hPlead : Function.Injective (matrixCoeff P 1).transpose.mulVec) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d) =
      ∑ kj : r × s, (d + 1 - (a kj.1 + b kj.2 + 1)) := by
  let V := polynomialKernelBasisMatrix P Bv
  let T := (polynomialKernelBasisMatrix (P * M * V).transpose Bt).transpose
  have hTG : T * (P * M * V) = 0 := by
    have hh := congrArg Matrix.transpose (polynomialKernelBasisMatrix_mul (P * M * V).transpose Bt)
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using hh
  have hDP := beta_relation_of_kernel_basis M P Bv R hPR T hTG
  exact middle_gl_kernel_hilbert M P Bv Bt R hPR (T * P * M * R) hDP hG a b
    hM hP hV hT hVlead hTlead hPlead d

end FD56

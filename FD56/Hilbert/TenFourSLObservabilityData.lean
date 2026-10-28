/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ObservabilityMatrix

/-! Small integer inverse certificates for the ten-state, four-output SL witness. -/

namespace FD56
open Matrix
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option Elab.async false

def tenFourM0Integer : Matrix (Fin 10) (Fin 10) ℤ :=
  ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def tenFourP0Integer : Matrix (Fin 4) (Fin 10) ℤ :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, -1, 0], ![0, 1, 0, 0, -1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1]]

def tenFourO2RightIntegerData : Matrix (Fin 10) (Fin 8) ℤ :=
  ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]

def tenFourO3LeftIntegerData : Matrix (Fin 10) (Fin 12) ℤ :=
  ![![1, 0, 1, -1, 0, 0, 0, 0, 1, -1, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 1, -1, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, -1, 0, 0, 0, 0, 1, -1, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0]]

def tenFourO2RightInteger : Matrix (Fin 10) (Fin 2 × Fin 4) ℤ :=
  fun i j => tenFourO2RightIntegerData i ⟨4*j.1.val+j.2.val,by omega⟩

def tenFourO3LeftInteger : Matrix (Fin 10) (Fin 3 × Fin 4) ℤ :=
  fun i j => tenFourO3LeftIntegerData i ⟨4*j.1.val+j.2.val,by omega⟩

private theorem tenFour_observability_two_integer_inverse :
    observabilityMatrix tenFourM0Integer tenFourP0Integer 2*tenFourO2RightInteger=1 := by
  decide

private theorem tenFour_observability_three_integer_inverse :
    tenFourO3LeftInteger*observabilityMatrix tenFourM0Integer tenFourP0Integer 3=1 := by
  decide

noncomputable section
variable {K : Type*} [CommRing K]

def tenFourM0 : Matrix (Fin 10) (Fin 10) K := tenFourM0Integer.map (Int.castRingHom K)
def tenFourP0 : Matrix (Fin 4) (Fin 10) K := tenFourP0Integer.map (Int.castRingHom K)
def tenFourO2Right : Matrix (Fin 10) (Fin 2 × Fin 4) K :=
  tenFourO2RightInteger.map (Int.castRingHom K)
def tenFourO3Left : Matrix (Fin 10) (Fin 3 × Fin 4) K :=
  tenFourO3LeftInteger.map (Int.castRingHom K)

theorem tenFour_observability_two_right_inverse :
    observabilityMatrix (tenFourM0 (K:=K)) tenFourP0 2*tenFourO2Right (K:=K)=1 := by
  have h := congrArg (fun A => A.map (Int.castRingHom K)) tenFour_observability_two_integer_inverse
  simpa only [Matrix.map_mul,observabilityMatrix_map,Matrix.map_one,map_zero,map_one]
    using h

theorem tenFour_observability_three_left_inverse :
    tenFourO3Left (K:=K)*observabilityMatrix (tenFourM0 (K:=K)) tenFourP0 3=1 := by
  have h := congrArg (fun A => A.map (Int.castRingHom K)) tenFour_observability_three_integer_inverse
  simpa only [Matrix.map_mul,observabilityMatrix_map,Matrix.map_one,map_zero,map_one]
    using h

end
end FD56

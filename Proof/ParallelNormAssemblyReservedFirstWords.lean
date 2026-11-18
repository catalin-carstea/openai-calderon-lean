import Proof.ParallelNormAssemblyReservedNormalizedWords
import Proof.ParallelNormAssemblyReservedCoordinateError
import Proof.PrincipalModelCoordinateContraction
import Proof.PrincipalFirstCorrectionCoordinateContraction
import Proof.FirstCovariantCoordinateAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The complete first-base coefficient's degree/raising/native-error
word coefficients in the same radius-normalized coordinate generators. -/
def effectiveFirstWordCoefficient (d : Data) (b : I) (y : X) : PhysicalPotentialGeneratorIndex → ℝ
  | .inl _ => principalModelDegreeCoordinateWeight d b y
  | .inr (.inl a) => principalModelRaisingCoordinateWeight d a b y
  | .inr (.inr a) => d.radius y*principalFirstErrorCoordinateWeight d a b y

/-- Explicit bounded geometric correction and scalar connection drift;
these are retained alongside, rather than absorbed into, the angular words. -/
def effectiveFirstBoundedRemainderHalfL (d : Data) (b : I) (y : X) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  principalFirstCorrectionCoordinateHalfL d y b-scalarPrincipalConnectionWeight d b y •
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)

/-- Exact decomposition of the SAME complete effective first coefficient
into the potential's coordinate generators plus its genuine bounded
geometric correction and scalar drift. -/
theorem effective_first_normalized_word_split {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε CF CT : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y) (b : I) :
    P.firstCovariantCoordinateHalfL b y=
      (∑ a : PhysicalPotentialGeneratorIndex,effectiveFirstWordCoefficient d b y a •
        normalizedPotentialGeneratorLow P y a)+effectiveFirstBoundedRemainderHalfL d b y := by
  have he := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hr := (hd.2.2.2.2.1.2 y hy).1.ne'
  have hE := P.first.principalFirstErrorCoordinateHalfL_eq
    (fun a x => potentialCoordinateGeneratorLow P x (.inr (.inr a))) hy he
    (fun a => coordinate_error_low_coarse P hy he a) b
  rw [PhysicalPrincipalData.firstCovariantCoordinateHalfL,
    P.firstDerivativeCoordinateHalfL_correction_split y b,
    hd.principalModelFirstDerivative_coordinate_eq hY hy b,hE]
  have hScale (a : I) :
      (d.radius y*principalFirstErrorCoordinateWeight d a b y) •
        ((d.radius y)⁻¹ • potentialCoordinateGeneratorLow P y (.inr (.inr a)))=
      principalFirstErrorCoordinateWeight d a b y • potentialCoordinateGeneratorLow P y (.inr (.inr a)) := by
    rw [smul_smul]
    congr 1
    field_simp
  simp only [effectiveFirstWordCoefficient,effectiveFirstBoundedRemainderHalfL,
    Fintype.sum_sum_type,Fintype.sum_unique,normalizedPotentialGeneratorLow,
    potentialGeneratorWeight,inv_one,one_smul]
  simp only [hScale]
  simp only [potentialCoordinateGeneratorLow,principalFirstErrorCoordinateWeight,Fin.sum_univ_three,degreeHalfL]
  module

end ShrinkingSpheres.ParallelEnergy

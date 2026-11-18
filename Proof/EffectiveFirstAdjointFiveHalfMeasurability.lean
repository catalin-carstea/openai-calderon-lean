import Proof.EffectiveFirstAdjointFiveHalf
import Proof.EffectiveFirstCovariantCoarseBridge
import Proof.SobolevCoefficientMeasurability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def PhysicalPrincipalData.firstCovariantAdjointFiveHalfSection
    {Y : Set X} {d : Data} {CF CT CG CK : ℝ} (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (b : I) : X → SphereSobolev (3/2:ℝ) := by
  classical
  exact fun y => if hy : y ∈ Y then P.firstCovariantCoordinateAdjointFiveHalfL (W y hy) b (U y) else 0

/-- The selected high core is measurable because all its harmonic
coefficients are determined by the SAME smooth genuine effective adjoint.
No smoothness is assigned to the independently chosen potential packet. -/
lemma PhysicalPrincipalData.firstCovariantAdjointFiveHalfSection_aestronglyMeasurable
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (WQ : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y) (b : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) :
    AEStronglyMeasurable (P.firstCovariantAdjointFiveHalfSection WQ U b) (volume.restrict Y) := by
  let J := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  let A := WF.covariantCoordinateAdjointHigher b
  have hAS := WF.covariantCoordinateAdjointHigher_smooth hd b hw
  have hObs : ContDiffOn ℝ ∞ (fun y => A y (J (U y))) Y :=
    hAS.clm_apply (J.contDiff.comp_contDiffOn hU)
  apply aestronglyMeasurable_sphereSobolev_of_coefficients (3/2:ℝ)
  intro k
  have hFormula := (sphereSobolevCoefficientL (1/2:ℝ) k).contDiff.comp_contDiffOn hObs
  apply hFormula.continuousOn.aestronglyMeasurable hY.measurableSet |>.congr
  filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
  have hGraph := DFunLike.congr_fun (P.firstCovariantCoordinateAdjointFiveHalfL_inclusion hy (WQ y hy) b
    (A y) (WF.covariantCoordinateAdjointHigher_balanced b hy)) (U y)
  simp only [ContinuousLinearMap.comp_apply] at hGraph
  have hCoeff := congrArg (sphereSobolevCoefficientL (1/2:ℝ) k) hGraph
  simp only [sphereSobolevCoefficientL_inclusion] at hCoeff
  simp only [PhysicalPrincipalData.firstCovariantAdjointFiveHalfSection,dite_eq_left hy]
  exact hCoeff.symm

end ShrinkingSpheres

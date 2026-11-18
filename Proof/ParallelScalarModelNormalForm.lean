import Proof.ParallelScalarModelHalfIdentity
import Proof.ParallelScalarModelCoordinateWeak
import Proof.ParallelScalarModelPairAlgebra
import Proof.ParallelScalarModelZeroIntegral
import Proof.ParallelScalarModelZeroWeights

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

def scalarModelLeadingDensity (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  ∑ a : I,∑ b : I,∑ k : I,∑ c : I,
    halfCovariantThirdDensity d (metricDensity d.γ)
      (scalarModelSymmetricCoefficient d (scalarModelLeadingWeight d a b k c) c)
      (fiveHalfCovariantDerivative d U) (axis a) (axis b) (axis k) y

def scalarModelDegreeDensity (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  ∑ k : I,∑ c : I,scalarModelDegreePairDensity d (fun a b => scalarModelZeroDensityWeight d a b k c) c U y

/-- Exact paired normal form on the SAME genuine source. The leading
third-base term, paired degree term, and complete scalar transpose defect
are exposed before any quantitative estimate. -/
theorem scalarModelHalfCorrectedDensity_split (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (y : X)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    scalarModelHalfCorrectedDensity d U y=
      4*(scalarModelLeadingDensity d U y+scalarModelDegreeDensity d U y-scalarModelDefectPairDensity d U y) := by
  let A := scalarPrincipalMatrix d.γ d.g₂ d.radius y
  let G := (d.γ y)⁻¹
  let ell := fun k : I => coordDeriv k (fun x => Real.log (d.radius x)) y
  let R := fun c : I => framedRaisingHalfL d y (axis c)
  let H := fun a b : I => halfSectionCovariantDerivativeL d (fiveHalfCovariantDerivative d U (axis b)) y (axis a)
  let V := fun k : I => sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (fiveHalfCovariantDerivative d U (axis k) y)
  let u := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let D0 := degreeHigherL u
  let D1 := D0-J u
  let F := scalarFiveHalfDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius) U y
  have hForward : scalarModelForwardWeakSection d U y=
      ∑ k : I,∑ c : I,G k c • (R c (V k)+ell k • R c D0) :=
    scalarModelForwardWeakSection_coordinate d U y hFrame
  have hAdjoint : scalarModelAdjointWeakSection d U y=
      ∑ k : I,∑ c : I,G k c • (-(R c).adjoint (V k)+ell k • (R c).adjoint D1) := by
    simpa only [D1,D0,u,J,sphereSobolevInclusionL_trans_apply] using
      scalarModelAdjointWeakSection_coordinate d U y hFrame
  have hLead : scalarModelLeadingDensity d U y=
      ∑ a : I,∑ b : I,∑ k : I,∑ c : I,metricDensity d.γ y*A a b*G k c*
        ⟪H a b,(R c+(R c).adjoint) (V k)⟫_ℝ := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro c _
    simp only [halfCovariantThirdDensity,scalarModelSymmetricCoefficient,scalarModelLeadingWeight,
      sphereSobolevDualPairing,_root_.smul_apply,real_inner_smul_right]
    ring
  have hDegree : scalarModelDegreeDensity d U y=
      ∑ k : I,∑ c : I,∑ a : I,∑ b : I,metricDensity d.γ y*A a b*G k c*ell k*
        (⟪D0,(R c).adjoint (H a b)⟫_ℝ-⟪D1,R c (H a b)⟫_ℝ) := by
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro c _
    dsimp only [scalarModelDegreePairDensity,pairedHalfMassDensity]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [halfCovariantSecondMassDensity,scalarModelZeroDensityWeight,scalarModelZeroWeight,
      scalarModelLeadingWeight,scalarModelShiftedDegreeSection,map_sub,
      scalarModelDegreeSection_half_inclusion,sphereSobolevInclusionL_trans_apply,sphereSobolevDualPairing]
    simp only [D1,D0,u,J,sphereSobolevInclusionL_trans_apply]
    ring
  have hAlg := scalar_model_pair_split_algebra (metricDensity d.γ y) A G ell R H V D0 D1 F
  let S := scalarFiveHalfSecondSection d (scalarPrincipalMatrix d.γ d.g₂ d.radius) U y
  have hIn := congrArg₂ (fun vf va : SphereSobolev (-(1/2:ℝ)) => metricDensity d.γ y*(
    sphereSobolevDualPairing (1/2:ℝ) S vf-sphereSobolevDualPairing (1/2:ℝ) (S+F) va)) hForward hAdjoint
  have hDefect : scalarModelDefectPairDensity d U y=
      metricDensity d.γ y*⟪F,(∑ k : I,∑ c : I,G k c • (-(R c).adjoint (V k)+ell k • (R c).adjoint D1))⟫_ℝ :=
    congrArg (fun va : SphereSobolev (-(1/2:ℝ)) => metricDensity d.γ y*sphereSobolevDualPairing (1/2:ℝ) F va) hAdjoint
  have hOut := congrArg₂ (fun lz f : ℝ => lz-f) (congrArg₂ (fun l z : ℝ => l+z) hLead hDegree) hDefect
  have hSplit : metricDensity d.γ y*(
      sphereSobolevDualPairing (1/2:ℝ) S (scalarModelForwardWeakSection d U y)-
      sphereSobolevDualPairing (1/2:ℝ) (S+F) (scalarModelAdjointWeakSection d U y))=
      scalarModelLeadingDensity d U y+scalarModelDegreeDensity d U y-scalarModelDefectPairDensity d U y := by
    exact hIn.trans (hAlg.trans hOut.symm)
  change 4*metricDensity d.γ y*(_-_) = _
  calc
    _ = 4*(metricDensity d.γ y*(_-_)) := by ring
    _ = _ := congrArg (fun r : ℝ => 4*r) hSplit

end ShrinkingSpheres.ParallelEnergy

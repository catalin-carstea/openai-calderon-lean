import Proof.RelativeCenterWeightRotation
import Proof.SmoothScalarRotationDerivative
import Proof.ScalarLinearCombinationDerivative
import Proof.RotationVectorCoefficientAlgebra
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation
namespace RelativeCenterErrorCoefficientFamily
variable {d : Data} {y a : X} {CC CH : ℝ}

def smoothThirdCoefficient {k : I} (C : RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (p : NormalFrameRelativeParameter) : SmoothCoefficientJets 3 :=
  commonSupportCoefficientFamily 3 C.scalar C.smooth C.support C.compact C.supported p

lemma closed_eq_include_smoothThird {k : I} (C : RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (p : NormalFrameRelativeParameter) :
    C.closed p=smoothCoefficientClosureInclusionL 3 (C.smoothThirdCoefficient p) := rfl

def coarseVectorRotationModel_at (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (p : NormalFrameRelativeParameter) (k i j : I) (θ : ℝ) : SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
  ∑ l : I,(coordinateRotationIsometry i j θ (axis k)) l •
    smoothCoefficientRotatingCoarseFamily ((C l).smoothThirdCoefficient p) i j θ

lemma coarse_rotation_germ_at (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (p : NormalFrameRelativeParameter) (hp : ∀ k,p ∈ (C k).domain)
    (he : ∀ k l,metricPair d.γ p.1.1 (p.1.2 (axis k)) (p.1.2 (axis l)) = if k=l then 1 else 0) (k i j : I) :
    (fun θ => closedThreeJetCoarseScalarMultiplierL ((C k).closed
      (normalFrameRelativeAngularCurve d.γ p i j θ))) =ᶠ[𝓝 (0:ℝ)]
      coarseVectorRotationModel_at C p k i j := by
  have hMap (θ : ℝ) : coarseVectorRotationModel_at C p k i j θ = coarseScalarMultiplierMapL
      (∑ l : I,(coordinateRotationIsometry i j θ (axis k)) l •
        coordinateRotationSphereSection i j
          (coefficientSmoothData (smoothMultiplierLowerJets ((C l).smoothThirdCoefficient p))).1
          (coefficientSmoothData (smoothMultiplierLowerJets ((C l).smoothThirdCoefficient p))).2 θ) := by
    simp only [coarseVectorRotationModel_at,smoothCoefficientRotatingCoarseFamily,map_sum,map_smul]
  filter_upwards [scalar_rotation_germ_at C p hp he i j] with θ hθ
  rw [closed_eq_include_smoothThird,closedThreeJetCoarseScalarMultiplierL_on_smooth,hMap]
  apply congrArg coarseScalarMultiplierMapL
  apply ContinuousMap.ext
  intro w
  change coefficientValue 2 (smoothMultiplierLowerJets ((C k).smoothThirdCoefficient
      (normalFrameRelativeAngularCurve d.γ p i j θ))) w.val =
    ∑ l : I,(coordinateRotationIsometry i j θ (axis k)) l*
      coefficientValue 2 (smoothMultiplierLowerJets ((C l).smoothThirdCoefficient p))
        (coordinateRotationIsometry i j θ w.val)
  simp only [coefficientValue_smoothMultiplierLowerJets,smoothThirdCoefficient,
    coefficientValue_commonSupportCoefficientFamily]
  exact hθ k w

lemma hasDerivAt_coarseVectorRotationModel_at (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (p : NormalFrameRelativeParameter) (k i j : I) :
    HasDerivAt (coarseVectorRotationModel_at C p k i j)
      (closedCoefficientAngularCoarseL i j ((C k).closed p)+
        (if k=i then closedThreeJetCoarseScalarMultiplierL ((C j).closed p) else 0)-
        (if k=j then closedThreeJetCoarseScalarMultiplierL ((C i).closed p) else 0)) 0 := by
  let Q := fun l => (C l).smoothThirdCoefficient p
  have hq (l : I) : HasDerivAt (fun θ => (coordinateRotationIsometry i j θ (axis k)) l)
      ((rotationVectorL i j (axis k)) l) 0 := by
    have hEntry := hasDerivAt_pi.mp (hasDerivAt_pi.mp (hasDerivAt_coordinateRotationMatrix_zero i j) l) k
    have hFun : (fun θ => coordinateRotationMatrix i j θ l k) =
        (fun θ => (coordinateRotationIsometry i j θ (axis k)) l) := by
      funext θ
      rw [coordinateRotationMatrix_entry]
      rfl
    have hGen : coordinateRotationGeneratorMatrix i j l k=(rotationVectorL i j (axis k)) l := by
      rw [coordinateRotationGeneratorMatrix_entry,rotationVectorL_apply]
    rw [hFun,hGen] at hEntry
    exact hEntry
  have hh := hasDerivAt_sum_smul_family
    (fun l θ => (coordinateRotationIsometry i j θ (axis k)) l) (fun l => (rotationVectorL i j (axis k)) l)
    (fun l => smoothCoefficientRotatingCoarseFamily (Q l) i j)
    (fun l => closedCoefficientAngularCoarseL i j (smoothCoefficientClosureInclusionL 3 (Q l))) 0
    hq (fun l => hasDerivAt_smoothCoefficientRotatingCoarseFamily (Q l) i j)
  have hZero (l : I) : (coordinateRotationIsometry i j 0 (axis k)) l=(axis k) l :=
    congrArg (fun z : X => z l) (coordinateRotation_zero i j (axis k))
  simp only [smoothCoefficientRotatingCoarseFamily_zero,hZero] at hh
  rw [rotation_coefficients_sum] at hh
  exact hh

lemma hasDerivAt_coarse_angular_curve_at (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (p : NormalFrameRelativeParameter) (hp : ∀ k,p ∈ (C k).domain)
    (he : ∀ k l,metricPair d.γ p.1.1 (p.1.2 (axis k)) (p.1.2 (axis l)) = if k=l then 1 else 0) (k i j : I) :
    HasDerivAt (fun θ => closedThreeJetCoarseScalarMultiplierL ((C k).closed
      (normalFrameRelativeAngularCurve d.γ p i j θ)))
      (closedCoefficientAngularCoarseL i j ((C k).closed p)+
        (if k=i then closedThreeJetCoarseScalarMultiplierL ((C j).closed p) else 0)-
        (if k=j then closedThreeJetCoarseScalarMultiplierL ((C i).closed p) else 0)) 0 := by
  exact (hasDerivAt_coarseVectorRotationModel_at C p k i j).congr_of_eventuallyEq (coarse_rotation_germ_at C p hp he k i j)
end RelativeCenterErrorCoefficientFamily
end ShrinkingSpheres

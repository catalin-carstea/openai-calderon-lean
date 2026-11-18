import Proof.RelativeCenterScalarRotationDerivative
import Proof.InjectiveLinearDerivative
import Proof.RelativeAngularDerivativeCurve
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
open OAI.AnisotropicCalderon.SphereHarmonic
namespace RelativeCenterErrorCoefficientFamily
variable {d : Data} {y a : X} {CC CH : ℝ}

lemma hasDerivAt_one_angular_curve_at (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (p : NormalFrameRelativeParameter) (hp : ∀ k,p ∈ (C k).domain)
    (he : ∀ k l,metricPair d.γ p.1.1 (p.1.2 (axis k)) (p.1.2 (axis l)) = if k=l then 1 else 0) (k i j : I) :
    HasDerivAt (fun θ => closedOneBoundaryScalarMultiplierL ((C k).closed
      (normalFrameRelativeAngularCurve d.γ p i j θ)))
      (closedCoefficientAngularOneL i j ((C k).closed p)+
        (if k=i then closedOneBoundaryScalarMultiplierL ((C j).closed p) else 0)-
        (if k=j then closedOneBoundaryScalarMultiplierL ((C i).closed p) else 0)) 0 := by
  let curve := normalFrameRelativeAngularCurve d.γ p i j
  let Q := fun l => (C l).closed p
  let A := fun θ => closedOneBoundaryScalarMultiplierL ((C k).closed (curve θ))
  let B := fun θ => closedThreeJetCoarseScalarMultiplierL ((C k).closed (curve θ))
  let DA := closedCoefficientAngularOneL i j (Q k)+
    (if k=i then closedOneBoundaryScalarMultiplierL (Q j) else 0)-
    (if k=j then closedOneBoundaryScalarMultiplierL (Q i) else 0)
  let DB := closedCoefficientAngularCoarseL i j (Q k)+
    (if k=i then closedThreeJetCoarseScalarMultiplierL (Q j) else 0)-
    (if k=j then closedThreeJetCoarseScalarMultiplierL (Q i) else 0)
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let L : (SphereSobolev 1 →L[ℝ] SphereSobolev 1) →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
    ContinuousLinearMap.compL ℝ (SphereSobolev 1) (SphereSobolev 1) (SphereSobolev 0) I0
  have hL : Function.Injective L := by
    intro U V hUV
    apply ContinuousLinearMap.ext
    intro u
    apply sphereSobolevInclusionL_injective 1 0 (by norm_num)
    exact congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T u) hUV
  have hC : ContDiff ℝ ∞ (C k).closed :=
    contDiff_commonSupportClosedCoefficientFamily 3 (C k).scalar (C k).smooth
      (C k).support (C k).compact (C k).supported
  have hA : DifferentiableAt ℝ A 0 :=
    ((closedOneBoundaryScalarMultiplierL.contDiff.comp hC).differentiable (by simp) (curve 0)).comp 0
      (hasDerivAt_normalFrameRelativeAngularCurve d.γ p i j).differentiableAt
  have hB : HasDerivAt B DB 0 := hasDerivAt_coarse_angular_curve_at C p hp he k i j
  have hCompat (θ : ℝ) : L (A θ)=(B θ).comp I0 := by
    apply ContinuousLinearMap.ext
    intro u
    exact closedThreeJet_scalar_multiplier_compatible _ u
  have hDCompat : L DA=DB.comp I0 := by
    apply ContinuousLinearMap.ext
    intro u
    have hOne (l : I) : I0 (closedOneBoundaryScalarMultiplierL (Q l) u) =
        closedThreeJetCoarseScalarMultiplierL (Q l) (I0 u) := closedThreeJet_scalar_multiplier_compatible _ u
    have hAng : I0 (closedCoefficientAngularOneL i j (Q k) u) =
        closedCoefficientAngularCoarseL i j (Q k) (I0 u) := closedCoefficientAngular_compatible _ _ _ u
    have hIf (P : Prop) [Decidable P] (l : I) :
        I0 ((if P then closedOneBoundaryScalarMultiplierL (Q l) else 0) u) =
          (if P then closedThreeJetCoarseScalarMultiplierL (Q l) else 0) (I0 u) := by
      split_ifs
      · exact hOne l
      · exact I0.map_zero
    change I0 (DA u)=DB (I0 u)
    calc
      _ = (I0 (closedCoefficientAngularOneL i j (Q k) u)+
          I0 ((if k=i then closedOneBoundaryScalarMultiplierL (Q j) else 0) u))-
          I0 ((if k=j then closedOneBoundaryScalarMultiplierL (Q i) else 0) u) := by
        simp only [DA,_root_.sub_apply,_root_.add_apply,map_sub,map_add]
      _ = (closedCoefficientAngularCoarseL i j (Q k) (I0 u)+
          (if k=i then closedThreeJetCoarseScalarMultiplierL (Q j) else 0) (I0 u))-
          (if k=j then closedThreeJetCoarseScalarMultiplierL (Q i) else 0) (I0 u) :=
        congrArg₂ (fun x y : SphereSobolev 0 => x-y)
          (congrArg₂ (fun x y : SphereSobolev 0 => x+y) hAng (hIf (k=i) j)) (hIf (k=j) i)
      _ = _ := rfl
  apply hasDerivAt_of_injective_clm L hL A DA 0 hA
  let Pre : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
    (ContinuousLinearMap.compL ℝ (SphereSobolev 1) (SphereSobolev 0) (SphereSobolev 0)).flip I0
  have hPost := Pre.hasFDerivAt.comp_hasDerivAt (0:ℝ) hB
  change HasDerivAt (fun θ => (B θ).comp I0) (DB.comp I0) 0 at hPost
  have hPostActual := hPost.congr_of_eventuallyEq (Filter.Eventually.of_forall hCompat)
  exact hPostActual.congr_deriv hDCompat.symm

lemma oneMultiplier_angularDerivative_at (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (p : NormalFrameRelativeParameter) (hp : ∀ k,p ∈ (C k).domain)
    (he : ∀ k l,metricPair d.γ p.1.1 (p.1.2 (axis k)) (p.1.2 (axis l)) = if k=l then 1 else 0) (k i j : I) :
    normalFrameRelativeAngularDerivative d.γ (fun p => closedOneBoundaryScalarMultiplierL ((C k).closed p)) i j
      p =
      closedCoefficientAngularOneL i j ((C k).closed p)+
        (if k=i then closedOneBoundaryScalarMultiplierL ((C j).closed p) else 0)-
        (if k=j then closedOneBoundaryScalarMultiplierL ((C i).closed p) else 0) := by
  have hC : ContDiff ℝ ∞ (C k).closed :=
    contDiff_commonSupportClosedCoefficientFamily 3 (C k).scalar (C k).smooth
      (C k).support (C k).compact (C k).supported
  have hF := closedOneBoundaryScalarMultiplierL.contDiff.comp hC
  exact (hasDerivAt_relativeAngularFamily d.γ (fun p => closedOneBoundaryScalarMultiplierL ((C k).closed p))
    p i j (hF.differentiable (by simp) _)).unique
      (hasDerivAt_one_angular_curve_at C p hp he k i j)
end RelativeCenterErrorCoefficientFamily
end ShrinkingSpheres

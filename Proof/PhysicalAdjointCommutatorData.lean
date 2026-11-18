import Proof.NativeAdjointCommutatorData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

def PhysicalFirstErrorAdjointCommutatorData (Eb : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (La Lb : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (B : ℝ) : Prop :=
  (∃ Ha : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ha=
      La.adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) ∧
  ∀ Ha Hb : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ha=
      La.adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) →
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hb=
      Eb.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) →
    GradedEndpointCommutatorBound (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
      La.adjoint Lb Ha Hb B

lemma native_first_error_adjoint_data_transport
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM CC CH CS : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (hData : NativeFirstErrorAdjointCommutatorData s CC CH CS) (a b : X)
    (Ca : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (Cb : (j : I) → RelativeCenterErrorCoefficientFamily d y b j CC CH)
    (Eb : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (La Lb : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hEb : Eb=s.firstAdjointErrorFamily Cb ((y,frameVectorLinear d.frame y),0))
    (hLa : La=s.firstAdjointHalfErrorFamily Ca ((y,frameVectorLinear d.frame y),0))
    (hLb : Lb=s.firstAdjointHalfErrorFamily Cb ((y,frameVectorLinear d.frame y),0)) :
    PhysicalFirstErrorAdjointCommutatorData Eb La Lb (CS*‖a‖*‖b‖*(d.radius y)^2) := by
  obtain ⟨hEndpoints,hMixed⟩ := hData
  constructor
  · obtain ⟨Ha,hHa⟩ := hEndpoints a Ca
    exact ⟨Ha,hHa.trans (congrArg (fun T => T.adjoint.comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) hLa.symm)⟩
  · intro Ha Hb hHa hHb
    have hHaNative := hHa.trans (congrArg (fun T => T.adjoint.comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) hLa)
    have hHbNative := hHb.trans (congrArg (fun T => T.comp
      (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) hEb)
    exact (hMixed a b Ca Cb Ha Hb hHaNative hHbNative).congr
      (congrArg (fun T => T.adjoint) hLa.symm) hLb.symm rfl rfl
end ShrinkingSpheres

import Proof.RadialEndpointCompatibility
import Proof.CanonicalFirstRadialCorrection
import Proof.RadialCorrectionSobolev

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma sphereSobolevInclusionL_trans_apply (s t r : ℝ) (hts : t ≤ s) (hrt : r ≤ t)
    (u : SphereSobolev s) :
    sphereSobolevInclusionL t r hrt (sphereSobolevInclusionL s t hts u) =
      sphereSobolevInclusionL s r (le_trans hrt hts) u := by
  exact congrArg (fun T : SphereSobolev s →L[ℝ] SphereSobolev r => T u)
    (sphereSobolevInclusionL_trans s t r hts hrt)

lemma radialCorrectionSobolevL_inclusion (s t : ℝ) (hts : t ≤ s)
    (q : X →L[ℝ] ℝ) (u : SphereSobolev s) :
    sphereSobolevInclusionL s t hts (radialCorrectionSobolevL s q u) =
      radialCorrectionSobolevL t q (sphereSobolevInclusionL s t hts u) :=
  sphereSobolevInclusionL_radialDrift sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics s t hts (radialCorrectionVector q) u

def actualHighRadialTaylorL (F : SmoothCoefficientMatrix 2) (q : X →L[ℝ] ℝ) (r : ℝ) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  actualHighRadialErrorL F-r • (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
    (radialCorrectionSobolevL (3/2:ℝ) q)

def actualLowRadialTaylorL (a : X → Mat)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (F : SmoothCoefficientMatrix 2) (q : X →L[ℝ] ℝ) (r : ℝ) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  actualLowRadialErrorL a ha F-r • (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
    (radialCorrectionSobolevL (1/2:ℝ) q)

theorem actual_radial_taylor_high_mid_compatible
    (F : SmoothCoefficientMatrix 2) (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (q : X →L[ℝ] ℝ) (r : ℝ)
    (hMid : R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F)) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialTaylorL F q r) =
      (R-r • (radialCorrectionCovectorL q).comp (sphereSobolevInclusionL 1 0 (by norm_num))).comp
        (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  have h := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => T u) hMid
  simp only [ContinuousLinearMap.comp_apply] at h
  change sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (actualHighRadialErrorL F u-r • sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
        (radialCorrectionSobolevL (3/2:ℝ) q u)) =
    R (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u)-
      r • radialCorrectionCovectorL q (sphereSobolevInclusionL 1 0 (by norm_num)
        (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u))
  rw [map_sub,map_smul,← h]
  congr 2
  rw [sphereSobolevInclusionL_trans_apply,radialCorrectionSobolevL_inclusion,
    radialCorrectionSobolevL_zero,sphereSobolevInclusionL_trans_apply]

theorem actual_radial_taylor_covector_endpoints_compatible {a : X → Mat}
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 ha))
    (F : SmoothCoefficientMatrix 2)
    (hPoint : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z = a z)
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (hNormal : (negativeBoundaryCoefficientMulL (normalCoefficientJet F)).IsInvertible)
    (q : X →L[ℝ] ℝ) (r : ℝ) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (actualHighRadialTaylorL F q r) =
      (actualLowRadialTaylorL a ha F q r).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  have h := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T u)
    (actual_radial_endpoints_compatible ha hc F hPoint hInv hNormal)
  simp only [ContinuousLinearMap.comp_apply] at h
  change sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (actualHighRadialErrorL F u-r • sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
        (radialCorrectionSobolevL (3/2:ℝ) q u)) =
    actualLowRadialErrorL a ha F (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)-
      r • sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (radialCorrectionSobolevL (1/2:ℝ) q (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u))
  rw [map_sub,map_smul,h]
  congr 2
  rw [← radialCorrectionSobolevL_inclusion,sphereSobolevInclusionL_trans_apply]

end ShrinkingSpheres

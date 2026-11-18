import Proof.ZeroOrderMidpointInclusion
import Proof.Archive.NativeH2ConormalRadialConversion
import Proof.Archive.SphereSobolevCompatibleInterpolationTopology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

def zeroOrderEndpointPair
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (KH : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) : SphereSobolevEndpointPair :=
  (KN.comp (sphereSobolevBesselOrderL (1/2:ℝ) (-(1/2:ℝ))),
    KH.comp (sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ)))
lemma zeroOrderEndpointPair_compatible
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (KH : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hc : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp KH=
      KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))) :
    zeroOrderEndpointPair KN KH ∈ sphereSobolevCompatibleEndpoints := by
  have hb := sphereSobolevBesselOrderL_inclusion_comp (3/2:ℝ) (1/2:ℝ) (1/2:ℝ) (-(1/2:ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have hCompat : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (KH.comp (sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ)))=
    (KN.comp (sphereSobolevBesselOrderL (1/2:ℝ) (-(1/2:ℝ)))).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
    calc
      _ = ((sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp KH).comp
          (sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ)) := rfl
      _ = (KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))).comp
          (sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ)) := congrArg
        (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
          T.comp (sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ))) hc
      _ = KN.comp ((sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
          (sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ))) := rfl
      _ = KN.comp ((sphereSobolevBesselOrderL (1/2:ℝ) (-(1/2:ℝ))).comp
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) := congrArg
        (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => KN.comp T) hb
      _ = _ := rfl
  have hI := sphereSobolevInclusionL_eq_of_target_eq (1/2:ℝ) (-1/2:ℝ) (-(1/2:ℝ))
    (by norm_num) (by norm_num) (by ring)
  exact (congrArg (fun J : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
    J.comp (KH.comp (sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ)))) hI).trans hCompat

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
def zeroOrderInterpolationFamily
    (KN : P → SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (KH : P → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (U : Set P)
    (hc : ∀ p ∈ U,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (KH p)=
      (KN p).comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))) :
    P → SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
  fun p => (sphereSobolevCompatibleInterpolationFamily (fun p => zeroOrderEndpointPair (KN p) (KH p)) U
    (fun p hp => zeroOrderEndpointPair_compatible (KN p) (KH p) (hc p hp)) p).comp (sphereSobolevBesselOrderL 0 1)
lemma zeroOrderInterpolationFamily_of_mem
    (KN : P → SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (KH : P → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (U : Set P)
    (hc : ∀ p ∈ U,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (KH p)=
      (KN p).comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)))
    (p : P) (hp : p ∈ U) :
    zeroOrderInterpolationFamily KN KH U hc p=zeroOrderMidpointL (KN p) (KH p) (hc p hp) := by
  rw [zeroOrderInterpolationFamily,sphereSobolevCompatibleInterpolationFamily_of_mem _ U _ p hp]
  rfl
lemma contDiffOn_zeroOrderInterpolationFamily
    (KN : P → SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (KH : P → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (U : Set P) (hU : IsOpen U)
    (hc : ∀ p ∈ U,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (KH p)=
      (KN p).comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)))
    (hKN : ContDiffOn ℝ ∞ KN U) (hKH : ContDiffOn ℝ ∞ KH U) :
    ContDiffOn ℝ ∞ (zeroOrderInterpolationFamily KN KH U hc) U := by
  have hT : ContDiffOn ℝ ∞ (fun p => zeroOrderEndpointPair (KN p) (KH p)) U :=
    (hKN.clm_comp contDiffOn_const).prodMk (hKH.clm_comp contDiffOn_const)
  exact (contDiffOn_sphereSobolevCompatibleInterpolationFamily _ U hU
    (fun p hp => zeroOrderEndpointPair_compatible (KN p) (KH p) (hc p hp)) hT).clm_comp contDiffOn_const
end ShrinkingSpheres

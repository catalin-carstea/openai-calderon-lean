import Proof.FrameErrorMatrixDegreeCross
import Proof.FramePrincipalSmooth
import Proof.ActualFrameErrorLift
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
namespace ActualFrameErrorEndpointPair
variable {Y : Set X} {d : Data}
  {A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0} {CE : ℝ}

def principalDegreeCrossL (P : ActualFrameErrorEndpointPair Y d A G CE) (x : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  frameErrorMatrixDegreeCrossL P.low P.high
    (fun x i j => frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j)
    (scaledFrameLogRadius d.radius d.frame) x

lemma norm_principalDegreeCrossL_small {Ω : Set X} {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : ActualFrameErrorEndpointPair Y d A G CE) (hCE : 0 ≤ CE)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {x : X} (hx : x ∈ Y) :
    ‖P.principalDegreeCrossL x‖ ≤ 324*(K+1)*K^2*CE*ε := by
  have hr : 0 < d.radius x := (hd.2.2.2.2.1.2 x hx).1
  have hrε : d.radius x ≤ ε := (radius_bounds (d.radius x) (beta d.γ d.radius x) floor ε hr.le hf
    (hd.2.2.2.2.1.2 x hx).2.1 (hd.2.2.2.2.2 x hx).2).2.2
  let B := 9*(K+1)*K^2
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hNorm := norm_frameErrorMatrixDegreeCrossL_le P.low P.high
    (fun x i j => frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j)
    (scaledFrameLogRadius d.radius d.frame) x hB (mul_nonneg hCE hr.le)
    (fun i j => (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hx i j).2.1)
    (fun i => hd.scaled_frame_logRadius_bound hf hε hε1 hx i)
    (fun i => P.low_bound i x hx) (fun j => P.high_bound j x hx)
  change ‖frameErrorMatrixDegreeCrossL P.low P.high _ _ x‖ ≤ _
  calc
    _ ≤ 36*B*(CE*d.radius x) := hNorm
    _ = (36*B*CE)*d.radius x := by ring
    _ ≤ (36*B*CE)*ε := mul_le_mul_of_nonneg_left hrε (by positivity)
    _ = _ := by dsimp only [B];ring

lemma principalDegreeCrossL_smooth {Ω : Set X} {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : ActualFrameErrorEndpointPair Y d A G CE) (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) :
    ContDiffOn ℝ ∞ P.principalDegreeCrossL Y := by
  have ht (i : I) : ContDiffOn ℝ ∞ (scaledFrameLogRadius d.radius d.frame i) Y :=
    contDiffOn_scaledFrameLogRadius hY hd.2.2.2.2.1.1
      (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
      (fun j => (hd.1.2.2.2.2.2.2.1 j).mono hSub) i
  exact contDiffOn_frameErrorMatrixDegreeCrossL P.low P.high _ _ P.low_smooth P.high_smooth
    (fun i j => hd.contDiffOn_framePrincipalCoefficient hSub hK i j) ht
end ActualFrameErrorEndpointPair

namespace SecondTraceSectionOutput
variable {Y : Set X} {d : Data}
  {A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {φ : Field} {L : ℂ →L[ℝ] ℝ} {F : X × X → ℝ} {hF : ContDiff ℝ ∞ F}

/-- Scaled logarithmic-radius degree/error terms are exactly the controlled
    coefficient on the SAME physical error lifts; t_i=r*d_i(log r). -/
lemma principal_degree_cross_actual (P : SecondTraceSectionOutput Y d A G S φ L F hF)
    {CE : ℝ} (E : ActualFrameErrorEndpointPair Y d A G CE) {y : X} (hy : y ∈ Y) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j •
        (scaledFrameLogRadius d.radius d.frame i y • sphereSobolevDegreeL (P.errorLift y j)+
          scaledFrameLogRadius d.radius d.frame j y •
            actualFrameFirstAdjointErrorFamily d A G i y
              (sphereSobolevShiftedDegreeL 2 (ambientSobolevSection 2 (by norm_num) F hF y))))=
      E.principalDegreeCrossL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num)
        (ambientSobolevSection 2 (by norm_num) F hF y)) :=
  frameErrorMatrixDegreeCrossL_actual_lifts E.low E.high
    (fun x i j => frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j)
    (scaledFrameLogRadius d.radius d.frame) y
    (fun i => actualFrameFirstAdjointErrorFamily d A G i y)
    (ambientSobolevSection 2 (by norm_num) F hF y) (P.errorLift y)
    (fun i => E.low_coarse i y hy) (fun j => P.errorLift_half E hy j)
end SecondTraceSectionOutput
end ShrinkingSpheres

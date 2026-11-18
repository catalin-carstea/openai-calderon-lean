import Proof.ActualCorrectionProductBudget
import Proof.FrameCorrectionErrorCross
import Proof.ActualFrameErrorLift
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
namespace ActualFrameErrorEndpointPair
variable {Y : Set X} {d : Data}
  {A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0} {CE : ℝ}

def principalCorrectionCrossL (P : ActualFrameErrorEndpointPair Y d A G CE) (x : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  radiusFrameCorrectionErrorCrossL d P.low P.high
    (fun x i j => frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j) x

lemma norm_principalCorrectionCrossL_small {Ω : Set X} (hΩ : IsOpen Ω) {m : ℕ} (hm : 2 ≤ m)
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : ActualFrameErrorEndpointPair Y d A G CE) (hCE : 0 ≤ CE)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {x : X} (hx : x ∈ Y) :
    ‖P.principalCorrectionCrossL x‖ ≤ 81*(K+1)*K^2*
      (firstCorrectionGradeBound (-(1/2:ℝ)) K (M ⟨1,by omega⟩)+
        firstCorrectionGradeBound (1/2:ℝ) K (M ⟨1,by omega⟩))*CE*ε := by
  have hr : 0 < d.radius x := (hd.2.2.2.2.1.2 x hx).1
  have hrε := (radius_bounds (d.radius x) (beta d.γ d.radius x) floor ε hr.le hf
    (hd.2.2.2.2.1.2 x hx).2.1 (hd.2.2.2.2.2 x hx).2).2.2
  have hB : 0 ≤ 9*(K+1)*K^2 := by positivity
  exact (norm_radiusFrameCorrectionErrorCrossL_small d P.low P.high _ x hB hCE
    (firstCorrectionGradeBound_nonneg (-(1/2:ℝ)) K (M ⟨1,by omega⟩))
    (firstCorrectionGradeBound_nonneg (1/2:ℝ) K (M ⟨1,by omega⟩))
    hr.le (hrε.trans hε1) hrε
    (fun i j => (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hx i j).2.1)
    (fun i => P.low_bound i x hx) (fun j => P.high_bound j x hx)
    (fun i => hd.norm_firstFrameAdjointCorrectionAtL_le_gradeBound hΩ hm hK hf hε hε1 (-(1/2:ℝ)) hx i)
    (fun j => hd.norm_firstFrameAdjointCorrectionAtL_le_gradeBound hΩ hm hK hf hε hε1 (1/2:ℝ) hx j)).trans_eq (by ring)

lemma principalCorrectionCrossL_smooth {Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : ActualFrameErrorEndpointPair Y d A G CE)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) :
    ContDiffOn ℝ ∞ P.principalCorrectionCrossL Y :=
  hd.2.2.2.2.1.1.smul (hd.contDiffOn_frameCorrectionErrorCrossL hY hΩ hK P.low P.high _
    P.low_smooth P.high_smooth
    (fun i j => hd.contDiffOn_framePrincipalCoefficient (fun _x hx => hd.2.1.center_mem hx) hK i j))
end ActualFrameErrorEndpointPair

namespace SecondTraceSectionOutput
variable {Y : Set X} {d : Data}
  {A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {φ : Field} {L : ℂ →L[ℝ] ℝ} {F : X × X → ℝ} {hF : ContDiff ℝ ∞ F}

/-- The actual principal F/E cross on the SAME second-trace error lifts. -/
lemma principal_correction_cross_actual (P : SecondTraceSectionOutput Y d A G S φ L F hF)
    {CE : ℝ} (E : ActualFrameErrorEndpointPair Y d A G CE) {y : X} (hy : y ∈ Y) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (d.radius y • (∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j •
        (firstFrameAdjointCorrectionL d y i
          (sphereSobolevInclusionL 1 0 (by norm_num) (P.errorLift y j))+
            actualFrameFirstAdjointErrorFamily d A G i y
              (firstFrameAdjointCorrectionSobolevL d y j
                (sphereSobolevInclusionL 2 1 (by norm_num)
                  (ambientSobolevSection 2 (by norm_num) F hF y))))))=
      E.principalCorrectionCrossL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num)
        (ambientSobolevSection 2 (by norm_num) F hF y)) := by
  rw [map_smul]
  exact congrArg (fun v : SphereSobolev (-(1/2:ℝ)) => d.radius y • v)
    (frameCorrectionErrorCrossL_actual_lifts d E.low E.high
      (fun x i j => frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j) y
      (fun i => actualFrameFirstAdjointErrorFamily d A G i y)
      (ambientSobolevSection 2 (by norm_num) F hF y) (P.errorLift y)
      (fun i => E.low_coarse i y hy) (fun j => P.errorLift_half E hy j))
end SecondTraceSectionOutput
end ShrinkingSpheres

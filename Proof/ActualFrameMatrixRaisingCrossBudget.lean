import Proof.FramePrincipalSmooth
import Proof.FrameErrorMatrixRaisingCross
import Proof.ActualFrameErrorLift
import Proof.FramePrincipalBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
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

def principalRaisingCrossL (P : ActualFrameErrorEndpointPair Y d A G CE) (x : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  frameErrorMatrixRaisingCrossL P.low P.high
    (fun x i j => frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j) x

lemma norm_principalRaisingCrossL_small {Ω : Set X} {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : ActualFrameErrorEndpointPair Y d A G CE) (hCE : 0 ≤ CE)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {x : X} (hx : x ∈ Y) :
    ‖P.principalRaisingCrossL x‖ ≤ 81*(K+1)*K^2*
      (10*radialDriftSobolevBound (-(1/2:ℝ))+10*radialDriftSobolevBound (-(3/2:ℝ)))*CE*ε := by
  have hr : 0 < d.radius x := (hd.2.2.2.2.1.2 x hx).1
  have hrε : d.radius x ≤ ε := (radius_bounds (d.radius x) (beta d.γ d.radius x) floor ε hr.le hf
    (hd.2.2.2.2.1.2 x hx).2.1 (hd.2.2.2.2.2 x hx).2).2.2
  let B := 9*(K+1)*K^2
  let C := 10*radialDriftSobolevBound (-(1/2:ℝ))+10*radialDriftSobolevBound (-(3/2:ℝ))
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hBlo : 0 ≤ radialDriftSobolevBound (-(1/2:ℝ)) := zero_le_one.trans (le_max_left _ _)
  have hBhi : 0 ≤ radialDriftSobolevBound (-(3/2:ℝ)) := zero_le_one.trans (le_max_left _ _)
  have hC : 0 ≤ C := by dsimp only [C];positivity
  have hNorm := norm_frameErrorMatrixRaisingCrossL_le P.low P.high
    (fun x i j => frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j) x hB (mul_nonneg hCE hr.le)
    (fun i j => (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hx i j).2.1)
    (fun i => P.low_bound i x hx) (fun j => P.high_bound j x hx)
  change ‖frameErrorMatrixRaisingCrossL P.low P.high _ x‖ ≤ _
  calc
    _ ≤ 9*B*C*(CE*d.radius x) := hNorm
    _ = (9*B*C*CE)*d.radius x := by ring
    _ ≤ (9*B*C*CE)*ε := mul_le_mul_of_nonneg_left hrε (by positivity)
    _ = _ := by dsimp only [B,C];ring

lemma principalRaisingCrossL_smooth {Ω : Set X} {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : ActualFrameErrorEndpointPair Y d A G CE) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) :
    ContDiffOn ℝ ∞ P.principalRaisingCrossL Y := by
  exact contDiffOn_frameErrorMatrixRaisingCrossL P.low P.high _ P.low_smooth P.high_smooth
    (fun i j => hd.contDiffOn_framePrincipalCoefficient hSub hK i j)

end ActualFrameErrorEndpointPair
namespace SecondTraceSectionOutput
variable {Y : Set X} {d : Data}
  {A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {φ : Field} {L : ℂ →L[ℝ] ℝ} {F : X × X → ℝ} {hF : ContDiff ℝ ∞ F}

/-- The actual full-principal-matrix raising/error cross equals the small
    balanced operator on the SAME physical first-error output lifts. -/
lemma principal_raising_cross_actual (P : SecondTraceSectionOutput Y d A G S φ L F hF)
    {CE : ℝ} (E : ActualFrameErrorEndpointPair Y d A G CE) {y : X} (hy : y ∈ Y) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j •
        (flatOneRaisingL i (P.errorLift y j)+actualFrameFirstAdjointErrorFamily d A G i y
          (flatTwoRaisingL j (ambientSobolevSection 2 (by norm_num) F hF y))))=
      E.principalRaisingCrossL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num)
        (ambientSobolevSection 2 (by norm_num) F hF y)) :=
  frameErrorMatrixRaisingCrossL_actual_lifts E.low E.high
    (fun x i j => frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j) y
    (fun i => actualFrameFirstAdjointErrorFamily d A G i y)
    (ambientSobolevSection 2 (by norm_num) F hF y) (P.errorLift y)
    (fun i => E.low_coarse i y hy) (fun j => P.errorLift_half E hy j)
end SecondTraceSectionOutput

end ShrinkingSpheres

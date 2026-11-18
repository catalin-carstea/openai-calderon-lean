import Proof.ActualCoframeSobolevMultiplier
import Proof.ActualSmoothRadialTaylorPair
import Proof.ActualCenterGradientRealization
import Proof.FirstAdjointNormalForm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier

def actualFirstAdjointErrorFamily (d : Data) (a : X)
    (A G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (x : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ((d.radius x)⁻¹ • (radialAdjointTaylorRemainderL (A x) (firstRadialCorrectionL d x) (d.radius x)).comp
    (actualCoframeNormalSobolevL 1 d a x)+
    (fderiv ℝ (fun x => Real.log (d.radius x)) x a) •
      radialAdjointTaylorRemainderL (A x) (firstRadialCorrectionL d x) (d.radius x))+G x

lemma contDiffOn_actualFirstAdjointErrorFamily {Y Ω : Set X} {d : Data} (a : X)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K)
    (hrSm : ContDiffOn ℝ ∞ d.radius Y) (hr : ∀ x ∈ Y,0 < d.radius x)
    (A G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hA : ContDiffOn ℝ ∞ A Y) (hG : ContDiffOn ℝ ∞ G Y) :
    ContDiffOn ℝ ∞ (actualFirstAdjointErrorFamily d a A G) Y := by
  have hB := (h.firstRadialCorrectionL_smooth hΩ hK).mono hSub
  have hBa : ContDiffOn ℝ ∞ (fun x => (firstRadialCorrectionL d x).adjoint) Y :=
    (realHilbertOperatorAdjointL (SphereSobolev 0)).contDiff.comp_contDiffOn hB
  have hPa : ContDiffOn ℝ ∞ (fun x => radialAdjointTaylorRemainderL (A x)
      (firstRadialCorrectionL d x) (d.radius x)) Y :=
    (hA.sub contDiffOn_const).sub (hrSm.smul (hBa.clm_comp contDiffOn_const))
  have hInv := hrSm.inv (fun x hx => (hr x hx).ne')
  have hM := (h.contDiffOn_actualCoframeNormalSobolevL 1 a).mono hSub
  have hLog : ContDiffOn ℝ ∞ (fderiv ℝ (fun x => Real.log (d.radius x))) Y :=
    (hrSm.log (fun x hx => (hr x hx).ne')).fderiv_of_isOpen (m:=∞) hY (by simp)
  exact ((hInv.smul (hPa.clm_comp hM)).add
    ((hLog.clm_apply contDiffOn_const).smul hPa)).add hG

lemma actualFirstAdjointErrorFamily_physical {Ω : Set X} {d : Data}
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) {x : X} (hx : x ∈ Ω) (a : X)
    (A G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hG : RealizesActualCenterGradientAdjoint d x a (A x) (G x))
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (W : I → SmoothCoefficientJets 2)
    (hW : ∀ j : I,∀ w : UnitSphere,coefficientValue 2 (W j) w.val = actualCenterErrorWeight d x a j w.val) :
    actualFirstAdjointErrorFamily d a A G x =
      firstBoundaryAdjointRemainderL (fixedCenterCoefficient Q d.γ d.frame x a) W (A x)
        (firstRadialCorrectionL d x) (d.radius x) (fderiv ℝ (fun x => Real.log (d.radius x)) x a) := by
  unfold actualFirstAdjointErrorFamily
  rw [actualCoframeNormalSobolevL_point h hx Q hQ a,hG W hW]
  rfl
end ShrinkingSpheres

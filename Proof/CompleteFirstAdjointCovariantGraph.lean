import Proof.FirstCorrectionCovariantGraph
import Proof.LeadingFrameAdjointGraph
import Proof.CovariantRotationGraphOperations
import Proof.UniformActualFrameErrorCovariantTensor
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

lemma contDiffOn_actualLeadingFrameAdjointL {Y : Set X} (hY : IsOpen Y) (d : Data)
    (hR : ContDiffOn ℝ ∞ d.radius Y) (hr : ∀ x ∈ Y,d.radius x ≠ 0)
    (he : ∀ j,ContDiffOn ℝ ∞ (fun x => d.frame x j) Y) (j : I) :
    ContDiffOn ℝ ∞ (actualLeadingFrameAdjointL d j) Y := by
  have hLog := (hR.log hr).fderiv_of_isOpen (m:=∞) hY (by simp)
  exact ((hR.inv hr).smul contDiffOn_const).add ((hLog.clm_apply (he j)).smul contDiffOn_const)

/-- Complete actual first-adjoint angular normal operator: leading model,
    bounded first correction, and the SAME physical complete error. -/
def completeFirstAdjointFamily (d : Data)
    (A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (j : I) (x : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  actualLeadingFrameAdjointL d j x+firstFrameCorrectionCoarseFamily d j x+
    actualFrameFirstAdjointErrorFamily d A G j x

lemma completeFirstAdjointFamily_eq_normal_form (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (d : Data) (A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (j : I) (x : X) :
    completeFirstAdjointFamily d A G j x=
      modelBoundaryAdjointL (coordinateBoundaryCoefficients Q j) (d.radius x)
        (fderiv ℝ (fun y => Real.log (d.radius y)) x (d.frame x j))+
      (firstBoundaryAdjointCorrectionL (coordinateBoundaryCoefficients Q j) (firstRadialCorrectionL d x)
        (d.radius x) (fderiv ℝ (fun y => Real.log (d.radius y)) x (d.frame x j))).comp
        (sphereSobolevInclusionL 1 0 (by norm_num))+actualFrameFirstAdjointErrorFamily d A G j x := by
  unfold completeFirstAdjointFamily firstFrameCorrectionCoarseFamily
  rw [actualLeadingFrameAdjointL_eq_model Q hQ,← firstFrameAdjointCorrectionL_actual Q hQ]

/-- Exact tensor covariant graph for the complete physical first adjoint.
    The only conditional input is the SAME error's own proved graph. -/
theorem Admissible.completeFirstAdjointFamily_covariant_graph {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hES : ∀ j,ContDiffOn ℝ ∞ (actualFrameFirstAdjointErrorFamily d A G j) Y)
    {y : X} (hy : y ∈ Y) (a : X) (j : I) (S : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hE : CoarseCovariantRotationGraph d y a (actualFrameFirstAdjointErrorFamily d A G j)
      ((∑ k : I,frameConnectionCoefficient d.γ d.frame y a j k • actualFrameFirstAdjointErrorFamily d A G k y)+S)) :
    CoarseCovariantRotationGraph d y a (completeFirstAdjointFamily d A G j)
      ((∑ k : I,frameConnectionCoefficient d.γ d.frame y a j k • completeFirstAdjointFamily d A G k y)+
        (-(d.radius y)⁻¹*fderiv ℝ (fun x => Real.log (d.radius x)) y a) • flatOneRaisingL j+
        hessianBilinear d.γ (fun x => Real.log (d.radius x)) y a (d.frame y j) • sphereSobolevDegreeL+
        (firstFrameAdjointCovariantJetL d y a j).comp (sphereSobolevInclusionL 1 0 (by norm_num))+S) := by
  have he : ∀ j,ContDiffOn ℝ ∞ (fun x => d.frame x j) Y :=
    fun j => (hd.1.2.2.2.2.2.2.1 j).mono hSub
  have hR : ∀ x ∈ Y,d.radius x ≠ 0 := fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne'
  have hLD := ((contDiffOn_actualLeadingFrameAdjointL hY d hd.2.2.2.2.1.1 hR he j).contDiffAt
    (hY.mem_nhds hy)).differentiableAt (by simp)
  have hFD : DifferentiableAt ℝ (firstFrameCorrectionCoarseFamily d j) y :=
    (((hd.contDiffOn_firstFrameAdjointCorrectionL hY hΩ hK j).clm_comp contDiffOn_const).contDiffAt
      (hY.mem_nhds hy)).differentiableAt (by simp)
  have hED := ((hES j).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hL := actualLeadingFrameAdjointL_covariant_graph hY hΩ hSub d hd.1.1 hK
    hd.1.2.2.2.2.2.2.1 hd.1.2.2.2.2.2.2.2 hd.2.2.2.2.1.1 hy (hd.2.2.2.2.1.2 y hy).1 a j
  have hF := hd.firstFrameCorrectionCoarseFamily_covariant_graph hY hΩ hK hy a j
  have hFull := (hL.add hF hLD hFD).add hE (hLD.add hFD) hED
  have hEq :
      (((∑ k : I,frameConnectionCoefficient d.γ d.frame y a j k • actualLeadingFrameAdjointL d k y)+
        (-(d.radius y)⁻¹*fderiv ℝ (fun x => Real.log (d.radius x)) y a) • flatOneRaisingL j+
        hessianBilinear d.γ (fun x => Real.log (d.radius x)) y a (d.frame y j) • sphereSobolevDegreeL)+
      ((∑ k : I,frameConnectionCoefficient d.γ d.frame y a j k • firstFrameCorrectionCoarseFamily d k y)+
        (firstFrameAdjointCovariantJetL d y a j).comp (sphereSobolevInclusionL 1 0 (by norm_num))))+
      ((∑ k : I,frameConnectionCoefficient d.γ d.frame y a j k • actualFrameFirstAdjointErrorFamily d A G k y)+S)=
      (∑ k : I,frameConnectionCoefficient d.γ d.frame y a j k • completeFirstAdjointFamily d A G k y)+
        (-(d.radius y)⁻¹*fderiv ℝ (fun x => Real.log (d.radius x)) y a) • flatOneRaisingL j+
        hessianBilinear d.γ (fun x => Real.log (d.radius x)) y a (d.frame y j) • sphereSobolevDegreeL+
        (firstFrameAdjointCovariantJetL d y a j).comp (sphereSobolevInclusionL 1 0 (by norm_num))+S := by
    simp only [completeFirstAdjointFamily,Fin.sum_univ_three]
    module
  exact hEq ▸ hFull
end ShrinkingSpheres

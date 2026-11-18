import Proof.CanonicalRaisingCovariantGraph
import Proof.DegreeCovariantGraph
import Proof.CovariantRotationGraphOperations
import Proof.FrameCovectorDerivative
import Proof.FirstAdjointNormalForm
import Proof.FlatRaisingSobolev
import Proof.MovingRadius
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

/-- The leading frame adjoint, with scalar inverse-radius and log-radius
    coefficients separated from the fixed genuine angular operators. -/
def leadingFrameModelFamily (c : X → ℝ) (f : I → X → ℝ) (i : I) (x : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 := c x • flatOneRaisingL i+f i x • sphereSobolevDegreeL

lemma leadingFrameModelFamily_covariant_graph (d : Data) (y a : X)
    (hSkew : ∀ p q,frameConnectionCoefficient d.γ d.frame y a p q=
      -frameConnectionCoefficient d.γ d.frame y a q p)
    (c : X → ℝ) (f : I → X → ℝ) (hCD : DifferentiableAt ℝ c y)
    (hFD : ∀ i,DifferentiableAt ℝ (f i) y) (i : I) :
    CoarseCovariantRotationGraph d y a (leadingFrameModelFamily c f i)
      ((∑ k : I,frameConnectionCoefficient d.γ d.frame y a i k • leadingFrameModelFamily c f k y)+
        fderiv ℝ c y a • flatOneRaisingL i+
        (fderiv ℝ (f i) y a-∑ k : I,frameConnectionCoefficient d.γ d.frame y a i k*f k y) • sphereSobolevDegreeL) := by
  have hA := (flatOneRaisingL_covariant_graph d y a hSkew i).smul c hCD (differentiableAt_const _)
  have hB := (sphereSobolevDegreeL_covariant_graph d y a).smul (f i) (hFD i) (differentiableAt_const _)
  have hAB := hA.add hB (hCD.smul (differentiableAt_const _)) ((hFD i).smul (differentiableAt_const _))
  have hS : (c y • (∑ k : I,frameConnectionCoefficient d.γ d.frame y a i k • flatOneRaisingL k)+
      fderiv ℝ c y a • flatOneRaisingL i)+(f i y • (0 : SphereSobolev 1 →L[ℝ] SphereSobolev 0)+
      fderiv ℝ (f i) y a • sphereSobolevDegreeL)=
      (∑ k : I,frameConnectionCoefficient d.γ d.frame y a i k • leadingFrameModelFamily c f k y)+
        fderiv ℝ c y a • flatOneRaisingL i+
        (fderiv ℝ (f i) y a-∑ k : I,frameConnectionCoefficient d.γ d.frame y a i k*f k y) • sphereSobolevDegreeL := by
    simp only [leadingFrameModelFamily,Fin.sum_univ_three]
    module
  exact hS ▸ hAB

lemma fderiv_inverse_radius_log (r : X → ℝ) (y a : X) (hr : 0 < r y)
    (hR : DifferentiableAt ℝ r y) :
    fderiv ℝ (fun x => (r x)⁻¹) y a= -(r y)⁻¹*fderiv ℝ (fun x => Real.log (r x)) y a := by
  have hh := DFunLike.congr_fun ((hasDerivAt_inv hr.ne').comp_hasFDerivAt y hR.hasFDerivAt).fderiv a
  change fderiv ℝ (fun x => (r x)⁻¹) y a=_ at hh
  simp only [_root_.smul_apply,smul_eq_mul] at hh
  rw [logRadius_derivative r y a hR hr.ne']
  exact hh.trans (by field_simp [hr.ne'])

def actualLeadingFrameAdjointL (d : Data) (i : I) : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  leadingFrameModelFamily (fun x => (d.radius x)⁻¹)
    (fun j x => fderiv ℝ (fun y => Real.log (d.radius y)) x (d.frame x j)) i

lemma actualLeadingFrameAdjointL_eq_model (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (d : Data) (i : I) (y : X) :
    actualLeadingFrameAdjointL d i y=modelBoundaryAdjointL (coordinateBoundaryCoefficients Q i)
      (d.radius y) (fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i)) := by
  change (d.radius y)⁻¹ • flatOneRaisingL i+_=(d.radius y)⁻¹ •
    boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL+_
  rw [flatOneRaisingL,flatRaisingSobolevL_one Q hQ]

/-- The leading physical adjoint has its exact tensor-index connection
    plus the inverse-radius derivative and the actual logarithmic Hessian. -/
theorem actualLeadingFrameAdjointL_covariant_graph {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hSub : Y ⊆ Ω) (d : Data) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (he : ∀ j,ContDiffOn ℝ ∞ (fun x => d.frame x j) Ω)
    (hFrame : ∀ x ∈ Ω,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (hR : ContDiffOn ℝ ∞ d.radius Y) {y : X} (hy : y ∈ Y) (hr : 0 < d.radius y) (a : X) (i : I) :
    CoarseCovariantRotationGraph d y a (actualLeadingFrameAdjointL d i)
      ((∑ k : I,frameConnectionCoefficient d.γ d.frame y a i k • actualLeadingFrameAdjointL d k y)+
        (-(d.radius y)⁻¹*fderiv ℝ (fun x => Real.log (d.radius x)) y a) • flatOneRaisingL i+
        hessianBilinear d.γ (fun x => Real.log (d.radius x)) y a (d.frame y i) • sphereSobolevDegreeL) := by
  have hRad := (hR.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hLog := (hR.contDiffAt (hY.mem_nhds hy)).log hr.ne'
  have hDLog := (hLog.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have hEj (j : I) := ((he j).contDiffAt (hΩ.mem_nhds (hSub hy))).differentiableAt (by simp)
  have hSkew := frameConnection_skew hΩ h hK d.frame he hFrame (hSub hy) a
  have hGraph := leadingFrameModelFamily_covariant_graph d y a hSkew
    (fun x => (d.radius x)⁻¹) (fun j x => fderiv ℝ (fun z => Real.log (d.radius z)) x (d.frame x j))
    (hRad.inv hr.ne') (fun j => hDLog.clm_apply (hEj j)) i
  have hC := fderiv_inverse_radius_log d.radius y a hr hRad
  have hH := frame_covector_derivative_eq_hessian d.γ d.frame (fun x => Real.log (d.radius x)) y a i
    hDLog (hEj i) (hFrame y (hSub hy))
  rw [hC,hH] at hGraph
  exact hGraph
end ShrinkingSpheres

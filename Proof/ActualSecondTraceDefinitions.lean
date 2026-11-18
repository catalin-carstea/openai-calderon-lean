import Proof.SecondTraceSectionExpansion
import Proof.PhysicalSecondTraceSection
import Proof.CanonicalFrameTraceSection
import Proof.FrameTraceRepresentatives
import Proof.SmoothHighCovariantSections
import Proof.UniformCompleteFirstAdjointGraph
import Proof.CompleteAdjointPhysicalSection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereFields

def completeFirstAdjointTensorJetL (d : Data)
    (S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (y : X) (i j : I) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (-(d.radius y)⁻¹*fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i)) • flatOneRaisingL j+
    hessianBilinear d.γ (fun x => Real.log (d.radius x)) y (d.frame y i) (d.frame y j) • sphereSobolevDegreeL+
    (firstFrameAdjointCovariantJetL d y (d.frame y i) j).comp (sphereSobolevInclusionL 1 0 (by norm_num))+S i j y

/-- Concrete genuine-section expansion of the actual second moving trace. -/
def expandedSecondTraceSection (d : Data)
    (A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (U : X → SphereSobolev 2) (V : I → X → SphereSobolev 1) (y : X) (i j : I) : SphereSobolev 0 :=
  let D := fun j x => highSectionCovariantDerivative d U x (d.frame x j)
  let C := completeFirstAdjointFamily d A G
  (oneSectionCovariantDerivative d (D j) y (d.frame y i)-
    ∑ k : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) j k •
      sphereSobolevInclusionL 1 0 (by norm_num) (D k y))+
    C i y (D j y)+C j y (D i y)+C i y (V j y)+
    completeFirstAdjointTensorJetL d S y i j (sphereSobolevInclusionL 2 1 (by norm_num) (U y))

structure SecondTraceSectionOutput (Y : Set X) (d : Data)
    (A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (φ : Field) (L : ℂ →L[ℝ] ℝ) (F : X × X → ℝ) (hF : ContDiff ℝ ∞ F) where
  representative : I → X × X → ℝ
  smooth : ∀ j,ContDiff ℝ ∞ (representative j)
  rep : ∀ j,∀ x ∈ Y,∀ w : UnitSphere,representative j (x,w.val)=
    L (frameAdjointField d.adjoint d.frame j φ (x,frameVector d.frame x w.val))
  normal : ∀ j,∀ x ∈ Y,completeFirstAdjointFamily d A G j x (ambientSobolevSection 1 (by norm_num) F hF x)=
    sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
      (ambientSphereL2 (representative j) (smooth j) x)
  second : ∀ y ∈ Y,∀ i j,(sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
    (expandedSecondTraceSection d A G S (ambientSobolevSection 2 (by norm_num) F hF)
      (fun k => ambientSobolevSection 1 (by norm_num) (representative k) (smooth k)) y i j) =ᵐ[sphereProbability]
    fun w : UnitSphere => L (frameCovariantTraceSecond d.γ d.adjoint d.frame i j φ (y,frameVector d.frame y w.val))

lemma Admissible.contDiffOn_completeFirstAdjointFamily {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hES : ∀ j,ContDiffOn ℝ ∞ (actualFrameFirstAdjointErrorFamily d A G j) Y) (j : I) :
    ContDiffOn ℝ ∞ (completeFirstAdjointFamily d A G j) Y := by
  have hL := contDiffOn_actualLeadingFrameAdjointL hY d hd.2.2.2.2.1.1
    (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne') (fun k => (hd.1.2.2.2.2.2.2.1 k).mono hSub) j
  have hC := (hd.contDiffOn_firstFrameAdjointCorrectionL hY hΩ hK j).clm_comp
    (contDiffOn_const (c:=sphereSobolevInclusionL 1 0 (by norm_num)))
  exact (hL.add hC).add (hES j)
end ShrinkingSpheres

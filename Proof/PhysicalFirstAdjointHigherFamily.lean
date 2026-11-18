import Proof.FirstFrameCorrectionAdjointHigher
import Proof.UniformPhysicalFrameSmoothAdjointHigher
import Proof.UniformFlatRaisingConstantAdjointHigher
import Proof.PhysicalFirstDerivativeCoordinates
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT : ℝ}

/-- Higher realization of the true full first-base adjoint, keeping the
SAME model, correction and actual error coefficients. -/
def firstDerivativeAdjointHigherFamily (P : PhysicalPrincipalData Y d CF CT)
    (AR : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (AE : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (y : X) (j : I) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  ((∑ i : I,((frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
      frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i)*
      scaledFrameLogRadius d.radius d.frame i y) • degreeHigherL)+
    (2:ℝ) • (∑ i : I,(frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j-
      (if i=j then 1 else 0)) • AR i))+
    d.radius y • (∑ i : I,(frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
      frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i) •
      (firstFrameCorrectionAdjointHigherL d y i+AE i y))

lemma firstDerivativeAdjointHigherFamily_balanced (P : PhysicalPrincipalData Y d CF CT)
    (AR : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (AE : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (y : X)
    (hR : ∀ i,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (AR i)=
      (flatHalfRaisingL i).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hE : ∀ i,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (AE i y)=
      (P.first.low i y).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (j : I) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (P.firstDerivativeAdjointHigherFamily AR AE y j)=
    (P.firstDerivativeHalfL y j).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  let Adj : (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) →L[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hAdd (A B : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :
      (A+B).adjoint=A.adjoint+B.adjoint := map_add Adj A B
  have hSum (A : I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :
      (∑ i : I,A i).adjoint=∑ i : I,(A i).adjoint := map_sum Adj A Finset.univ
  have hSm (c : ℝ) (A : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :
      (c • A).adjoint=c • A.adjoint := map_smul Adj c A
  simp only [firstDerivativeAdjointHigherFamily,firstDerivativeHalfL,principalModelFirstDerivativeHalfL,
    ActualFrameErrorEndpointPair.principalFirstDerivativeHalfL,hAdd,hSum,hSm]
  apply ContinuousLinearMap.ext
  intro u
  have hR' := fun i => DFunLike.congr_fun (hR i) u
  have hE' := fun i => DFunLike.congr_fun (hE i) u
  have hC' := fun i => DFunLike.congr_fun (firstFrameCorrectionAdjointHigherL_balanced d y i) u
  have hD' := DFunLike.congr_fun degreeHigherL_adjoint_pair u
  simp only [ContinuousLinearMap.comp_apply] at hR' hE' hC' hD'
  simp only [ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sum_apply,_root_.smul_apply,
    map_add,map_sum,map_smul,hR',hE',hC',hD',degreeHalfL]

lemma firstDerivativeAdjointHigherFamily_smooth {Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : PhysicalPrincipalData Y d CF CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (AR : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (AE : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hAE : ∀ i,ContDiffOn ℝ ∞ (AE i) Y) (j : I) :
    ContDiffOn ℝ ∞ (fun y => P.firstDerivativeAdjointHigherFamily AR AE y j) Y := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hQ := fun i k => hd.contDiffOn_framePrincipalCoefficient hSub hK i k
  have hT := fun i => contDiffOn_scaledFrameLogRadius hY hd.2.2.2.2.1.1
    (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
    (fun k => (hd.1.2.2.2.2.2.2.1 k).mono hSub) i
  apply ContDiffOn.add
  · apply ContDiffOn.add
    · exact ContDiffOn.sum (fun i _ => (((hQ i j).add (hQ j i)).mul (hT i)).smul contDiffOn_const)
    · exact (ContDiffOn.sum (fun i _ => ((hQ i j).sub contDiffOn_const).smul contDiffOn_const)).const_smul (2:ℝ)
  · apply hd.2.2.2.2.1.1.smul
    exact ContDiffOn.sum (fun i _ => ((hQ i j).add (hQ j i)).smul
      ((hd.contDiffOn_firstFrameCorrectionAdjointHigherL hY hΩ hK i).add (hAE i)))
end PhysicalPrincipalData
end ShrinkingSpheres

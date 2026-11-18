import Proof.LeadingPrincipalModelSection
import Proof.ActualPrincipalSectionAssembly
import Proof.PrincipalAdjointProductCollection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

def principalFirstRemainderSection (d : Data)
    (A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (U : X → SphereSobolev 2) (y : X) : SphereSobolev 0 :=
  let D := fun j => highSectionCovariantDerivative d U y (d.frame y j)
  let B := fun i v => firstFrameCorrectionCoarseFamily d i y v+actualFrameFirstAdjointErrorFamily d A G i y v
  d.radius y • (∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j •
    (B i (D j)+B j (D i)))

def principalCovariantRemainderSection (d : Data)
    (S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (U : X → SphereSobolev 2) (y : X) : SphereSobolev 0 :=
  let u := sphereSobolevInclusionL 2 1 (by norm_num) (U y)
  d.radius y • (∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j •
    (firstFrameAdjointCovariantJetL d y (d.frame y i) j (sphereSobolevInclusionL 1 0 (by norm_num) u)+S i j y u))

/-- Exact physical principal bookkeeping. The remaining product difference
is precisely the SAME seven controlled groups in the balanced product
collection; no new adjoint representatives or error lifts are selected. -/
lemma expandedPrincipalSection_leading_remainder (d : Data)
    (A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (U : X → SphereSobolev 2) (V : I → X → SphereSobolev 1) (y : X) :
    let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
    expandedPrincipalSection d A G S U V y=
      d.radius y • (∑ i : I,∑ j : I,q i j • leadingSecondTraceSection d U y i j)+
      principalFirstRemainderSection d A G U y+principalCovariantRemainderSection d S U y+
      d.radius y • (∑ i : I,∑ j : I,q i j • completeFirstAdjointFamily d A G i y (V j y))-
      principalLeadingAdjointProductValue d y (U y) := by
  dsimp only
  let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
  let D := fun j => highSectionCovariantDerivative d U y (d.frame y j)
  let u := sphereSobolevInclusionL 2 1 (by norm_num) (U y)
  let f := fun k => fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y k)
  let B := fun i v => firstFrameCorrectionCoarseFamily d i y v+actualFrameFirstAdjointErrorFamily d A G i y v
  let K := fun i j => firstFrameAdjointCovariantJetL d y (d.frame y i) j
    (sphereSobolevInclusionL 1 0 (by norm_num) u)+S i j y u
  let P := fun i j => actualLeadingFrameAdjointL d i y
    ((d.radius y)⁻¹ • flatTwoRaisingL j (U y)+f j • sphereSobolevShiftedDegreeL 2 (U y))
  have hPoint (i j : I) : expandedSecondTraceSection d A G S U V y i j=
      leadingSecondTraceSection d U y i j+(B i (D j)+B j (D i))+K i j+
        completeFirstAdjointFamily d A G i y (V j y)-P i j := by
    dsimp only [expandedSecondTraceSection,leadingSecondTraceSection,highSectionCovariantHessian,B,D,K,P,u,f]
    simp only [completeFirstAdjointFamily,completeFirstAdjointTensorJetL,
      _root_.add_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply]
    abel
  have hSum := Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl
    (fun i _ => Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl
      (fun j _ => congrArg (fun z : SphereSobolev 0 => q i j • z) (hPoint i j)))
  have h := congrArg (fun z : SphereSobolev 0 => d.radius y • z) hSum
  simpa only [smul_add,smul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    expandedPrincipalSection,principalFirstRemainderSection,principalCovariantRemainderSection,
    principalLeadingAdjointProductValue,q,B,D,K,P,u,f] using h

namespace SecondTraceSectionOutput
variable {Y : Set X} {d : Data}
  {A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {φ : Field} {L : ℂ →L[ℝ] ℝ} {F : X × X → ℝ} {hF : ContDiff ℝ ∞ F}

/-- Full actual principal residual after removing the SAME leading raising
section and canonical J. Every product error uses the physical second-trace
witness and its compatible endpoints; the rQ tensor square is retained. -/
lemma principal_residual_balanced (P : SecondTraceSectionOutput Y d A G S φ L F hF)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[nhds z] (fun _ => (1:ℝ)))
    {CE : ℝ} (E : ActualFrameErrorEndpointPair Y d A G CE) {y : X} (hy : y ∈ Y)
    (hr : d.radius y ≠ 0)
    (hSym : ∀ a b,principal d.γ d.g₂ y a b=principal d.γ d.g₂ y b a)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    let U := ambientSobolevSection 2 (by norm_num) F hF
    let u := U y
    let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (expandedPrincipalSection d A G S U
        (fun j => ambientSobolevSection 1 (by norm_num) (P.representative j) (P.smooth j)) y-
        (2:ℝ) • (∑ i : I,flatOneRaisingL i (highSectionModelPlus d U y i))-
        firstCorrectionCrossRemainderL Q d y (sphereSobolevInclusionL 2 1 (by norm_num) u))=
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (d.radius y • (∑ i : I,∑ j : I,q i j • modelPlusTensorSection d U y i j)+
          (2:ℝ) • (∑ i : I,∑ j : I,(q i j-(if i=j then 1 else 0)) • flatOneRaisingL i (highSectionModelPlus d U y j))+
          pureAngularPrincipalPerturbationL d y u+
          principalFirstRemainderSection d A G U y+principalCovariantRemainderSection d S U y+
          principalRaisingCorrectionPerturbationL d y (sphereSobolevInclusionL 2 1 (by norm_num) u)+
          principalDegreeCorrectionCrossL d y (sphereSobolevInclusionL 2 1 (by norm_num) u)+
          principalCorrectionProductL 0 d y (sphereSobolevInclusionL 2 0 (by norm_num) u))+
      E.principalRaisingCrossL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)+
      E.principalDegreeCrossL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)+
      E.principalCorrectionCrossL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)+
      E.radiusPrincipalProductL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u) := by
  dsimp only
  let U := ambientSobolevSection 2 (by norm_num) F hF
  let u := U y
  let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
  let Inc := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  let V := fun j => ambientSobolevSection 1 (by norm_num) (P.representative j) (P.smooth j)
  let T := (2:ℝ) • (∑ i : I,flatOneRaisingL i (highSectionModelPlus d U y i))
  let Core := d.radius y • (∑ i : I,∑ j : I,q i j • modelPlusTensorSection d U y i j)+
    (2:ℝ) • (∑ i : I,∑ j : I,(q i j-(if i=j then 1 else 0)) • flatOneRaisingL i (highSectionModelPlus d U y j))+
    pureAngularPrincipalPerturbationL d y u
  let Leading := d.radius y • (∑ i : I,∑ j : I,q i j • leadingSecondTraceSection d U y i j)
  let Product := d.radius y • (∑ i : I,∑ j : I,q i j • completeFirstAdjointFamily d A G i y (V j y))
  let RF := principalRaisingCorrectionCrossL d y (sphereSobolevInclusionL 2 1 (by norm_num) u)
  let J := firstCorrectionCrossRemainderL Q d y (sphereSobolevInclusionL 2 1 (by norm_num) u)
  let RP := principalRaisingCorrectionPerturbationL d y (sphereSobolevInclusionL 2 1 (by norm_num) u)
  have hCollect := congrArg Inc (expandedPrincipalSection_leading_remainder d A G S U V y)
  have hLeading : Leading=T+Core := by
    have h := leadingPrincipalSection_model_split d U y hr hSym hFrame
    exact h.trans (by dsimp only [T,Core,u,q];abel)
  have hModel := congrArg Inc hLeading
  have hProduct := P.principal_adjoint_product_balanced E hy hr
  have hRF : RF-J=RP := by
    exact DFunLike.congr_fun (principalRaisingCorrectionCrossL_sub_J Q hQ d y)
      (sphereSobolevInclusionL 2 1 (by norm_num) u)
  have hRFM := congrArg Inc hRF
  simp only [map_add,map_sub] at hCollect hModel hRFM
  have hReorder {W : Type} [AddCommGroup W]
      (p t j l c b k w a rf df ff e1 e2 e3 e4 rp : W)
      (hp : p=l+b+k+w-a) (hl : l=t+c)
      (hw : w=a+rf+df+ff+e1+e2+e3+e4) (hf : rf-j=rp) :
      p-t-j=c+b+k+rp+df+ff+e1+e2+e3+e4 := by
    have hrf := (sub_eq_iff_eq_add).1 hf
    rw [hp,hl,hw,hrf]
    abel
  have h := hReorder _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hCollect hModel hProduct hRFM
  simpa only [map_add,map_sub,Inc,Core,T,RP,J,u,U,q] using h
end SecondTraceSectionOutput
end ShrinkingSpheres

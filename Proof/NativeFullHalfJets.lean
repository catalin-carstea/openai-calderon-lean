import Proof.NativeFullHalfResponse
import Proof.SmoothFiniteAdjointJets
import Proof.NormalFrameRelativeHalfTaylorJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.NormalFrameRelativeResponsePacket
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma fullHalf_three_jet_bounds
    {Y Ω : Set X} {d : Data} {y : X} {Z C CI CW : ℝ}
    {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
      (frameVectorLinear d.frame y) (d.radius y) 4 Z C}
    (t : NormalFrameRelativeResponsePacket q) (V : t.SymmetricAdjointDomain)
    (hZ : 2 ≤ Z) (hC : 0 ≤ C) (hCW : 0 ≤ CW)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (point : NormalFrameRelativeNativePointData q F0 CI CW) :
    let B := |lowRadialTaylorJetBudget 3 2 CW 5 C C C|+firstLowRadialJetConstant*C+‖fixedLowRadialL‖
    SmoothFiniteJetBound t.fullHalfResponse ((y,frameVectorLinear d.frame y),0) 3 B ∧
      SmoothFiniteJetBound t.fullHalfAdjoint ((y,frameVectorLinear d.frame y),0) 3 B := by
  intro B
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let L := commonSupportLowRadialErrorL q.a q.smooth q.support q.compact q.supported
  let F := commonSupportLowFirstRadialL q.a1 q.firstSmooth q.support q.compact q.firstSupported 1
  let CL := |lowRadialTaylorJetBudget 3 2 CW 5 C C C|
  let CF := firstLowRadialJetConstant*C
  have hCL : 0 ≤ CL := abs_nonneg _
  have hCF : 0 ≤ CF := mul_nonneg firstLowRadialJetConstant_nonneg hC
  have hFSm : ContDiffAt ℝ ∞ F p0 :=
    (contDiff_commonSupport_lowFirstRadial_one q.a1 q.firstSmooth q.support q.compact q.firstSupported).contDiffAt
  have hWeak (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
      (commonSupportZeroWeakEnergy q.a q.smooth p).IsInvertible :=
    isInvertible_of_bilinear_coercive _ (V.coercive p hp)
  have hLSm : ContDiffAt ℝ ∞ L p0 :=
    (contDiffOn_commonSupportLowRadialErrorL q.a q.smooth q.support q.compact q.supported V.domain hWeak V.normal).contDiffAt
      (V.domainOpen.mem_nhds V.pointMem)
  have hHalf : SmoothFiniteJetBound q.halfTaylor p0 3 (CL*(d.radius y)^2) :=
    ⟨by positivity,hLSm.sub (hFSm.const_smul (d.radius y)),
      q.native_half_taylor_higher_jets 3 hZ hC hCW hr hr1 F0 hF0 point⟩
  have hFirst : SmoothFiniteJetBound F p0 3 CF := by
    refine ⟨hCF,hFSm,?_⟩
    intro n hn
    apply norm_iteratedFDeriv_commonSupport_lowFirstRadial_one_le q.a1 q.firstSmooth q.support q.compact q.firstSupported
      p0 n C hC
    intro i j k x hx
    have hxZ : ‖x‖ ≤ Z := by
      have hh : ‖x‖ ≤ 2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using unitBall_subset_closedBall_two hx
      exact hh.trans hZ
    exact q.firstMixedJets x hxZ n k.val (by omega) i j
  have hrr : (d.radius y)^2 ≤ 1 := by nlinarith only [hr,hr1]
  have hHalf' := hHalf.weaken ((mul_le_mul_of_nonneg_left hrr hCL).trans_eq (mul_one _))
  have hScaled := hFirst.const_smul (d.radius y)
  rw [abs_of_nonneg hr] at hScaled
  have hScaled' := hScaled.weaken ((mul_le_mul_of_nonneg_right hr1 hCF).trans_eq (one_mul _))
  have hSum := (hHalf'.add hScaled').add (SmoothFiniteJetBound.constant fixedLowRadialL p0 3)
  have hEq : t.fullHalfResponse = fun p => (q.halfTaylor p+d.radius y • F p)+fixedLowRadialL := by
    funext p
    change L p+fixedLowRadialL = (L p-d.radius y • F p+d.radius y • F p)+fixedLowRadialL
    abel
  have hFull : SmoothFiniteJetBound t.fullHalfResponse p0 3 B := by
    rw [hEq]
    exact hSum
  exact ⟨hFull,hFull.adjoint⟩
end ShrinkingSpheres.NormalFrameRelativeResponsePacket

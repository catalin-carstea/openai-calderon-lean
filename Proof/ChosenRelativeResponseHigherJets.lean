import Proof.ChosenRelativeCoefficientHigherJets
import Proof.NormalFrameRelativeResponsePacket
import Proof.RadialConormalReconstruction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N0 : ℕ} {Z C0 : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N0 Z C0}

/-- Higher geometric budgets give every prescribed forward jet of a
    PREVIOUSLY selected response. The compatible midpoint construction is
    compared on one common open neighborhood, so all its jets transfer to
    the SAME response rather than to unrelated point witnesses. -/
theorem forward_higher_jets_of_budget (t : NormalFrameRelativeResponsePacket q)
    (N : ℕ) (C CI CW : ℝ) (hBudget : NormalFrameRelativeCoefficientHigherBudget q (N+1) C)
    (hZ : 2 ≤ Z) (hC : 0 ≤ C) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (point : NormalFrameRelativeNativePointData q F0 CI CW) :
    ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n t.forwardTaylor ((y,frameVectorLinear d.frame y),0)‖ ≤
      normalFrameRelativeMidpointJetBudget N CI CW C*(d.radius y)^2 := by
  let qH := q.withHigherJetBudget (N+1) C hBudget
  have pointH : NormalFrameRelativeNativePointData qH F0 CI CW :=
    ⟨point.strong,point.strongNorm,point.flatStrong,point.flatStrongNorm,point.weak,point.weakNorm,
      point.normal,point.normalNorm,point.coercive⟩
  obtain ⟨V,hV,hpV,hSub,R,hR,hRestrict,hSmooth,hJets⟩ :=
    qH.native_midpoint_higher_jets N hZ hC hCI hCW hr hr1 F0 hF0 pointH
  let F := commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported
  have hEq (p : NormalFrameRelativeParameter) (hp : p ∈ V) (hpD : p ∈ t.domain) :
      t.response p = R p := by
    apply midpoint_radial_eq_of_coefficient_restrictions (t.response p) (R p) (F p) (F p)
      (fun _ _ => rfl) (t.highRestriction p hpD)
    exact hRestrict p hp
  have hGerm : t.forwardTaylor =ᶠ[𝓝 (((y,frameVectorLinear d.frame y),0))]
      (fun p => R p-d.radius y •
        (coarseFirstRadialVariationL 1 (normalFrameRelativeFirstCovector d.γ d.g₁ p)).comp
          (sphereSobolevInclusionL 1 0 (by norm_num))) := by
    filter_upwards [hV.mem_nhds hpV,t.domainOpen.mem_nhds t.pointMem] with p hp hpD
    unfold forwardTaylor
    rw [hEq p hp hpD]
  intro n hn
  rw [(hGerm.iteratedFDeriv ℝ n).eq_of_nhds]
  exact hJets n hn

/-- The actual adjoint formula of that SAME previously selected response
    retains the higher quadratic gain from its native inverse and coefficient
    jets. The only radius restriction is quantitative and uniform in the data. -/
theorem adjoint_higher_jets_of_budget (t : NormalFrameRelativeResponsePacket q)
    (N : ℕ) (C CI CW : ℝ) (hBudget : NormalFrameRelativeCoefficientHigherBudget q (N+1) C)
    (hZ : 2 ≤ Z) (hC : 0 ≤ C) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (point : NormalFrameRelativeNativePointData q F0 CI CW)
    (hSmall : (2*(18*coarseOneBoundaryBundleBudget)*C)*d.radius y ≤ (1/2:ℝ)) :
    ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n t.adjointTaylor ((y,frameVectorLinear d.frame y),0)‖ ≤
      normalFrameRelativeAdjointHigherJetBudget N C (normalFrameRelativeMidpointJetBudget N CI CW C)*(d.radius y)^2 := by
  let qH := q.withHigherJetBudget (N+1) C hBudget
  let CF := normalFrameRelativeMidpointJetBudget N CI CW C
  have hCF : 0 ≤ CF := by dsimp only [CF,normalFrameRelativeMidpointJetBudget];positivity
  have hForward := t.forward_higher_jets_of_budget N C CI CW hBudget hZ hC hCI hCW hr hr1 F0 hF0 point
  obtain ⟨hOne,hOneNorm,hAdjoint⟩ := qH.native_adjoint_higher_jets N hZ hC hCF hr hr1 F0 hF0
    point.flatStrong t.response (t.smooth.contDiffAt (t.domainOpen.mem_nhds t.pointMem)) hForward hSmall
  exact hAdjoint

end NormalFrameRelativeResponsePacket
end ShrinkingSpheres

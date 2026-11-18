import Proof.NormalFrameRelativeHalfTaylorJets
import Proof.NormalFrameRelativeNativePointData
import Proof.CommonSupportMidpointNeighborhood
import Proof.CommonSupportLowRadialTaylorHigherJets
import Proof.CommonSupportStrongPoissonTaylorHigherJets
import Proof.CommonSupportRadialMidpointHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def normalFrameRelativeMidpointJetBudget (N : ℕ) (CI CW C : ℝ) : ℝ :=
  (|lowRadialTaylorJetBudget N 2 CW 5 C C C|+
    |‖fixedHalfOutwardTraceL‖*strongPoissonTaylorJetBudget N CI CI C C C|)/2

/-- The uniform genuine geometric pair feeds the SAME native strong/weak
    inverses and compatible midpoint. Every prescribed mixed jet retains r². -/
theorem NormalFrameRelativeCoefficientJetFamily.native_midpoint_higher_jets
    {Y Ω : Set X} {d : Data} {y : X} (N : ℕ) {Z C CI CW : ℝ}
    (q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
      (frameVectorLinear d.frame y) (d.radius y) (N+1) Z C)
    (hZ : 2 ≤ Z) (hC : 0 ≤ C) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (t : NormalFrameRelativeNativePointData q F0 CI CW) :
    let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    ∃ V : Set NormalFrameRelativeParameter,IsOpen V ∧ p0 ∈ V ∧ V ⊆ q.domain ∧
      ∃ R : NormalFrameRelativeParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ContDiffOn ℝ ∞ R V ∧
        (∀ p ∈ V,(R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
          (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
            (actualHighRadialErrorL (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p))) ∧
        let T := fun p => R p-d.radius y •
          (coarseFirstRadialVariationL 1 (normalFrameRelativeFirstCovector d.γ d.g₁ p)).comp
            (sphereSobolevInclusionL 1 0 (by norm_num))
        ContDiffAt ℝ ∞ T p0 ∧ ∀ n : ℕ,n ≤ N →
          ‖iteratedFDeriv ℝ n T p0‖ ≤ normalFrameRelativeMidpointJetBudget N CI CW C*(d.radius y)^2 := by
  intro p0
  let r := d.radius y
  let F := commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported
  let F1 := commonSupportMatrixFamily 2 q.a1 q.firstSmooth q.support q.compact q.firstSupported
  let CL := |lowRadialTaylorJetBudget N 2 CW 5 C C C|
  let CH := |‖fixedHalfOutwardTraceL‖*strongPoissonTaylorJetBudget N CI CI C C C|
  have hFlatB (z : X) (hz : z ∈ (ballOpens:Set X)) := hF0 z (unitBall_subset_closedBall_two hz)
  have hxZ (x : X) (hx : x ∈ (ballOpens:Set X)) : ‖x‖ ≤ Z := by
    have hh : ‖x‖ ≤ 2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using unitBall_subset_closedBall_two hx
    exact hh.trans hZ
  have hAJets (l : ℕ) (hl : l ≤ N) (i j : I) (k : Fin 2) (x : X) (hx : x ∈ (ballOpens:Set X)) :
      ‖iteratedFDeriv ℝ l (fun p => iteratedFDeriv ℝ k.val (fun z => q.a (p,z) i j) x) p0‖ ≤ C :=
    q.coefficientMixedJets x (hxZ x hx) l k.val (by omega) i j
  have hFirstJets (l : ℕ) (hl : l ≤ N) (i j : I) (k : Fin 2) (x : X) (hx : x ∈ (ballOpens:Set X)) :
      ‖iteratedFDeriv ℝ l (fun p => iteratedFDeriv ℝ k.val (fun z => q.a1 (p,z) i j) x) p0‖ ≤ C :=
    q.firstMixedJets x (hxZ x hx) l k.val (by omega) i j
  have hRemainderJets (l : ℕ) (hl : l ≤ N) (i j : I) (k : Fin 2) (x : X) (hx : x ∈ (ballOpens:Set X)) :
      ‖iteratedFDeriv ℝ l (fun p => iteratedFDeriv ℝ k.val (fun z => (q.affineCoefficient (p,z)-(1:Mat)) i j) x) p0‖ ≤ C*r^2 :=
    q.remainderMixedJets x (hxZ x hx) l k.val (by omega) i j
  have hLow := q.native_half_taylor_higher_jets N hZ hC hCW hr hr1 F0 hF0 t
  have hHigh := commonSupport_strong_poisson_taylor_higher_jets
    q.a q.a1 q.affineCoefficient q.smooth q.firstSmooth q.affineSmooth
    q.support q.support q.support q.compact q.compact q.compact q.supported q.firstSupported q.affineSupported
    r (fun _ => rfl) F0 hFlatB p0 N CI CI C C C hr hr1 hCI hCI hC hC hC
    t.strong t.flatStrong t.strongNorm t.flatStrongNorm hAJets hFirstJets hRemainderJets
  have hNormal0 : (negativeBoundaryCoefficientMulL (normalCoefficientJet (F p0))).IsInvertible := by
    rw [← commonSupport_negative_normal_multiplier_eq]
    exact t.normal
  obtain ⟨V,hV,hpV,hSub,hCoercive,hStrong,hNormal,R,hR,hRestrict⟩ := exists_commonSupport_midpoint_neighborhood
    q.a q.smooth q.support q.compact q.supported p0 q.domain q.domainOpen q.pointMem t.coercive t.strong hNormal0
  have hFirst (p : NormalFrameRelativeParameter) (hp : p ∈ V) (z : X) (hz : z ∈ Metric.closedBall (0:X) 2) :
      q.a1 (p,z) = normalFrameRelativeFirstCovector d.γ d.g₁ p z • (1:Mat) :=
    q.firstScalar p (hSub hp) z (Metric.closedBall_subset_closedBall hZ hz)
  have hLowNorm (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n (fun p =>
      commonSupportLowRadialErrorL q.a q.smooth q.support q.compact q.supported p-
      r • commonSupportLowFirstRadialL q.a1 q.firstSmooth q.support q.compact q.firstSupported 1 p) p0‖ ≤ CL*r^2 :=
    hLow n hn
  have hHighNorm (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n (fun p =>
      actualHighRadialErrorL (F p)-r • highFirstRadialVariationL F0 (F1 p) 1) p0‖ ≤ CH*r^2 :=
    ((hHigh n hn).2.1).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg r))
  have hMid := commonSupport_radial_midpoint_higher_jet_data
    q.a q.a1 q.smooth q.firstSmooth q.support q.support q.compact q.compact q.supported q.firstSupported
    F0 hFlatB (normalFrameRelativeFirstCovector d.γ d.g₁) R p0 V hV hpV N r CL CH
    (abs_nonneg _) (abs_nonneg _) (hR.contDiffAt (hV.mem_nhds hpV))
    (q.covectorSmooth.contDiffAt (q.domainOpen.mem_nhds q.pointMem))
    hCoercive hStrong hNormal hFirst hRestrict hLowNorm hHighNorm
  exact ⟨V,hV,hpV,hSub,R,hR,hRestrict,hMid⟩

end ShrinkingSpheres

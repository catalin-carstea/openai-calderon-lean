import Proof.CommonSupportGainMultiplierContinuity
import Proof.ContinuousLinearFamilyMovingArgument
import Proof.NormalFrameMultiplierGainCurveGerm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

attribute [local irreducible] radialTaylorMultiplierInMultiplierL radialTaylorMultiplierCommutatorL
  nativeBulkMultiplierForcingInMultiplierL operatorMultiplierTaylorInMultiplierL

namespace NormalFrameMultiplierGainFamily
variable {d : Data} {A : NormalFrameParameter × X → Mat} {hA : ContDiff ℝ ∞ A}
  {S : Set X} {hS : IsCompact S} {hz : ∀ p z,z ∉ S → A (p,z) = 0}
  {F0 : SmoothCoefficientMatrix 2}
  {ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
    ((volume:Measure X).restrict ballOpens)}
  {r0 : ℝ} {V : Set NormalFrameParameter} {p0 : NormalFrameParameter}
  (T : NormalFrameMultiplierGainFamily d A hA S hS hz F0 ha0 r0 V p0)

def gainInMultiplier (p : NormalFrameParameter) : SmoothCoefficientJets 3 →L[ℝ]
    (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :=
  radialTaylorMultiplierInMultiplierL (commonSupportMatrixFamily 2 A hA S hS hz p) F0
    (commonSupportMatrixFamily 2 T.first T.first_smooth T.first_support T.first_support_compact T.first_vanish p)
    (T.principal_mem p) ha0 (T.first_mem p) r0

lemma gainInMultiplier_apply (p : NormalFrameParameter) (Q : SmoothCoefficientJets 3) :
    T.gainInMultiplier p Q = T.gain Q p := radialTaylorMultiplierInMultiplierL_apply ..

variable
  (hStrong : ∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
    (commonSupportMatrixFamily 2 A hA S hS hz p)).IsInvertible)
  (hCoercive : ∀ p ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp A hA p)))

include hStrong hCoercive

theorem gainInMultiplier_continuousOn : ContinuousOn T.gainInMultiplier T.domain := by
  exact continuousOn_commonSupport_gainInMultiplier A T.first hA T.first_smooth S T.first_support
    hS T.first_support_compact hz T.first_vanish F0 T.principal_mem T.first_mem ha0 r0 T.domain
    (fun p hp => hStrong p (T.domain_subset hp)) (fun p hp => hCoercive p (T.domain_subset hp))

/-- Exact differentiation for a genuinely moving multiplier: the fixed-Q
parameter derivative PLUS the SAME gained point operator on the actual
multiplier derivative. No multiplier term is discarded. -/
theorem hasDerivAt_gain_moving_multiplier
    (c : ℝ → NormalFrameParameter) (v : NormalFrameParameter) (hc : HasDerivAt c v 0) (hc0 : c 0 = p0)
    (q : ℝ → SmoothCoefficientJets 3) (q1 : SmoothCoefficientJets 3) (hq : HasDerivAt q q1 0) :
    HasDerivAt (fun t => T.gain (q t) (c t))
      (fderiv ℝ (T.gain (q 0)) p0 v+T.gain q1 p0) 0 := by
  have hG : DifferentiableAt ℝ (T.gain (q 0)) p0 :=
    ((T.gain_contDiffOn (q 0)).1.contDiffAt (T.domain_open.mem_nhds T.point_mem)).differentiableAt (by simp)
  have hGc : HasFDerivAt (T.gain (q 0)) (fderiv ℝ (T.gain (q 0)) p0) (c 0) := by
    rw [hc0];exact hG.hasFDerivAt
  have hFixed : HasDerivAt (fun t => T.gain (q 0) (c t)) (fderiv ℝ (T.gain (q 0)) p0 v) 0 :=
    hGc.comp_hasDerivAt 0 hc
  have hL0 : ContinuousAt T.gainInMultiplier p0 :=
    (T.gainInMultiplier_continuousOn hStrong hCoercive).continuousAt (T.domain_open.mem_nhds T.point_mem)
  have hLc : ContinuousAt T.gainInMultiplier (c 0) := by rw [hc0];exact hL0
  have hFixedL : HasDerivAt (fun t => T.gainInMultiplier (c t) (q 0))
      (fderiv ℝ (T.gain (q 0)) p0 v) 0 := by
    simpa only [gainInMultiplier_apply] using hFixed
  have hResult := hasDerivAt_clm_apply_of_continuous_family (fun t => T.gainInMultiplier (c t)) q 0
    (fderiv ℝ (T.gain (q 0)) p0 v) q1 (hLc.comp hc.continuousAt) hFixedL hq
  simpa only [gainInMultiplier_apply,hc0] using hResult

/-- Curve form of the same rule, written with the genuine curve derivatives
so the rotation and actual-profile covariant jets can be combined exactly. -/
theorem deriv_gain_moving_multiplier_curve
    (c : ℝ → NormalFrameParameter) (v : NormalFrameParameter) (hc : HasDerivAt c v 0) (hc0 : c 0 = p0)
    (q : NormalFrameParameter → SmoothCoefficientJets 3) (hq : DifferentiableAt ℝ q p0) :
    deriv (fun t => T.gain (q (c t)) (c t)) 0 =
      deriv (fun t => T.gain (q p0) (c t)) 0+T.gain (deriv (fun t => q (c t)) 0) p0 := by
  have hqc : HasFDerivAt q (fderiv ℝ q p0) (c 0) := by rw [hc0];exact hq.hasFDerivAt
  have hqCurve : HasDerivAt (fun t => q (c t)) (fderiv ℝ q p0 v) 0 := hqc.comp_hasDerivAt 0 hc
  have hG : DifferentiableAt ℝ (T.gain (q p0)) p0 :=
    ((T.gain_contDiffOn (q p0)).1.contDiffAt (T.domain_open.mem_nhds T.point_mem)).differentiableAt (by simp)
  have hGc : HasFDerivAt (T.gain (q p0)) (fderiv ℝ (T.gain (q p0)) p0) (c 0) := by
    rw [hc0];exact hG.hasFDerivAt
  have hGCurve : HasDerivAt (fun t => T.gain (q p0) (c t)) (fderiv ℝ (T.gain (q p0)) p0 v) 0 :=
    hGc.comp_hasDerivAt 0 hc
  have hMoving := T.hasDerivAt_gain_moving_multiplier hStrong hCoercive c v hc hc0
    (fun t => q (c t)) (fderiv ℝ q p0 v) hqCurve
  simpa only [hc0,hqCurve.deriv,hGCurve.deriv] using hMoving.deriv

end NormalFrameMultiplierGainFamily
end ShrinkingSpheres

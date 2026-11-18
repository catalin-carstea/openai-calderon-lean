import Proof.NormalFrameRelativeHalfTaylorJets
import Proof.MidpointHalfCompatibility
import Proof.NativeRelativeDegreeHigherData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres.NormalFrameRelativeResponsePacket
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z C}
  {t : NormalFrameRelativeResponsePacket q}

lemma SymmetricAdjointDomain.contDiffOn_halfTaylor (V : t.SymmetricAdjointDomain) :
    ContDiffOn ℝ ∞ q.halfTaylor V.domain := by
  have hWeak (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
      (commonSupportZeroWeakEnergy q.a q.smooth p).IsInvertible :=
    isInvertible_of_bilinear_coercive _ (V.coercive p hp)
  exact (contDiffOn_commonSupportLowRadialErrorL q.a q.smooth q.support q.compact q.supported V.domain
    hWeak V.normal).sub
      ((contDiff_commonSupport_lowFirstRadial_one q.a1 q.firstSmooth q.support q.compact q.firstSupported).contDiffOn.const_smul (d.radius y))

lemma SymmetricAdjointDomain.halfTaylor_coarse_compatible (V : t.SymmetricAdjointDomain)
    (hZ : 2 ≤ Z) (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (t.forwardTaylor p) =
      (q.halfTaylor p).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  let F := commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported
  let F1 := commonSupportMatrixFamily 2 q.a1 q.firstSmooth q.support q.compact q.firstSupported
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
  let H := actualHighRadialErrorL (F p)-d.radius y • highFirstRadialVariationL F0 (F1 p) 1
  have hFlat (z : X) (hz : z ∈ (ballOpens:Set X)) := hF0 z (unitBall_subset_closedBall_two hz)
  have hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 ((1:ℝ) • F0)).IsInvertible :=
    strongDirichletOperator_isInvertible_of_elliptic fixedSobolevCalculus fixedDirichletRegularity 0 _
      (uniformlyEllipticOn_flat_coefficientMatrix F0 1 (by norm_num) hFlat)
  have hFirst (z : X) (hz : z ∈ Metric.closedBall (0:X) 2) : q.a1 (p,z) = ell z • (1:Mat) :=
    q.firstScalar p (t.sub (V.sub hp)) z (Metric.closedBall_subset_closedBall hZ hz)
  have hFirstMem : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 (F1 p) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens) := by
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact commonSupportEnergyMemLp q.a1 q.firstSmooth p
  have hLH : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H =
      (q.halfTaylor p).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
    actual_radial_taylor_endpoints_compatible q.a q.a1 q.smooth q.firstSmooth
      q.support q.support q.compact q.compact q.supported q.firstSupported p 1 (d.radius y) F0 (F p) (F1 p)
      ell (by norm_num) (V.coercive p hp) hFirstMem hFlat
      (fun z _ => congrArg (fun f : X → Mat => f z) (coefficientMatrixField_commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p))
      (fun z _ => congrArg (fun f : X → Mat => f z) (coefficientMatrixField_commonSupportMatrixFamily 2 q.a1 q.firstSmooth q.support q.compact q.firstSupported p))
      (fun w => hFirst w.val (Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall w.property)))
      (V.strong p hp) hInv0 (V.normal p hp)
  have hRH : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp H =
      (t.forwardTaylor p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
    symm
    apply midpoint_radial_taylor_high_restriction (t.response p) (F p) (F p) F0 (F1 p) 1 (d.radius y)
      (by norm_num) ell (t.highRestriction p (V.sub hp)) (fun _ _ => rfl) hFlat (fun z hzB k l => ?_) hInv0
    change coefficientMatrixField 2 (F1 p) z k l = ell z*(1:Mat) k l
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact congrArg (fun A : Mat => A k l) (hFirst z (unitBall_subset_closedBall_two hzB))
  exact midpoint_half_compatible_of_common_high (t.forwardTaylor p) (q.halfTaylor p) H hRH hLH

lemma SymmetricAdjointDomain.halfTaylor_physical_block (V : t.SymmetricAdjointDomain)
    (hZ : 2 ≤ Z) (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) (m n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (-(1/2:ℝ)) m (q.halfTaylor p (sphereSobolevSingleL (1/2:ℝ) n z)) =
      coarsePhysicalHarmonicBlock (t.forwardTaylor p) m n z := by
  have hh := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
    sphereSobolevCoefficientL (-(1/2:ℝ)) m (A (sphereSobolevSingleL 1 n z)))
      (V.halfTaylor_coarse_compatible hZ F0 hF0 p hp)
  simpa only [ContinuousLinearMap.comp_apply,sphereSobolevCoefficientL_inclusion,sphereSobolevInclusionL_single,
    coarsePhysicalHarmonicBlock] using hh.symm
end ShrinkingSpheres.NormalFrameRelativeResponsePacket

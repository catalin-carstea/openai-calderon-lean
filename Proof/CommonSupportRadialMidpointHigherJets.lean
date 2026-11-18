import Proof.MidpointFamilyHigherJets
import Proof.CommonSupportFirstRadialHigherJets
import Proof.CommonSupportMidpointRadialRegularity
import Proof.ActualRadialTaylorEndpointCompatibility
import Proof.MidpointFamilyDerivativeBound
import Proof.RadialRotationTaylorRestriction
import Proof.OperatorPoissonFamilyRegularity
import Proof.FlatCoefficientEllipticity
import Proof.RadialCorrectionLinear

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
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
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- Compatible actual low/high Taylor jets control every finite derivative
    of the SAME true midpoint family over an arbitrary finite parameter space. -/
theorem commonSupport_radial_midpoint_higher_jet_data
    (a a1 : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (hz1 : ∀ p z,z ∉ S1 → a1 (p,z) = 0)
    (F0 : SmoothCoefficientMatrix 2) (hF0 : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (ell : P → X →L[ℝ] ℝ) (R : P → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (x : P) (V : Set P) (hV : IsOpen V) (hx : x ∈ V) (N : ℕ) (r CL CH : ℝ)
    (hCL : 0 ≤ CL) (hCH : 0 ≤ CH)
    (hRDiff : ContDiffAt ℝ ∞ R x) (hEllDiff : ContDiffAt ℝ ∞ ell x)
    (hCoercive : ∀ p ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp a ha p)))
    (hInv : ∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 a ha S hS hz p)).IsInvertible)
    (hNormal : ∀ p ∈ V,(negativeBoundaryCoefficientMulL
      (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p))).IsInvertible)
    (hFirst : ∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,a1 (p,z) = ell p z • (1:Mat))
    (hRestrict : ∀ p ∈ V,(R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
        (actualHighRadialErrorL (commonSupportMatrixFamily 2 a ha S hS hz p)))
    (hLNorm : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (fun p => commonSupportLowRadialErrorL a ha S hS hz p-
      r • commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 1 p) x‖ ≤ CL*r^2)
    (hHigh : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (fun p => actualHighRadialErrorL (commonSupportMatrixFamily 2 a ha S hS hz p)-
      r • highFirstRadialVariationL F0 (commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 p) 1) x‖ ≤ CH*r^2) :
    let T := fun p => R p-r • (coarseFirstRadialVariationL 1 (ell p)).comp (sphereSobolevInclusionL 1 0 (by norm_num))
    ContDiffAt ℝ ∞ T x ∧ ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n T x‖ ≤ ((CL+CH)/2)*r^2 := by
  let F := commonSupportMatrixFamily 2 a ha S hS hz
  let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
  let L := fun p => commonSupportLowRadialErrorL a ha S hS hz p-r • commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 1 p
  let H := fun p => actualHighRadialErrorL (F p)-r • highFirstRadialVariationL F0 (F1 p) 1
  let T := fun p => R p-r • (coarseFirstRadialVariationL 1 (ell p)).comp (sphereSobolevInclusionL 1 0 (by norm_num))
  have hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 ((1:ℝ) • F0)).IsInvertible :=
    strongDirichletOperator_isInvertible_of_elliptic fixedSobolevCalculus fixedDirichletRegularity 0 _
      (uniformlyEllipticOn_flat_coefficientMatrix F0 1 (by norm_num) hF0)
  have hHSmooth := (contDiffOn_commonSupport_highRadialErrorL a ha S hS hz V hInv).sub
    ((contDiffOn_highFirstRadialVariationL_of_operator F1 F0 1 V
      (contDiff_commonSupport_fullCoefficientOperator 0 a1 ha1 S1 hS1 hz1).contDiffOn).const_smul r)
  have hHDiff : ContDiffAt ℝ ∞ H x := hHSmooth.contDiffAt (hV.mem_nhds hx)
  have hB : ContDiffAt ℝ ∞ (fun p => coarseFirstRadialVariationL 1 (ell p)) x := by
    have hFun : (fun p => coarseFirstRadialVariationL 1 (ell p)) = fun p => radialCorrectionCovectorL (ell p) := by
      funext p
      rw [coarseFirstRadialVariationL_normalized_covector,inv_one,one_smul]
    rw [hFun]
    exact radialCorrectionCovectorL.contDiff.contDiffAt.comp x hEllDiff
  have hTDiff : ContDiffAt ℝ ∞ T x := hRDiff.sub
    ((hB.clm_comp (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : P => sphereSobolevInclusionL 1 0 (by norm_num)) x)).const_smul r)
  have hWeak (p : P) (hp : p ∈ V) : (commonSupportZeroWeakEnergy a ha p).IsInvertible :=
    isInvertible_of_bilinear_coercive _ (hCoercive p hp)
  have hLDiff : ContDiffAt ℝ ∞ L x :=
    ((contDiffOn_commonSupportLowRadialErrorL a ha S hS hz V hWeak hNormal).contDiffAt (hV.mem_nhds hx)).sub
      (((contDiff_commonSupport_lowFirstRadial_one a1 ha1 S1 hS1 hz1).contDiffAt).const_smul r)
  have hFirstMem (p : P) : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 (F1 p) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens) := by
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact commonSupportEnergyMemLp a1 ha1 p
  have hLH (p : P) (hp : p ∈ V) :
      (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp (H p) =
        (L p).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
    have hComp := actual_radial_taylor_endpoints_compatible a a1 ha ha1 S S1 hS hS1 hz hz1 p 1 r F0 (F p) (F1 p)
      (ell p) (by norm_num) (hCoercive p hp) (hFirstMem p) hF0
      (fun z _ => congrArg (fun f : X → Mat => f z) (coefficientMatrixField_commonSupportMatrixFamily 2 a ha S hS hz p))
      (fun z _ => congrArg (fun f : X → Mat => f z) (coefficientMatrixField_commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 p))
      (fun w => hFirst p hp w.val (Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall w.property)))
      (hInv p hp) hInv0 (hNormal p hp)
    have hI := sphereSobolevInclusionL_eq_of_target_eq (1/2:ℝ) (-1/2:ℝ) (-(1/2:ℝ))
      (by norm_num) (by norm_num) (by ring)
    exact (congrArg (fun I => I.comp (H p)) hI).trans hComp
  have hTH (p : P) (hp : p ∈ V) :
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (H p) =
        (T p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
    symm
    apply midpoint_radial_taylor_high_restriction (R p) (F p) (F p) F0 (F1 p) 1 r (by norm_num) (ell p)
      (hRestrict p hp) (fun _ _ => rfl) hF0 (fun z hzB k l => ?_) hInv0
    change coefficientMatrixField 2 (F1 p) z k l = ell p z*(1:Mat) k l
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact congrArg (fun A : Mat => A k l) (hFirst p hp z (unitBall_subset_closedBall_two hzB))
  refine ⟨hTDiff,?_⟩
  intro n hn
  have hNorm := norm_iteratedFDeriv_midpoint_family_le L H T x hLDiff hHDiff hTDiff
    (by filter_upwards [hV.mem_nhds hx] with p hp;exact hLH p hp)
    (by filter_upwards [hV.mem_nhds hx] with p hp;exact hTH p hp)
    n (CL*r^2) (CH*r^2) (mul_nonneg hCL (sq_nonneg r)) (mul_nonneg hCH (sq_nonneg r))
    (hLNorm n hn) (hHigh n hn)
  exact hNorm.trans_eq (by ring)

end ShrinkingSpheres

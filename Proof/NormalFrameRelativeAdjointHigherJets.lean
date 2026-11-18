import Proof.ScalarFirstCovectorHigherJets
import Proof.CoarseOneBoundaryBundleCalculus
import Proof.CommonSupportCoarseOneBoundaryHigherJets
import Proof.RadialAdjointTaylorHigherJets
import Proof.CommonSupportRadialAdjointRegularity
import Proof.FirstRadialAdjointCorrectionIdentity
import Proof.NearIdentityInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxSynthPendingDepth 30
set_option synthInstance.maxHeartbeats 120000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] sphereSobolevDegreeL
local instance : CompleteSpace (SphereSobolev 1) := lp.completeSpace

def normalFrameRelativeAdjointInputBudget (C CJ : ℝ) : ℝ :=
  1+4*(18*coarseOneBoundaryBundleBudget)*C+CJ+6*C

def normalFrameRelativeAdjointHigherJetBudget (N : ℕ) (C CJ : ℝ) : ℝ :=
  radialAdjointTaylorHigherJetBudget N 2 (normalFrameRelativeAdjointInputBudget C CJ) ‖sphereSobolevDegreeL‖

theorem NormalFrameRelativeCoefficientJetFamily.native_adjoint_higher_jets
    {Y Ω : Set X} {g g₁ : MetricField} {E : X × X → X} {y : X} {L : X →L[ℝ] X}
    (N : ℕ) {r Z C CJ : ℝ}
    (q : NormalFrameRelativeCoefficientJetFamily Y Ω g g₁ E y L r (N+1) Z C)
    (hZ : 2 ≤ Z) (hC : 0 ≤ C) (hCJ : 0 ≤ CJ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (R : NormalFrameRelativeParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hR : ContDiffAt ℝ ∞ R ((y,L),0))
    (hForward : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (fun p => R p-r •
      (coarseFirstRadialVariationL 1 (normalFrameRelativeFirstCovector g g₁ p)).comp
        (sphereSobolevInclusionL 1 0 (by norm_num))) ((y,L),0)‖ ≤ CJ*r^2)
    (hSmall : (2*(18*coarseOneBoundaryBundleBudget)*C)*r ≤ (1/2:ℝ)) :
    (oneBoundaryCoefficientMulL (normalCoefficientJet
      (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported ((y,L),0)))).IsInvertible ∧
    ‖(oneBoundaryCoefficientMulL (normalCoefficientJet
      (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported ((y,L),0)))).inverse‖ ≤ 2 ∧
    ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (fun p =>
      radialAdjointFromResponseL (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p)
        (R p+sphereSobolevDegreeL)-sphereSobolevDegreeL-
        r • (radialCorrectionCovectorL (normalFrameRelativeFirstCovector g g₁ p)).adjoint.comp
          (sphereSobolevInclusionL 1 0 (by norm_num))) ((y,L),0)‖ ≤
        normalFrameRelativeAdjointHigherJetBudget N C CJ*r^2 := by
  let p0 : NormalFrameRelativeParameter := ((y,L),0)
  let CB := 18*coarseOneBoundaryBundleBudget
  let CC := normalFrameRelativeAdjointInputBudget C CJ
  let F := commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported
  let F1 := commonSupportMatrixFamily 2 q.a1 q.firstSmooth q.support q.compact q.firstSupported
  let B0 := fun p => coarseOneBoundaryBundle (F p)
  let B1 := fun p => coarseOneBoundaryBundle (F1 p)
  let BQ := fun p => B0 p-coarseOneBoundaryBundle F0-r • B1 p
  let M0 := fun p => (B0 p).1
  let M01 := fun p => (B1 p).1
  let M1 := fun p => (B0 p).2.1
  let M11 := fun p => (B1 p).2.1
  let T := fun p => (B0 p).2.2.1
  let Td := fun p => (B0 p).2.2.2
  let ell := normalFrameRelativeFirstCovector g g₁
  let B := fun p => radialCorrectionCovectorL (ell p)
  let Incl := sphereSobolevInclusionL 1 0 (by norm_num)
  let D := fun p => R p+sphereSobolevDegreeL
  let D1 := fun p => (B p).comp Incl
  let Da1 := fun p => (B p).adjoint.comp Incl
  have hCB : 0 ≤ CB := mul_nonneg (by norm_num) coarseOneBoundaryBundleBudget_nonneg
  have hCBC : 0 ≤ CB*C := mul_nonneg hCB hC
  have hCC : 0 ≤ CC := by dsimp only [CC,normalFrameRelativeAdjointInputBudget];positivity
  have hCBCle : CB*C ≤ CC := by dsimp only [CC,normalFrameRelativeAdjointInputBudget,CB];nlinarith only [hCBC,hCJ,hC]
  have h2CBCle : 2*CB*C ≤ CC := by dsimp only [CC,normalFrameRelativeAdjointInputBudget,CB];nlinarith only [hCBC,hCJ,hC]
  have hCJle : CJ ≤ CC := by dsimp only [CC,normalFrameRelativeAdjointInputBudget,CB];nlinarith only [hCBC,hC]
  have h6Cle : 6*C ≤ CC := by dsimp only [CC,normalFrameRelativeAdjointInputBudget,CB];nlinarith only [hCBC,hCJ]
  have hB0 : ContDiffAt ℝ ∞ B0 p0 := (contDiff_commonSupport_coarseOneBoundaryBundle q.a q.smooth q.support q.compact q.supported).contDiffAt
  have hB1 : ContDiffAt ℝ ∞ B1 p0 := (contDiff_commonSupport_coarseOneBoundaryBundle q.a1 q.firstSmooth q.support q.compact q.firstSupported).contDiffAt
  have hBQ : ContDiffAt ℝ ∞ BQ p0 := (hB0.sub contDiffAt_const).sub (hB1.const_smul r)
  have hM0 : ContDiffAt ℝ ∞ M0 p0 := hB0.fst
  have hM01 : ContDiffAt ℝ ∞ M01 p0 := hB1.fst
  have hM1 : ContDiffAt ℝ ∞ M1 p0 := hB0.snd.fst
  have hM11 : ContDiffAt ℝ ∞ M11 p0 := hB1.snd.fst
  have hT : ContDiffAt ℝ ∞ T p0 := hB0.snd.snd.fst
  have hTd : ContDiffAt ℝ ∞ Td p0 := hB0.snd.snd.snd
  have hxZ (x : X) (hx : x ∈ (ballOpens:Set X)) : ‖x‖ ≤ Z := by
    have hh : ‖x‖ ≤ 2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using unitBall_subset_closedBall_two hx
    exact hh.trans hZ
  have hB0J (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n B0 p0‖ ≤ CB*C :=
    norm_iteratedFDeriv_commonSupport_coarseOneBoundaryBundle_le q.a q.smooth q.support q.compact q.supported p0 n C hC
      (fun i j k x hx => q.coefficientMixedJets x (hxZ x hx) n k.val (by omega) i j)
  have hB1J (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n B1 p0‖ ≤ CB*C :=
    norm_iteratedFDeriv_commonSupport_coarseOneBoundaryBundle_le q.a1 q.firstSmooth q.support q.compact q.firstSupported p0 n C hC
      (fun i j k x hx => q.firstMixedJets x (hxZ x hx) n k.val (by omega) i j)
  have hBQJ (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n BQ p0‖ ≤ (CB*C)*r^2 :=
    (norm_iteratedFDeriv_commonSupport_coarseOneBoundaryBundle_affine_remainder_le q.a q.a1 q.affineCoefficient
      q.smooth q.firstSmooth q.support q.support q.compact q.compact q.supported q.firstSupported r (fun _ => rfl)
      F0 (fun z hz => hF0 z (unitBall_subset_closedBall_two hz)) p0 n (C*r^2) (by positivity)
      (fun i j k x hx => q.remainderMixedJets x (hxZ x hx) n k.val (by omega) i j)).trans_eq (by ring)
  have hP0 (n : ℕ) (hn : n ≤ N) := norm_iteratedFDeriv_coarseOneBoundaryBundle_components_le B0 p0 hB0 n _ (hB0J n hn)
  have hP1 (n : ℕ) (hn : n ≤ N) := norm_iteratedFDeriv_coarseOneBoundaryBundle_components_le B1 p0 hB1 n _ (hB1J n hn)
  have hPQ (n : ℕ) (hn : n ≤ N) := norm_iteratedFDeriv_coarseOneBoundaryBundle_components_le BQ p0 hBQ n _ (hBQJ n hn)
  have hFlat := coarseOneBoundaryBundle_flat F0 hF0
  have hQ0Eq : (fun p => (BQ p).1) = fun p => M0 p-ContinuousLinearMap.id ℝ (SphereSobolev 0)-r • M01 p := by
    funext p
    change (B0 p).1-(coarseOneBoundaryBundle F0).1-r • (B1 p).1 = _
    rw [hFlat]
  have hQ1Eq : (fun p => (BQ p).2.1) = fun p => M1 p-ContinuousLinearMap.id ℝ (SphereSobolev 1)-r • M11 p := by
    funext p
    change (B0 p).2.1-(coarseOneBoundaryBundle F0).2.1-r • (B1 p).2.1 = _
    rw [hFlat]
  have hQ0J (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n (fun p => M0 p-ContinuousLinearMap.id ℝ (SphereSobolev 0)-r • M01 p) p0‖ ≤ (CB*C)*r^2 := by
    rw [← hQ0Eq]
    exact (hPQ n hn).1
  have hQ1J (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n (fun p => M1 p-ContinuousLinearMap.id ℝ (SphereSobolev 1)-r • M11 p) p0‖ ≤ (CB*C)*r^2 := by
    rw [← hQ1Eq]
    exact (hPQ n hn).2.1
  have hDiff0 (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n (fun p => M0 p-ContinuousLinearMap.id ℝ (SphereSobolev 0)) p0‖ ≤ (2*CB*C)*r :=
    (norm_iteratedFDeriv_difference_of_affine_remainder_le M0 M01 _ p0 hM0 hM01 n r (CB*C) (CB*C)
      hr hr1 hCBC hCBC (hP1 n hn).1 (hQ0J n hn)).trans_eq (by ring)
  have hDiff1 (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n (fun p => M1 p-ContinuousLinearMap.id ℝ (SphereSobolev 1)) p0‖ ≤ (2*CB*C)*r :=
    (norm_iteratedFDeriv_difference_of_affine_remainder_le M1 M11 _ p0 hM1 hM11 n r (CB*C) (CB*C)
      hr hr1 hCBC hCBC (hP1 n hn).2.1 (hQ1J n hn)).trans_eq (by ring)
  have hTan : (fun p => (T p,Td p)) =ᶠ[𝓝 p0] (fun p => ((BQ p).2.2.1,(BQ p).2.2.2)) := by
    filter_upwards [q.domainOpen.mem_nhds q.pointMem] with p hp
    have hFirstTan := boundaryTangential_scalar_zero (F1 p) (ell p) (by
      intro w
      rw [coefficientMatrixField_commonSupportMatrixFamily]
      exact q.firstScalar p hp w.val (Metric.closedBall_subset_closedBall (by linarith only [hZ])
        (Metric.sphere_subset_closedBall w.property)))
    change (B1 p).2.2.1 = 0 ∧ (B1 p).2.2.2 = 0 at hFirstTan
    change (T p,Td p) = ((T p-(coarseOneBoundaryBundle F0).2.2.1-r • (B1 p).2.2.1),
      (Td p-(coarseOneBoundaryBundle F0).2.2.2-r • (B1 p).2.2.2))
    rw [hFlat]
    change (T p,Td p) = (T p-0-r • _,Td p-0-r • _)
    rw [hFirstTan.1,hFirstTan.2,smul_zero,sub_zero,sub_zero,sub_zero,sub_zero]
  have hTJ (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n T p0‖ ≤ (CB*C)*r^2 := by
    have he : T =ᶠ[𝓝 p0] (fun p => (BQ p).2.2.1) := hTan.mono (fun p hp => congrArg Prod.fst hp)
    rw [(he.iteratedFDeriv ℝ n).eq_of_nhds]
    exact (hPQ n hn).2.2.1
  have hTdJ (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n Td p0‖ ≤ (CB*C)*r^2 := by
    have he : Td =ᶠ[𝓝 p0] (fun p => (BQ p).2.2.2) := hTan.mono (fun p hp => congrArg Prod.snd hp)
    rw [(he.iteratedFDeriv ℝ n).eq_of_nhds]
    exact (hPQ n hn).2.2.2
  have hNear : ‖M1 p0-ContinuousLinearMap.id ℝ (SphereSobolev 1)‖ ≤ (1/2:ℝ) := by
    have hh := (hDiff1 0 (Nat.zero_le N)).trans hSmall
    simpa only [norm_iteratedFDeriv_zero] using hh
  obtain ⟨hNormal,hNormalNorm⟩ := near_identity_inverse_data (M1 p0) hNear
  have hEll : ContDiffAt ℝ ∞ ell p0 := q.covectorSmooth.contDiffAt (q.domainOpen.mem_nhds q.pointMem)
  have hB : ContDiffAt ℝ ∞ B p0 := radialCorrectionCovectorL.contDiff.contDiffAt.comp p0 hEll
  let Adj := (ContinuousLinearMap.adjoint : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) ≃ₗᵢ[ℝ]
    (SphereSobolev 0 →L[ℝ] SphereSobolev 0))
  have hBa : ContDiffAt ℝ ∞ (fun p => (B p).adjoint) p0 :=
    Adj.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp (f:=B) p0 hB
  have hBJ (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n B p0‖ ≤ 6*C :=
    (norm_iteratedFDeriv_clm_comp_le radialCorrectionCovectorL ell p0 hEll n).trans
      ((mul_le_mul norm_radialCorrectionCovectorL_le (q.firstCovectorJets hZ n hn) (norm_nonneg _) (by norm_num)).trans_eq (by ring))
  have hBaJ (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n (fun p => (B p).adjoint) p0‖ ≤ 6*C := by
    change ‖iteratedFDeriv ℝ n (Adj ∘ B) p0‖ ≤ _
    rw [LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hBJ n hn
  have hD1 : ContDiffAt ℝ ∞ D1 p0 := hB.clm_comp contDiffAt_const
  have hDa1 : ContDiffAt ℝ ∞ Da1 p0 := hBa.clm_comp contDiffAt_const
  have hD : ContDiffAt ℝ ∞ D p0 := hR.add contDiffAt_const
  have hIncl : ‖Incl‖ ≤ 1 := norm_sphereSobolevInclusionL_le 1 0 (by norm_num)
  have hD1J (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n D1 p0‖ ≤ 6*C :=
    (norm_iteratedFDeriv_operator_precomp_fixed_le B Incl p0 hB n).trans
      ((mul_le_mul hIncl (hBJ n hn) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hDa1J (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n Da1 p0‖ ≤ 6*C :=
    (norm_iteratedFDeriv_operator_precomp_fixed_le _ Incl p0 hBa n).trans
      ((mul_le_mul hIncl (hBaJ n hn) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hForwardEq : (fun p => D p-sphereSobolevDegreeL-r • D1 p) = fun p => R p-r •
      (coarseFirstRadialVariationL 1 (ell p)).comp Incl := by
    funext p
    rw [← radialCorrectionCovectorL_apply]
    change R p+sphereSobolevDegreeL-sphereSobolevDegreeL-r • D1 p = _
    rw [add_sub_cancel_right]
  have hFirst : Da1 =ᶠ[𝓝 p0] (fun p => D1 p+(M01 p).comp sphereSobolevDegreeL-sphereSobolevDegreeL.comp (M11 p)) := by
    filter_upwards [q.domainOpen.mem_nhds q.pointMem] with p hp
    have ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 (F1 p) z) 0 0) ⊤
        ((volume:Measure X).restrict ballOpens) := by
      rw [coefficientMatrixField_commonSupportMatrixFamily]
      exact commonSupportEnergyMemLp q.a1 q.firstSmooth p
    exact first_radial_adjoint_correction_normalized F0 (F1 p) (ell p) hF0 (by
      intro z hz i j
      have hMat : coefficientMatrixField 2 (F1 p) z = ell p z • (1:Mat) :=
        (congrFun (coefficientMatrixField_commonSupportMatrixFamily 2 q.a1 q.firstSmooth q.support q.compact q.firstSupported p) z).trans
          (q.firstScalar p hp z (Metric.closedBall_subset_closedBall hZ hz))
      exact congrArg (fun A : Mat => A i j) hMat) ha1 hInv0
  refine ⟨hNormal,hNormalNorm,?_⟩
  intro n hn
  change ‖iteratedFDeriv ℝ n (fun p => ((M0 p).comp (D p)+T p-Td p).comp (M1 p).inverse-
    sphereSobolevDegreeL-r • Da1 p) p0‖ ≤ radialAdjointTaylorHigherJetBudget N 2 CC ‖sphereSobolevDegreeL‖*r^2
  exact norm_iteratedFDeriv_radial_adjoint_taylor_higher_le M0 M01 M1 M11 D D1 Da1 T Td sphereSobolevDegreeL p0
    hM0 hM01 hM1 hM11 hD hD1 hDa1 hT hTd hNormal hFirst N r 2 CC hr (by norm_num) hCC hNormalNorm
    (fun j hj => ((hP0 j hj).1).trans hCBCle) (fun j _ hj => ((hP0 j hj).2.1).trans hCBCle)
    (fun j hj => by rw [hForwardEq];exact (hForward j hj).trans (mul_le_mul_of_nonneg_right hCJle (sq_nonneg r)))
    (fun j hj => (hQ0J j hj).trans (mul_le_mul_of_nonneg_right hCBCle (sq_nonneg r)))
    (fun j hj => (hQ1J j hj).trans (mul_le_mul_of_nonneg_right hCBCle (sq_nonneg r)))
    (fun j hj => (hDiff0 j hj).trans (mul_le_mul_of_nonneg_right h2CBCle hr))
    (fun j hj => (hDiff1 j hj).trans (mul_le_mul_of_nonneg_right h2CBCle hr))
    (fun j hj => (hD1J j hj).trans h6Cle) (fun j hj => (hDa1J j hj).trans h6Cle)
    (fun j hj => (hTJ j hj).trans (mul_le_mul_of_nonneg_right hCBCle (sq_nonneg r)))
    (fun j hj => (hTdJ j hj).trans (mul_le_mul_of_nonneg_right hCBCle (sq_nonneg r))) n hn

end ShrinkingSpheres

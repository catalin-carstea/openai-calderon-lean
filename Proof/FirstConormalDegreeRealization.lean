import Proof.ConormalFirstAdjoint
import Proof.FirstRadialCompatibility
import Proof.CoarseCoefficientCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] weakFirstConormalVariationL lowFirstRadialVariationL

theorem lowFirstRadialVariation_coarse (F0 F1 : SmoothCoefficientMatrix 2)
    (c : ℝ) (hc : 0 < c) (ell : X →L[ℝ] ℝ)
    (hF0 : ∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1)
    (hF1 : ∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) x = ell x*(1:Mat) i j)
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 x) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible) :
    (lowFirstRadialVariationL c F1 ha1).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) =
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
        ((coarseFirstRadialVariationL c ell).comp (sphereSobolevInclusionL 1 0 (by norm_num))) := by
  let A := (lowFirstRadialVariationL c F1 ha1).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
  let C := (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
    ((coarseFirstRadialVariationL c ell).comp (sphereSobolevInclusionL 1 0 (by norm_num)))
  have hScalar (w : UnitSphere) : coefficientMatrixField 2 F1 w.val = ell w.val • (1:Mat) := by
    have hw := Metric.closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 2) (Metric.sphere_subset_closedBall w.property)
    ext i j
    exact hF1 w.val hw i j
  have hFirst := highFirstRadialVariation_coarse_eq F0 F1 c hc.ne' ell
    (fun x hx => hF0 x (unitBall_subset_closedBall_two hx))
    (fun x hx i j => hF1 x (unitBall_subset_closedBall_two hx) i j) hInv0
  have hAgree (f : SphereSobolev (3/2:ℝ)) :
      A (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f) =
      C (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f) := by
    have hHalf := congrArg (fun I : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => I f)
      (sphereSobolevInclusionL_trans (3/2:ℝ) 1 (1/2:ℝ) (by norm_num) (by norm_num))
    have hZero := congrArg (fun I : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => I f)
      (sphereSobolevInclusionL_trans (3/2:ℝ) 1 0 (by norm_num) (by norm_num))
    have hLow := lowFirstRadialVariation_high_compatible F0 F1 c hc
      (fun x hx => hF0 x (unitBall_subset_closedBall_two hx)) ell hScalar ha1 hInv0 f
    have hHigh := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => T f) hFirst
    have hTrans := congrArg (fun I : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      I (highFirstRadialVariationL F0 F1 c f))
        (sphereSobolevInclusionL_trans (1/2:ℝ) 0 (-(1/2:ℝ)) (by norm_num) (by norm_num))
    exact (congrArg (lowFirstRadialVariationL c F1 ha1) hHalf).trans
      (hLow.trans (hTrans.symm.trans ((congrArg (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)) hHigh).trans
        (congrArg (fun z : SphereSobolev 0 => sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
          (coarseFirstRadialVariationL c ell z)) hZero.symm))))
  have hEq : (A : SphereSobolev 1 → SphereSobolev (-(1/2:ℝ))) = C :=
    (denseRange_sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)).equalizer A.continuous C.continuous (funext hAgree)
  exact DFunLike.ext' hEq

def firstConormalOneL (F1 : SmoothCoefficientMatrix 2) (c : ℝ) (ell : X →L[ℝ] ℝ) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  c • (coarseFirstRadialVariationL c ell).comp (sphereSobolevInclusionL 1 0 (by norm_num))+
    (coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F1)))).comp sphereSobolevDegreeL

/-- The genuine weak first conormal variation is the inclusion of the H1
    operator consisting of its bounded radial correction and scalar flux term. -/
theorem weakFirstConormal_degree_realization (F0 F1 : SmoothCoefficientMatrix 2)
    (c : ℝ) (hc : 0 < c) (ell : X →L[ℝ] ℝ)
    (hF0 : ∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1)
    (hF1 : ∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) x = ell x*(1:Mat) i j)
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 x) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible)
    (u : SphereSobolev 1) :
    weakFirstConormalVariationL c (coefficientMatrixField 2 F1) ha1
      (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u) =
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (firstConormalOneL F1 c ell u) := by
  let Ihalf := sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let J := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  let B := coarseFirstRadialVariationL c ell
  let Mneg := negativeBoundaryCoefficientMulL (normalCoefficientJet F1)
  let C := coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F1)))
  have hL := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T u)
    (lowFirstRadialVariation_coarse F0 F1 c hc ell hF0 hF1 ha1 hInv0)
  have hD := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T u) fixedLowRadialL_degree_compatible
  have hCancel : c • lowFirstRadialVariationL c F1 ha1 (Ihalf u) =
      weakFirstConormalVariationL c (coefficientMatrixField 2 F1) ha1 (Ihalf u)-Mneg (fixedLowRadialL (Ihalf u)) := by
    have hDef : lowFirstRadialVariationL c F1 ha1 (Ihalf u) =
        c⁻¹ • (weakFirstConormalVariationL c (coefficientMatrixField 2 F1) ha1 (Ihalf u)-Mneg (fixedLowRadialL (Ihalf u))) := by
      unfold lowFirstRadialVariationL
      rfl
    exact (congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => c • z) hDef).trans (smul_inv_smul₀ hc.ne' _)
  have hN := sub_eq_iff_eq_add.mp hCancel.symm
  have hT : Mneg (fixedLowRadialL (Ihalf u)) = J (C (sphereSobolevDegreeL u)) :=
    (congrArg Mneg hD).trans (negativeBoundaryCoefficientMulL_coarse (normalCoefficientJet F1) (sphereSobolevDegreeL u))
  have hBoth := congrArg₂ (fun x y : SphereSobolev (-(1/2:ℝ)) => c • x+y) hL hT
  have hSum : J (c • B (I0 u)+C (sphereSobolevDegreeL u)) = c • J (B (I0 u))+J (C (sphereSobolevDegreeL u)) :=
    (J.map_add _ _).trans (congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => z+J (C (sphereSobolevDegreeL u))) (J.map_smul c _))
  exact hN.trans (hBoth.trans hSum.symm)

theorem firstConormalOneL_symmetric (F0 F1 : SmoothCoefficientMatrix 2)
    (c : ℝ) (hc : 0 < c) (ell : X →L[ℝ] ℝ)
    (hF0 : ∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1)
    (hF1 : ∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) x = ell x*(1:Mat) i j)
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 x) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible)
    (u v : SphereSobolev 1) :
    ⟪firstConormalOneL F1 c ell u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,firstConormalOneL F1 c ell v⟫_ℝ := by
  have hs : ∀ᵐ x ∂((volume:Measure X).restrict ballOpens),(coefficientMatrixField 2 F1 x).IsSymm := by
    filter_upwards [ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx
    have hMat : coefficientMatrixField 2 F1 x = ell x • (1:Mat) := by
      ext i j
      exact hF1 x (unitBall_subset_closedBall_two hx) i j
    exact (congrArg Matrix.IsSymm hMat).mpr (Matrix.isSymm_one.smul (ell x))
  have hLower : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (firstConormalOneL F1 c ell) =
      (weakFirstConormalVariationL c (coefficientMatrixField 2 F1) ha1).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    apply ContinuousLinearMap.ext
    intro w
    exact (weakFirstConormal_degree_realization F0 F1 c hc ell hF0 hF1 ha1 hInv0 w).symm
  exact conormal_midpoint_symmetric _ _ hLower (weakFirstConormal_symmetric c ha1 hs) u v

end ShrinkingSpheres

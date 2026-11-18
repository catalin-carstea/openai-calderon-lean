import Proof.OrderOneBoundaryCoefficient
import Proof.Archive.SphereContinuousScalarMultiplierSymmetry

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier

theorem coarseSphereScalarMulL_add (q p : C(UnitSphere,ℝ)) :
    coarseSphereScalarMulL (q+p) = coarseSphereScalarMulL q+coarseSphereScalarMulL p := by
  apply ContinuousLinearMap.ext
  intro u
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  have hA : sphereContinuousScalarMulL (q+p) = sphereContinuousScalarMulL q+sphereContinuousScalarMulL p :=
    sphereContinuousScalarMultiplierL.map_add q p
  have h := congrArg (fun A : SphereL2 →L[ℝ] SphereL2 => Z (A (Z.symm u))) hA
  exact h.trans (Z.map_add _ _)

theorem coarseSphereScalarMulL_smul (c : ℝ) (q : C(UnitSphere,ℝ)) :
    coarseSphereScalarMulL (c • q) = c • coarseSphereScalarMulL q := by
  apply ContinuousLinearMap.ext
  intro u
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  have hA : sphereContinuousScalarMulL (c • q) = c • sphereContinuousScalarMulL q :=
    sphereContinuousScalarMultiplierL.map_smul c q
  have h := congrArg (fun A : SphereL2 →L[ℝ] SphereL2 => Z (A (Z.symm u))) hA
  exact h.trans (Z.map_smul c _)

theorem coarseSphereScalarMulL_const (q : C(UnitSphere,ℝ)) (c : ℝ) (hq : ∀ w,q w = c) :
    coarseSphereScalarMulL q = c • ContinuousLinearMap.id ℝ (SphereSobolev 0) := by
  apply ContinuousLinearMap.ext
  intro u
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  have hM : sphereContinuousScalarMulL q (Z.symm u) = c • Z.symm u := by
    apply Lp.ext
    filter_upwards [sphereContinuousScalarMul_value_ae q (Z.symm u),Lp.coeFn_smul c (Z.symm u)] with w hm hs
    exact hm.trans (by rw [hq w];exact hs.symm)
  exact (congrArg Z hM).trans ((Z.map_smul c _).trans (congrArg (fun v : SphereSobolev 0 => c • v) (Z.apply_symm_apply u)))

theorem coarseSphereScalarMulL_symmetric (q : C(UnitSphere,ℝ)) (u v : SphereSobolev 0) :
    ⟪coarseSphereScalarMulL q u,v⟫_ℝ = ⟪u,coarseSphereScalarMulL q v⟫_ℝ := by
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  have hLeft := Z.inner_map_map (sphereContinuousScalarMulL q (Z.symm u)) (Z.symm v)
  have hRight := Z.inner_map_map (Z.symm u) (sphereContinuousScalarMulL q (Z.symm v))
  have hV := congrArg (fun w : SphereSobolev 0 => ⟪coarseSphereScalarMulL q u,w⟫_ℝ) (Z.apply_symm_apply v)
  have hU := congrArg (fun w : SphereSobolev 0 => ⟪w,coarseSphereScalarMulL q v⟫_ℝ) (Z.apply_symm_apply u)
  exact hV.symm.trans (hLeft.trans ((inner_sphereContinuousScalarMulL_left q (Z.symm u) (Z.symm v)).trans
    (hRight.symm.trans hU)))

theorem oneBoundaryCoefficientMulL_add (F G : SmoothCoefficientJets 2) :
    oneBoundaryCoefficientMulL (F+G) = oneBoundaryCoefficientMulL F+oneBoundaryCoefficientMulL G := by
  have hm : smoothSphereValue (coefficientSmoothData (F+G)) =
      smoothSphereValue (coefficientSmoothData F)+smoothSphereValue (coefficientSmoothData G) := by
    ext w
    rfl
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective 1 0 (by norm_num)
  let I := sphereSobolevInclusionL 1 0 (by norm_num)
  have hA := congrArg (fun q : C(UnitSphere,ℝ) => coarseSphereScalarMulL q (I u)) hm
  have hB := congrArg (fun A : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => A (I u))
    (coarseSphereScalarMulL_add (smoothSphereValue (coefficientSmoothData F)) (smoothSphereValue (coefficientSmoothData G)))
  have hR := congrArg₂ (fun x y : SphereSobolev 0 => x+y)
    (oneBoundaryCoefficientMulL_coarse F u) (oneBoundaryCoefficientMulL_coarse G u)
  exact (oneBoundaryCoefficientMulL_coarse (F+G) u).trans (hA.trans (hB.trans
    (hR.symm.trans (I.map_add _ _).symm)))

theorem oneBoundaryCoefficientMulL_smul (c : ℝ) (F : SmoothCoefficientJets 2) :
    oneBoundaryCoefficientMulL (c • F) = c • oneBoundaryCoefficientMulL F := by
  have hm : smoothSphereValue (coefficientSmoothData (c • F)) = c • smoothSphereValue (coefficientSmoothData F) := by
    ext w
    rfl
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective 1 0 (by norm_num)
  let I := sphereSobolevInclusionL 1 0 (by norm_num)
  have hA := congrArg (fun q : C(UnitSphere,ℝ) => coarseSphereScalarMulL q (I u)) hm
  have hB := congrArg (fun A : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => A (I u))
    (coarseSphereScalarMulL_smul c (smoothSphereValue (coefficientSmoothData F)))
  have hR := congrArg (fun x : SphereSobolev 0 => c • x) (oneBoundaryCoefficientMulL_coarse F u)
  exact (oneBoundaryCoefficientMulL_coarse (c • F) u).trans (hA.trans (hB.trans
    (hR.symm.trans (I.map_smul c _).symm)))

theorem oneBoundaryCoefficientMulL_zero : oneBoundaryCoefficientMulL (0:SmoothCoefficientJets 2) = 0 := by
  have h := oneBoundaryCoefficientMulL_smul 0 (0:SmoothCoefficientJets 2)
  simpa only [zero_smul] using h

theorem oneBoundaryCoefficientMulL_sub (F G : SmoothCoefficientJets 2) :
    oneBoundaryCoefficientMulL (F-G) = oneBoundaryCoefficientMulL F-oneBoundaryCoefficientMulL G := by
  rw [sub_eq_add_neg,← neg_one_smul ℝ G,oneBoundaryCoefficientMulL_add,oneBoundaryCoefficientMulL_smul]
  module

theorem oneBoundaryCoefficientMulL_const_sphere (F : SmoothCoefficientJets 2) (c : ℝ)
    (hF : ∀ w : UnitSphere,coefficientValue 2 F w.val = c) :
    oneBoundaryCoefficientMulL F = c • ContinuousLinearMap.id ℝ (SphereSobolev 1) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective 1 0 (by norm_num)
  let I := sphereSobolevInclusionL 1 0 (by norm_num)
  have hA := congrArg (fun A : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => A (I u))
    (coarseSphereScalarMulL_const (smoothSphereValue (coefficientSmoothData F)) c hF)
  exact (oneBoundaryCoefficientMulL_coarse F u).trans (hA.trans (I.map_smul c u).symm)

end ShrinkingSpheres

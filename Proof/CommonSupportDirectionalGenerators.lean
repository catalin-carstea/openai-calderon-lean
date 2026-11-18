import Proof.BoundaryMatrixAngleDerivative
import Proof.WeakEnergyAngleDerivative
import Proof.ParallelFrameMetricJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL

/-- Actual joint directional jets bound the genuine compact generator in
    local matrix C1. This applies equally to a rotation or a center path. -/
theorem exists_commonSupport_generator_of_joint_bounds
    (a : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (q : ℝ) (hq : 0 ≤ q)
    (h0 : ∀ z ∈ (ballOpens:Set X),∀ i j,|fderiv ℝ (fun p => a p i j) (0,z) (1,0)| ≤ q)
    (h1 : ∀ z ∈ (ballOpens:Set X),∀ v : X,∀ i j,
      |fderiv ℝ (fderiv ℝ (fun p => a p i j)) (0,z) (0,v) (1,0)| ≤ q*‖v‖) :
    ∃ b : X → Mat,ContDiff ℝ ∞ b ∧ (∀ z,z ∉ S → b z = 0) ∧
      (∀ z,HasDerivAt (fun t => a (t,z)) (b z) 0) ∧
      (∀ z ∈ (ballOpens:Set X),‖b z‖ ≤ q) ∧
      ∀ z ∈ (ballOpens:Set X),‖fderiv ℝ b z‖ ≤ q := by
  obtain ⟨b,hb,hzb,hCurve⟩ := exists_commonSupport_angle_generator a ha S hz
  have hEntrySmooth (i j : I) : ContDiff ℝ ∞ (fun p => a p i j) := contDiff_pi.mp (contDiff_pi.mp ha i) j
  have hEntry (z : X) (i j : I) : b z i j = fderiv ℝ (fun p => a p i j) (0,z) (1,0) := by
    have hFirst : HasDerivAt (fun t => a (t,z) i j) (b z i j) 0 := by
      simpa only [Function.comp_def,matrixEntryL_apply] using
        (matrixEntryL i j).hasFDerivAt.comp_hasDerivAt (0:ℝ) (hCurve z)
    have hOther := ((hEntrySmooth i j).differentiable (by simp) (0,z)).hasFDerivAt.comp_hasDerivAt (0:ℝ)
      ((hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) z))
    exact hFirst.unique hOther
  refine ⟨b,hb,hzb,hCurve,?_,?_⟩
  · intro z hzB
    apply (Matrix.norm_le_iff hq).mpr
    intro i j
    rw [Real.norm_eq_abs,hEntry]
    exact h0 z hzB i j
  · intro z hzB
    apply norm_fderiv_matrix_le_of_entries b z (hb.differentiable (by simp) z) q hq
    intro i j
    apply ContinuousLinearMap.opNorm_le_bound _ hq
    intro v
    have hNear : (fun w => fderiv ℝ (fun p => a p i j) (0,w) (1,0)) =ᶠ[𝓝 z] (fun w => b w i j) :=
      Filter.Eventually.of_forall (fun w => (hEntry w i j).symm)
    have hMixed := mixed_first_coordinate_fderiv_of_germ (fun p => a p i j) z v (fun w => b w i j)
      (hEntrySmooth i j).contDiffAt hNear
    rw [← hMixed,Real.norm_eq_abs]
    exact h1 z hzB v i j

/-- Native derivative estimates retain the actual raw family and support witnesses. -/
structure CommonSupportNativeDerivativeBounds
    (a : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (q : ℝ) : Prop where
  strong : ‖fderiv ℝ (fun t => strongDirichletOperator fixedSobolevCalculus 0
    (commonSupportMatrixFamily 2 a ha S hS hz t)) 0‖ ≤ 2*strongC1OperatorBudget fixedSobolevCalculus*q
  full : ‖fderiv ℝ (fun t => fullCoefficientOperatorL fixedSobolevCalculus 0
    (commonSupportMatrixFamily 2 a ha S hS hz t)) 0‖ ≤ 2*fullC1OperatorBudget fixedSobolevCalculus*q
  fullWeak : ‖fderiv ℝ (commonSupportFullWeakEnergy a ha) 0‖ ≤ weakFullDerivativeBudget*q
  weak : ‖fderiv ℝ (commonSupportWeakEnergy a ha) 0‖ ≤ weakFullDerivativeBudget*q
  zeroWeak : ‖fderiv ℝ (commonSupportZeroWeakEnergy a ha) 0‖ ≤ weakFullDerivativeBudget*q
  normal : ‖fderiv ℝ (fun t => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz t)) 0‖ ≤
    boundaryHalfDerivativeBudget*(36*q)
  tangent : ∀ j : I,‖fderiv ℝ (fun t => negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz j t)) 0‖ ≤
    boundaryHalfDerivativeBudget*(78*q)

/-- Shared native operator derivative bounds from the genuine compact
    coefficient generator and its spatial C1 bounds. -/
theorem commonSupport_native_derivatives_of_generator_bounds
    (a : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (b : X → Mat) (hb : ContDiff ℝ ∞ b)
    (hzb : ∀ z,z ∉ S → b z = 0) (hCurve : ∀ z,HasDerivAt (fun t => a (t,z)) (b z) 0)
    (q : ℝ) (hq : 0 ≤ q) (hValue : ∀ z ∈ (ballOpens:Set X),‖b z‖ ≤ q)
    (hSpatial : ∀ z ∈ (ballOpens:Set X),‖fderiv ℝ b z‖ ≤ q) :
    CommonSupportNativeDerivativeBounds a ha S hS hz q := by
  have hStrong := norm_fderiv_angle_commonSupport_operators_le fixedSobolevCalculus a ha S hS hz b
    (hb.differentiable (by simp)) hCurve q hq hValue hSpatial
  have hWeak := norm_fderiv_angle_commonSupport_weakEnergy_le a ha S hS hz b
    (fun z _ => hCurve z) q hq hValue
  have hFullWeak := norm_fderiv_angle_commonSupport_fullWeakEnergy_le a ha S hS hz b
    (fun z _ => hCurve z) q hq hValue
  have hBoundary := norm_fderiv_commonSupport_boundary_matrix_angle_le a ha S hS hz b hb hzb hCurve q hq hValue hSpatial
  exact ⟨hStrong.1,hStrong.2,hFullWeak,hWeak.1,hWeak.2,hBoundary.1,hBoundary.2⟩


/-- The same actual compact family feeds the existing strong, weak and
    boundary multiplier derivative bounds from its genuine center/angular jets. -/
theorem commonSupport_native_derivatives_of_joint_bounds
    (a : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (q : ℝ) (hq : 0 ≤ q)
    (h0 : ∀ z ∈ (ballOpens:Set X),∀ i j,|fderiv ℝ (fun p => a p i j) (0,z) (1,0)| ≤ q)
    (h1 : ∀ z ∈ (ballOpens:Set X),∀ v : X,∀ i j,
      |fderiv ℝ (fderiv ℝ (fun p => a p i j)) (0,z) (0,v) (1,0)| ≤ q*‖v‖) :
    CommonSupportNativeDerivativeBounds a ha S hS hz q := by
  obtain ⟨b,hb,hzb,hCurve,hValue,hSpatial⟩ := exists_commonSupport_generator_of_joint_bounds a ha S hz q hq h0 h1
  exact commonSupport_native_derivatives_of_generator_bounds a ha S hS hz b hb hzb hCurve q hq hValue hSpatial


end ShrinkingSpheres

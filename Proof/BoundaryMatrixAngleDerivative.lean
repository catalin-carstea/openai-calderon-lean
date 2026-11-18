import Proof.BoundaryMultiplierDerivative
import Proof.BoundaryMatrixGeneratorSlices
import Proof.CommonSupportLowRadialRegularity
import Proof.BoundaryCoefficientC1Bounds
import Proof.AngleLowJetDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
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

/-- A compact smooth actual family has a genuine compact smooth angle generator. -/
theorem exists_commonSupport_angle_generator
    (a : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X)
    (hz : ∀ θ z,z ∉ S → a (θ,z) = 0) :
    ∃ b : X → Mat,ContDiff ℝ ∞ b ∧ (∀ z,z ∉ S → b z = 0) ∧
      ∀ z,HasDerivAt (fun θ => a (θ,z)) (b z) 0 := by
  let b : X → Mat := fun z => fderiv ℝ a (0,z) (1,0)
  have hbSmooth : ContDiff ℝ ∞ b :=
    ((ha.fderiv_right (by simp)).comp (contDiff_const.prodMk contDiff_id)).clm_apply contDiff_const
  have hb (z : X) : HasDerivAt (fun θ => a (θ,z)) (b z) 0 := by
    exact (ha.differentiable (by simp) (0,z)).hasFDerivAt.comp_hasDerivAt (0:ℝ)
      ((hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) z))
  refine ⟨b,hbSmooth,?_,hb⟩
  intro z hzS
  have hFun : (fun θ => a (θ,z)) = fun _ : ℝ => (0:Mat) := funext (fun θ => hz θ z hzS)
  have h := hb z
  rw [hFun] at h
  exact h.unique (hasDerivAt_const (0:ℝ) (0:Mat))

/-- Local matrix C1 control gives the normal/tangent scalar C1 budgets for
    the genuine angle generator, without using exterior coefficient jets. -/
theorem commonSupport_boundary_angle_generator_C1
    (b : X → Mat) (hb : ContDiff ℝ ∞ b) (S : Set X) (hS : IsCompact S)
    (hz : ∀ z,z ∉ S → b z = 0) (q : ℝ) (hq : 0 ≤ q)
    (h0 : ∀ z ∈ (ballOpens:Set X),‖b z‖ ≤ q)
    (h1 : ∀ z ∈ (ballOpens:Set X),‖fderiv ℝ b z‖ ≤ q) :
    LocalC1Bound (fun z => normalCoefficientFunction (fun v : ℝ × X => b v.2) (0,z)) (36*q) ∧
      ∀ j : I,LocalC1Bound (fun z => tangentCoefficientFunction (fun v : ℝ × X => b v.2) j (0,z)) (78*q) := by
  let bb : ℝ × X → Mat := fun v => b v.2
  have hbb : ContDiff ℝ ∞ bb := hb.comp contDiff_snd
  have hzbb : ∀ θ z,z ∉ S → bb (θ,z) = 0 := fun _ z hzS => hz z hzS
  let F := commonSupportMatrixFamily 2 bb hbb S hS hzbb 0
  have hRep : coefficientMatrixField 2 F = b :=
    coefficientMatrixField_commonSupportMatrixFamily 2 bb hbb S hS hzbb 0
  have hVal (i j : I) (z : X) (hzB : z ∈ (ballOpens:Set X)) : |coefficientValue 2 (F i j) z| ≤ q := by
    change |coefficientMatrixField 2 F z i j| ≤ q
    rw [hRep]
    exact (Matrix.norm_entry_le_entrywise_sup_norm (b z) (i:=i) (j:=j)).trans (h0 z hzB)
  have hDer (i j : I) (z : X) (hzB : z ∈ (ballOpens:Set X)) : ‖fderiv ℝ (coefficientValue 2 (F i j)) z‖ ≤ q := by
    have hFun : coefficientValue 2 (F i j) = fun z => b z i j := congrArg (fun B : X → Mat => fun z => B z i j) hRep
    rw [hFun,fderiv_matrix_entry b z (hb.differentiable (by simp) z) i j]
    apply ContinuousLinearMap.opNorm_le_bound _ hq
    intro v
    exact (Matrix.norm_entry_le_entrywise_sup_norm (fderiv ℝ b z v) (i:=i) (j:=j)).trans
      ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (h1 z hzB) (norm_nonneg v)))
  have hN := boundaryNormalCoefficient_local_C1 F q hq hVal hDer
  have hT (j : I) := boundaryTangentCoefficient_local_C1 F q hq hVal hDer j
  have hNEq : (boundaryNormalCoefficientData F).1 =
      fun z => normalCoefficientFunction bb (0,z) := by
    funext z
    change (∑ i : I,∑ j : I,z i*coefficientMatrixField 2 F z i j*z j) = _
    rw [hRep]
    rfl
  have hTEq (j : I) : (boundaryTangentCoefficientData F j).1 =
      fun z => tangentCoefficientFunction bb j (0,z) := by
    funext z
    change (∑ i : I,z i*coefficientMatrixField 2 F z i j)-(boundaryNormalCoefficientData F).1 z*z j = _
    rw [hRep,hNEq]
    rfl
  exact ⟨hNEq ▸ hN,fun j => hTEq j ▸ hT j⟩

/-- The genuine normal and tangential negative-half multipliers inherit local
    C1 angle-generator bounds from their actual compact matrix family. -/
theorem norm_fderiv_commonSupport_boundary_matrix_angle_le
    (a : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ θ z,z ∉ S → a (θ,z) = 0)
    (b : X → Mat) (hb : ContDiff ℝ ∞ b) (hzb : ∀ z,z ∉ S → b z = 0)
    (hAngle : ∀ z,HasDerivAt (fun θ => a (θ,z)) (b z) 0)
    (q : ℝ) (hq : 0 ≤ q)
    (h0 : ∀ z ∈ (ballOpens:Set X),‖b z‖ ≤ q)
    (h1 : ∀ z ∈ (ballOpens:Set X),‖fderiv ℝ b z‖ ≤ q) :
    ‖fderiv ℝ (fun θ => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz θ)) 0‖ ≤
        boundaryHalfDerivativeBudget*(36*q) ∧
      ∀ j : I,‖fderiv ℝ (fun θ => negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz j θ)) 0‖ ≤
        boundaryHalfDerivativeBudget*(78*q) := by
  let bb : ℝ × X → Mat := fun v => b v.2
  have hSlices := commonSupport_boundary_generator_slices a b hAngle
  have hN := hSlices.1
  have hT := hSlices.2
  have hBounds := commonSupport_boundary_angle_generator_C1 b hb S hS hzb q hq h0 h1
  have hNBound := norm_fderiv_commonSupport_negativeBoundaryCoefficientMul_le
    (normalCoefficientFunction a) (contDiff_normalCoefficientFunction a ha) S hS
    (normalCoefficientFunction_support a S hz) 0 (36*q) (by positivity)
    (fun k z hzB => norm_fderiv_angle_spatial_low_jets_le
      (normalCoefficientFunction a) (contDiff_normalCoefficientFunction a ha)
      (fun z => normalCoefficientFunction bb (0,z)) hN z (36*q) (by positivity)
      (hBounds.1 z hzB).1 (hBounds.1 z hzB).2 k)
  refine ⟨hNBound,?_⟩
  intro j
  exact norm_fderiv_commonSupport_negativeBoundaryCoefficientMul_le
    (tangentCoefficientFunction a j) (contDiff_tangentCoefficientFunction a ha j) S hS
    (tangentCoefficientFunction_support a S hz j) 0 (78*q) (by positivity)
    (fun k z hzB => norm_fderiv_angle_spatial_low_jets_le
      (tangentCoefficientFunction a j) (contDiff_tangentCoefficientFunction a ha j)
      (fun z => tangentCoefficientFunction bb j (0,z)) (hT j) z (78*q) (by positivity)
      (hBounds.2 j z hzB).1 (hBounds.2 j z hzB).2 k)

end ShrinkingSpheres

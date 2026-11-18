import Proof.BoundaryScalarGeneratorDerivative
import Proof.BoundaryMatrixGeneratorSlices

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies

/-- Exact coarse/H1 derivatives of all boundary multipliers, obtained from
    one compact matrix generator. These identities also determine the actual
    tangential operator and its physical adjoint under differentiation. -/
theorem hasDerivAt_commonSupport_boundary_matrix
    (a : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0)
    (b : X → Mat) (hb : ContDiff ℝ ∞ b) (hzb : ∀ z,z ∉ S → b z = 0)
    (hAngle : ∀ z,HasDerivAt (fun t => a (t,z)) (b z) 0) :
    let bb : ℝ × X → Mat := fun v => b v.2
    let hbb : ContDiff ℝ ∞ bb := hb.comp contDiff_snd
    let hzbb : ∀ t z,z ∉ S → bb (t,z) = 0 := fun _ z h => hzb z h
    let F := commonSupportMatrixFamily 2 a ha S hS hz
    let G := commonSupportMatrixFamily 2 bb hbb S hS hzbb 0
    HasDerivAt (fun t => coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData
      (normalCoefficientJet (F t)))))
      (coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet G)))) 0 ∧
    HasDerivAt (fun t => oneBoundaryCoefficientMulL (normalCoefficientJet (F t)))
      (oneBoundaryCoefficientMulL (normalCoefficientJet G)) 0 ∧
    (∀ j,HasDerivAt (fun t => coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData
      (tangentCoefficientJet (F t) j))))
      (coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (tangentCoefficientJet G j)))) 0) ∧
    (∀ j,HasDerivAt (fun t => oneBoundaryCoefficientMulL (tangentCoefficientJet (F t) j))
      (oneBoundaryCoefficientMulL (tangentCoefficientJet G j)) 0) := by
  dsimp only
  let bb : ℝ × X → Mat := fun v => b v.2
  have hbb : ContDiff ℝ ∞ bb := hb.comp contDiff_snd
  have hzbb : ∀ t z,z ∉ S → bb (t,z) = 0 := fun _ z h => hzb z h
  let F := commonSupportMatrixFamily 2 a ha S hS hz
  let G := commonSupportMatrixFamily 2 bb hbb S hS hzbb 0
  let gN := normalCoefficientFunction a
  let bN := fun z => normalCoefficientFunction bb (0,z)
  have hgN := contDiff_normalCoefficientFunction a ha
  have hbN : ContDiff ℝ ∞ bN :=
    (contDiff_normalCoefficientFunction bb hbb).comp (contDiff_const.prodMk contDiff_id)
  have hzN := normalCoefficientFunction_support a S hz
  have hzbN : ∀ z,z ∉ S → bN z = 0 := fun z h => normalCoefficientFunction_support bb S hzbb 0 z h
  have hSlices := commonSupport_boundary_generator_slices a b hAngle
  have hNC := hasDerivAt_commonSupport_coarseCoefficientMul gN hgN S hS hzN bN hbN hzbN hSlices.1
  have hN1 := hasDerivAt_commonSupport_oneCoefficientMul gN hgN S hS hzN bN hbN hzbN hSlices.1
  have hNV (t : ℝ) (w : UnitSphere) :
      coefficientValue 2 (normalCoefficientJet (F t)) w.val =
        coefficientValue 2 (commonSupportCoefficientFamily 2 gN hgN S hS hzN t) w.val :=
    (commonSupport_normal_sphereValue a ha S hS hz t w).trans
      (coefficientValue_commonSupportCoefficientFamily 2 gN hgN S hS hzN t w.val).symm
  have hNG (w : UnitSphere) : coefficientValue 2 (normalCoefficientJet G) w.val =
      coefficientValue 2 (compactCoefficient 2 bN hbN (HasCompactSupport.intro hS hzbN)) w.val :=
    (commonSupport_normal_sphereValue bb hbb S hS hzbb 0 w).trans
      (congrFun (coefficientValue_compactCoefficient 2 bN hbN (HasCompactSupport.intro hS hzbN)) w.val).symm
  have hNCEq : (fun t => coarseSphereScalarMulL (smoothSphereValue
      (coefficientSmoothData (normalCoefficientJet (F t))))) =
      fun t => coarseSphereScalarMulL (smoothSphereValue
        (coefficientSmoothData (commonSupportCoefficientFamily 2 gN hgN S hS hzN t))) := by
    funext t;congr 1
  have hNCGEq : coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet G))) =
      coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData
        (compactCoefficient 2 bN hbN (HasCompactSupport.intro hS hzbN)))) := by
    congr 1
  have hN1Eq := funext (fun t => oneBoundaryCoefficientMulL_congr_sphere _ _ (hNV t))
  have hN1GEq := oneBoundaryCoefficientMulL_congr_sphere _ _ hNG
  refine ⟨?_,?_,?_,?_⟩
  · rw [hNCEq,hNCGEq];exact hNC
  · rw [hN1Eq,hN1GEq];exact hN1
  · intro j
    let gT := tangentCoefficientFunction a j
    let bT := fun z => tangentCoefficientFunction bb j (0,z)
    have hgT := contDiff_tangentCoefficientFunction a ha j
    have hbT : ContDiff ℝ ∞ bT :=
      (contDiff_tangentCoefficientFunction bb hbb j).comp (contDiff_const.prodMk contDiff_id)
    have hzT := tangentCoefficientFunction_support a S hz j
    have hzbT : ∀ z,z ∉ S → bT z = 0 := fun z h => tangentCoefficientFunction_support bb S hzbb j 0 z h
    have hTC := hasDerivAt_commonSupport_coarseCoefficientMul gT hgT S hS hzT bT hbT hzbT (hSlices.2 j)
    convert hTC using 1
    · funext t;congr 1
    · congr 1
  · intro j
    let gT := tangentCoefficientFunction a j
    let bT := fun z => tangentCoefficientFunction bb j (0,z)
    have hgT := contDiff_tangentCoefficientFunction a ha j
    have hbT : ContDiff ℝ ∞ bT :=
      (contDiff_tangentCoefficientFunction bb hbb j).comp (contDiff_const.prodMk contDiff_id)
    have hzT := tangentCoefficientFunction_support a S hz j
    have hzbT : ∀ z,z ∉ S → bT z = 0 := fun z h => tangentCoefficientFunction_support bb S hzbb j 0 z h
    have hT1 := hasDerivAt_commonSupport_oneCoefficientMul gT hgT S hS hzT bT hbT hzbT (hSlices.2 j)
    convert hT1 using 1
    · funext t
      apply oneBoundaryCoefficientMulL_congr_sphere
      intro w
      exact (commonSupport_tangent_sphereValue a ha S hS hz j t w).trans
        (coefficientValue_commonSupportCoefficientFamily 2 gT hgT S hS hzT t w.val).symm
    · apply oneBoundaryCoefficientMulL_congr_sphere
      intro w
      exact (commonSupport_tangent_sphereValue bb hbb S hS hzbb j 0 w).trans
        (congrFun (coefficientValue_compactCoefficient 2 bT hbT (HasCompactSupport.intro hS hzbT)) w.val).symm

end ShrinkingSpheres

import Proof.BoundaryMatrixGeneratorDerivative
import Proof.CoarseBoundaryCoefficientNorm
import Proof.CommonSupportDirectionalGenerators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
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

lemma norm_fderiv_le_of_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (v : E) (x q : ℝ) (h : HasDerivAt f v x) (hq : 0 ≤ q) (hv : ‖v‖ ≤ q) :
    ‖fderiv ℝ f x‖ ≤ q := by
  apply ContinuousLinearMap.opNorm_le_bound _ hq
  intro t
  rw [fderiv_eq_smul_deriv,h.deriv]
  exact (norm_smul_le t v).trans ((mul_le_mul_of_nonneg_left hv (norm_nonneg t)).trans_eq (by ring))

def boundaryTangentialCoarseBudget : ℝ :=
  ∑ j : I,∑ i : I,‖coarseSphereScalarMulL (sphereCoordinate i)‖*‖sphereSobolevRotationL 1 i j‖

lemma boundaryTangentialCoarseBudget_nonneg : 0 ≤ boundaryTangentialCoarseBudget := by
  unfold boundaryTangentialCoarseBudget
  positivity

theorem norm_coarseBoundaryTangentialL_le (F : I → SmoothCoefficientJets 2)
    (q : ℝ) (hq : 0 ≤ q)
    (hF : ∀ j,‖coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (F j)))‖ ≤ q) :
    ‖coarseBoundaryTangentialL F‖ ≤ boundaryTangentialCoarseBudget*q := by
  have hTerm (j i : I) : ‖(coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (F j)))).comp
      ((coarseSphereScalarMulL (sphereCoordinate i)).comp (sphereSobolevRotationL 1 i j))‖ ≤
      (‖coarseSphereScalarMulL (sphereCoordinate i)‖*‖sphereSobolevRotationL 1 i j‖)*q := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (hF j) (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) hq).trans_eq (by ring))
  calc
    _ ≤ ∑ j : I,∑ i : I,‖(coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (F j)))).comp
        ((coarseSphereScalarMulL (sphereCoordinate i)).comp (sphereSobolevRotationL 1 i j))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => norm_sum_le _ _))
    _ ≤ ∑ j : I,∑ i : I,(‖coarseSphereScalarMulL (sphereCoordinate i)‖*‖sphereSobolevRotationL 1 i j‖)*q :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ => hTerm j i))
    _ = _ := by unfold boundaryTangentialCoarseBudget;rw [Finset.sum_mul];simp_rw [Finset.sum_mul]

/-- Additional endpoint budgets required by actual radial adjunction. They
    are kept separate from the earlier weak/strong derivative interface. -/
structure CommonSupportOneBoundaryDerivativeBounds
    (a : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (q : ℝ) : Prop where
  coarseNormal : ‖fderiv ℝ (fun t => coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData
    (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz t))))) 0‖ ≤ 36*q
  oneNormal : ‖fderiv ℝ (fun t => oneBoundaryCoefficientMulL
    (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz t))) 0‖ ≤ (73*36)*q
  tangent : ‖fderiv ℝ (fun t => coarseBoundaryTangentialL
    (fun j => tangentCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz t) j)) 0‖ ≤
      boundaryTangentialCoarseBudget*(78*q)
  adjointTangent : ‖fderiv ℝ (fun t => adjointBoundaryTangentialL
    (fun j => tangentCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz t) j)) 0‖ ≤
      boundaryTangentialAdjointBudget*((73*78)*q)

/-- Sharp endpoint derivative estimates from the same true local C1 matrix
    generator; no high exterior jets enter their constants. -/
theorem commonSupport_one_boundary_derivatives_of_generator_bounds
    (a : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0)
    (b : X → Mat) (hb : ContDiff ℝ ∞ b) (hzb : ∀ z,z ∉ S → b z = 0)
    (hAngle : ∀ z,HasDerivAt (fun t => a (t,z)) (b z) 0)
    (q : ℝ) (hq : 0 ≤ q)
    (h0 : ∀ z ∈ (ballOpens:Set X),‖b z‖ ≤ q)
    (h1 : ∀ z ∈ (ballOpens:Set X),‖fderiv ℝ b z‖ ≤ q) :
    CommonSupportOneBoundaryDerivativeBounds a ha S hS hz q := by
  let bb : ℝ × X → Mat := fun v => b v.2
  have hbb : ContDiff ℝ ∞ bb := hb.comp contDiff_snd
  have hzbb : ∀ t z,z ∉ S → bb (t,z) = 0 := fun _ z h => hzb z h
  let F := commonSupportMatrixFamily 2 a ha S hS hz
  let G := commonSupportMatrixFamily 2 bb hbb S hS hzbb 0
  have hDer := hasDerivAt_commonSupport_boundary_matrix a ha S hS hz b hb hzb hAngle
  dsimp only at hDer
  have hBounds := commonSupport_boundary_angle_generator_C1 b hb S hS hzb q hq h0 h1
  have hGN : coefficientValue 2 (normalCoefficientJet G) =
      fun z => normalCoefficientFunction bb (0,z) := by
    funext z
    rw [coefficientValue_normalCoefficientJet]
    change (∑ i : I,∑ j : I,z i*coefficientMatrixField 2 G z i j*z j) = _
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    rfl
  have hGT (j : I) : coefficientValue 2 (tangentCoefficientJet G j) =
      fun z => tangentCoefficientFunction bb j (0,z) := by
    funext z
    rw [coefficientValue_tangentCoefficientJet]
    change (∑ i : I,z i*coefficientMatrixField 2 G z i j)-
      (∑ i : I,∑ k : I,z i*coefficientMatrixField 2 G z i k*z k)*z j = _
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    rfl
  have hNC1 : LocalC1Bound (coefficientValue 2 (normalCoefficientJet G)) (36*q) := by
    rw [hGN];exact hBounds.1
  have hTC1 (j : I) : LocalC1Bound (coefficientValue 2 (tangentCoefficientJet G j)) (78*q) := by
    rw [hGT];exact hBounds.2 j
  have hNC : ‖coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet G)))‖ ≤ 36*q :=
    norm_coarse_boundary_coefficient_local_C1 _ (36*q) (by positivity) hNC1
  have hN1 : ‖oneBoundaryCoefficientMulL (normalCoefficientJet G)‖ ≤ (73*36)*q :=
    (norm_oneBoundaryCoefficientMulL_local_C1 _ (36*q) (by positivity) hNC1).trans_eq (by ring)
  have hTC (j : I) : ‖coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (tangentCoefficientJet G j)))‖ ≤ 78*q :=
    norm_coarse_boundary_coefficient_local_C1 _ (78*q) (by positivity) (hTC1 j)
  have hT1 (j : I) : ‖oneBoundaryCoefficientMulL (tangentCoefficientJet G j)‖ ≤ (73*78)*q :=
    (norm_oneBoundaryCoefficientMulL_local_C1 _ (78*q) (by positivity) (hTC1 j)).trans_eq (by ring)
  have hTang : HasDerivAt (fun t => coarseBoundaryTangentialL (fun j => tangentCoefficientJet (F t) j))
      (coarseBoundaryTangentialL (fun j => tangentCoefficientJet G j)) 0 := by
    have h := HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) =>
      HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => (hDer.2.2.1 j).clm_comp
        (hasDerivAt_const (0:ℝ) ((coarseSphereScalarMulL (sphereCoordinate i)).comp (sphereSobolevRotationL 1 i j)))))
    simpa only [ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp,zero_add,add_zero,
      coarseBoundaryTangentialL,_root_.sum_apply] using h
  have hAdj : HasDerivAt (fun t => adjointBoundaryTangentialL (fun j => tangentCoefficientJet (F t) j))
      (adjointBoundaryTangentialL (fun j => tangentCoefficientJet G j)) 0 := by
    have h := HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) =>
      HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) =>
        ((hasDerivAt_const (0:ℝ) (sphereSobolevRotationL 1 i j : SphereSobolev 1 →L[ℝ] SphereSobolev 0)).clm_comp
          ((hasDerivAt_const (0:ℝ) (oneSphereCoordinateMulL i)).clm_comp (hDer.2.2.2 j))).neg))
    simpa only [ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp,zero_add,add_zero,
      adjointBoundaryTangentialL,_root_.sum_apply,Pi.neg_apply] using h
  exact ⟨norm_fderiv_le_of_hasDerivAt _ _ _ _ hDer.1 (by positivity) hNC,
    norm_fderiv_le_of_hasDerivAt _ _ _ _ hDer.2.1 (by positivity) hN1,
    norm_fderiv_le_of_hasDerivAt _ _ _ _ hTang (by have := boundaryTangentialCoarseBudget_nonneg;positivity)
      (norm_coarseBoundaryTangentialL_le _ (78*q) (by positivity) hTC),
    norm_fderiv_le_of_hasDerivAt _ _ _ _ hAdj (by have := boundaryTangentialAdjointBudget_nonneg;positivity)
      (norm_adjointBoundaryTangentialL_le _ ((73*78)*q) (by positivity) hT1)⟩

theorem commonSupport_one_boundary_derivatives_of_joint_bounds
    (a : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (q : ℝ) (hq : 0 ≤ q)
    (h0 : ∀ z ∈ (ballOpens:Set X),∀ i j,|fderiv ℝ (fun p => a p i j) (0,z) (1,0)| ≤ q)
    (h1 : ∀ z ∈ (ballOpens:Set X),∀ v : X,∀ i j,
      |fderiv ℝ (fderiv ℝ (fun p => a p i j)) (0,z) (0,v) (1,0)| ≤ q*‖v‖) :
    CommonSupportOneBoundaryDerivativeBounds a ha S hS hz q := by
  obtain ⟨b,hb,hzb,hCurve,hValue,hSpatial⟩ :=
    exists_commonSupport_generator_of_joint_bounds a ha S hz q hq h0 h1
  exact commonSupport_one_boundary_derivatives_of_generator_bounds a ha S hS hz b hb hzb hCurve q hq hValue hSpatial

end ShrinkingSpheres

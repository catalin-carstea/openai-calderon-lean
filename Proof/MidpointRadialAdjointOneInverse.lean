import Proof.MidpointRadialAdjointNative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The actual H1 reciprocal and reconstructed conormal symmetry suffice
    for true radial adjunction. This form is stable under native parameter
    neighborhoods and does not require a new positivity witness at each point. -/
theorem radialAdjointFromResponseL_pairing_of_one_inverse
    (F : SmoothCoefficientMatrix 2) (D : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hOne : (oneBoundaryCoefficientMulL (normalCoefficientJet F)).IsInvertible)
    (hSym : ∀ u v : SphereSobolev 1,
      let N := (coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F)))).comp D+
        coarseBoundaryTangentialL (fun j => tangentCoefficientJet F j)
      ⟪N u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,N v⟫_ℝ) :
    ∀ u v : SphereSobolev 1,⟪D u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,radialAdjointFromResponseL F D v⟫_ℝ := by
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let M := oneBoundaryCoefficientMulL (normalCoefficientJet F)
  let C := coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F)))
  let T := coarseBoundaryTangentialL (fun j => tangentCoefficientJet F j)
  let Td := adjointBoundaryTangentialL (fun j => tangentCoefficientJet F j)
  let N := C.comp D+T
  intro u v
  let w := M.inverse v
  have hIw : I0 v = C (I0 w) := by
    exact (congrArg I0 (hOne.self_apply_inverse v)).symm.trans
      (oneBoundaryCoefficientMulL_coarse (normalCoefficientJet F) w)
  have hN : ⟪N u,I0 w⟫_ℝ = ⟪I0 u,N w⟫_ℝ := hSym u w
  have hT := boundaryTangentialL_adjoint (fun j => tangentCoefficientJet F j) u w
  change ⟪D u,I0 v⟫_ℝ = ⟪I0 u,N w-Td w⟫_ℝ
  rw [hIw,← coarseSphereScalarMulL_symmetric]
  have hC : C (D u) = N u-T u := by
    change C (D u) = C (D u)+T u-T u
    abel
  rw [hC,inner_sub_left,hN,hT,inner_sub_right]

theorem midpoint_radialAdjointFromResponse_pairing_of_one_inverse {a : X → Mat}
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 ha))
    (hs : ∀ᵐ z ∂((volume:Measure X).restrict ballOpens),(a z).IsSymm)
    (F : SmoothCoefficientMatrix 2)
    (hField : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z = a z)
    (hStrong : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (hNormal : (negativeBoundaryCoefficientMulL (normalCoefficientJet F)).IsInvertible)
    (hOne : (oneBoundaryCoefficientMulL (normalCoefficientJet F)).IsInvertible)
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hR : R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F)) :
    ∀ u v,⟪(R+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,
        radialAdjointFromResponseL F (R+sphereSobolevDegreeL) v⟫_ℝ := by
  have hWeak := midpoint_radial_reconstructed_conormal_weak ha hc F hField hStrong hNormal R hR
  exact radialAdjointFromResponseL_pairing_of_one_inverse F (R+sphereSobolevDegreeL) hOne
    (conormal_midpoint_symmetric _ _ hWeak (nativeWeakConormal_symmetric ha hc hs))

end ShrinkingSpheres

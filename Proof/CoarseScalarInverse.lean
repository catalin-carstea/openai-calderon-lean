import Proof.InverseEndpointCompatibility
import Proof.OrderOneCoefficientAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier

def sphereScalarReciprocal (q : C(UnitSphere,ℝ)) (h : ∀ w,0 < q w) : C(UnitSphere,ℝ) :=
  ⟨fun w => (q w)⁻¹,q.continuous.inv₀ (fun w => (h w).ne')⟩

theorem coarseSphereScalarMulL_comp_eq_id (q p : C(UnitSphere,ℝ)) (h : ∀ w,q w*p w = 1) :
    (coarseSphereScalarMulL q).comp (coarseSphereScalarMulL p) =
      ContinuousLinearMap.id ℝ (SphereSobolev 0) := by
  apply ContinuousLinearMap.ext
  intro u
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  change Z (sphereContinuousScalarMulL q (Z.symm (Z (sphereContinuousScalarMulL p (Z.symm u))))) = u
  rw [LinearIsometryEquiv.symm_apply_apply]
  have hP := congrArg (fun A : SphereL2 →L[ℝ] SphereL2 => Z (A (Z.symm u)))
    (sphereContinuousScalarMulL_comp_eq_id_of_mul_eq_one q p h)
  exact hP.trans (Z.apply_symm_apply u)

theorem coarseSphereScalarMulL_isInvertible_of_pos (q : C(UnitSphere,ℝ)) (h : ∀ w,0 < q w) :
    (coarseSphereScalarMulL q).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (coarseSphereScalarMulL_comp_eq_id q (sphereScalarReciprocal q h) (fun w => mul_inv_cancel₀ (h w).ne'))
    (coarseSphereScalarMulL_comp_eq_id (sphereScalarReciprocal q h) q (fun w => inv_mul_cancel₀ (h w).ne'))

theorem coarseSphereScalarMulL_inverse_eq (q : C(UnitSphere,ℝ)) (h : ∀ w,0 < q w) :
    (coarseSphereScalarMulL q).inverse = coarseSphereScalarMulL (sphereScalarReciprocal q h) :=
  ContinuousLinearMap.inverse_eq
    (coarseSphereScalarMulL_comp_eq_id q (sphereScalarReciprocal q h) (fun w => mul_inv_cancel₀ (h w).ne'))
    (coarseSphereScalarMulL_comp_eq_id (sphereScalarReciprocal q h) q (fun w => inv_mul_cancel₀ (h w).ne'))

theorem norm_coarseSphereScalarMulL_inverse_le (q : C(UnitSphere,ℝ)) (lam : ℝ) (hlam : 0 < lam)
    (hLower : ∀ w,lam ≤ q w) : ‖(coarseSphereScalarMulL q).inverse‖ ≤ lam⁻¹ := by
  have hPos (w : UnitSphere) : 0 < q w := hlam.trans_le (hLower w)
  have hN : ‖sphereScalarReciprocal q hPos‖ ≤ lam⁻¹ := by
    apply (ContinuousMap.norm_le _ (inv_nonneg.mpr hlam.le)).mpr
    intro w
    change ‖(q w)⁻¹‖ ≤ lam⁻¹
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hPos w))]
    simpa only [one_div] using one_div_le_one_div_of_le hlam (hLower w)
  exact (congrArg norm (coarseSphereScalarMulL_inverse_eq q hPos)).le.trans
    ((norm_coarseSphereScalarMulL_le _).trans hN)

/-- The H1 and physical L2 inverses act on the same boundary data, even
    though their qualitative constructions use different interfaces. -/
theorem oneBoundaryCoefficientMulL_inverse_coarse (F : SmoothCoefficientJets 2)
    (h : ∀ w : UnitSphere,0 < coefficientValue 2 F w.val) (u : SphereSobolev 1) :
    sphereSobolevInclusionL 1 0 (by norm_num) ((oneBoundaryCoefficientMulL F).inverse u) =
      (coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData F))).inverse
        (sphereSobolevInclusionL 1 0 (by norm_num) u) := by
  let I := sphereSobolevInclusionL 1 0 (by norm_num)
  let M := oneBoundaryCoefficientMulL F
  let C := coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData F))
  have hM : M.IsInvertible := oneBoundaryCoefficientMulL_isInvertible_of_pos F h
  have hC : C.IsInvertible := coarseSphereScalarMulL_isInvertible_of_pos (smoothSphereValue (coefficientSmoothData F)) h
  have hCompat : I.comp M=C.comp I := ContinuousLinearMap.ext (oneBoundaryCoefficientMulL_coarse F)
  have hInv : I.comp M.inverse=C.inverse.comp I := inverse_endpoint_compatible I M C hM hC hCompat
  exact DFunLike.congr_fun hInv u

theorem coarseSphereScalarMulL_inverse_symmetric (q : C(UnitSphere,ℝ)) (h : ∀ w,0 < q w)
    (u v : SphereSobolev 0) :
    ⟪(coarseSphereScalarMulL q).inverse u,v⟫_ℝ = ⟪u,(coarseSphereScalarMulL q).inverse v⟫_ℝ := by
  have hEq := coarseSphereScalarMulL_inverse_eq q h
  have hU := congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => ⟪T u,v⟫_ℝ) hEq
  have hV := congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => ⟪u,T v⟫_ℝ) hEq
  exact hU.trans ((coarseSphereScalarMulL_symmetric _ u v).trans hV.symm)

end ShrinkingSpheres

import Proof.CommonSupportBoundaryOperatorRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.CompactParameterSmoothness

/-- The actual coarse scalar multiplier, as a continuous linear map in its
    coefficient. This permits derivative identification before taking norms. -/
def coarseScalarMultiplierMapL : C(UnitSphere,ℝ) →L[ℝ]
    (SphereSobolev 0 →L[ℝ] SphereSobolev 0) :=
  ({ toFun := coarseSphereScalarMulL
     map_add' := coarseSphereScalarMulL_add
     map_smul' := coarseSphereScalarMulL_smul } :
    C(UnitSphere,ℝ) →ₗ[ℝ] (SphereSobolev 0 →L[ℝ] SphereSobolev 0)).mkContinuous 1
      (fun q => (norm_coarseSphereScalarMulL_le q).trans_eq (one_mul _).symm)

/-- A smooth joint coefficient has the expected derivative as a continuous
    function on the sphere. Compactness supplies the uniform topology. -/
theorem hasDerivAt_compactSphereValue_of_slice
    (g : ℝ × X → ℝ) (hg : ContDiff ℝ ∞ g)
    (b : X → ℝ) (hb : Continuous b)
    (hSlice : ∀ z,HasDerivAt (fun t => g (t,z)) (b z) 0) :
    HasDerivAt (fun t => (⟨fun w : UnitSphere => g (t,w.val),
      hg.continuous.comp (continuous_const.prodMk continuous_subtype_val)⟩ : C(UnitSphere,ℝ)))
      (⟨fun w : UnitSphere => b w.val,hb.comp continuous_subtype_val⟩ : C(UnitSphere,ℝ)) 0 := by
  let Q := compactPullback g hg.continuous
    (⟨Subtype.val,continuous_subtype_val⟩ : C(UnitSphere,X))
  have hQ : DifferentiableAt ℝ Q 0 :=
    (contDiff_infty_compactPullback g hg
      (⟨Subtype.val,continuous_subtype_val⟩ : C(UnitSphere,X))).differentiable (by simp) 0
  have hEq : deriv Q 0 =
      (⟨fun w : UnitSphere => b w.val,hb.comp continuous_subtype_val⟩ : C(UnitSphere,ℝ)) := by
    ext w
    have hEval := (ContinuousMap.evalCLM (R:=ℝ) w).hasFDerivAt.comp_hasDerivAt (0:ℝ) hQ.hasDerivAt
    exact hEval.unique (hSlice w.val)
  exact hEq ▸ hQ.hasDerivAt

/-- The genuine coarse multiplier derivative is multiplication by the same
    scalar generator, with no exterior coefficient norm in this identity. -/
theorem hasDerivAt_commonSupport_coarseCoefficientMul
    (g : ℝ × X → ℝ) (hg : ContDiff ℝ ∞ g) (S : Set X) (hS : IsCompact S)
    (hz : ∀ t z,z ∉ S → g (t,z) = 0)
    (b : X → ℝ) (hb : ContDiff ℝ ∞ b) (hzb : ∀ z,z ∉ S → b z = 0)
    (hSlice : ∀ z,HasDerivAt (fun t => g (t,z)) (b z) 0) :
    HasDerivAt (fun t => coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData
      (commonSupportCoefficientFamily 2 g hg S hS hz t))))
      (coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData
        (compactCoefficient 2 b hb (HasCompactSupport.intro hS hzb))))) 0 := by
  have hQ := hasDerivAt_compactSphereValue_of_slice g hg b hb.continuous hSlice
  have hMul := coarseScalarMultiplierMapL.hasFDerivAt.comp_hasDerivAt (0:ℝ) hQ
  convert hMul using 1
  · congr 1
  · congr 1

/-- Differentiating the exact H1-to-L2 compatibility identifies the genuine
    H1 multiplier derivative with the multiplier of the same generator. -/
theorem hasDerivAt_commonSupport_oneCoefficientMul
    (g : ℝ × X → ℝ) (hg : ContDiff ℝ ∞ g) (S : Set X) (hS : IsCompact S)
    (hz : ∀ t z,z ∉ S → g (t,z) = 0)
    (b : X → ℝ) (hb : ContDiff ℝ ∞ b) (hzb : ∀ z,z ∉ S → b z = 0)
    (hSlice : ∀ z,HasDerivAt (fun t => g (t,z)) (b z) 0) :
    HasDerivAt (fun t => oneBoundaryCoefficientMulL
      (commonSupportCoefficientFamily 2 g hg S hS hz t))
      (oneBoundaryCoefficientMulL
        (compactCoefficient 2 b hb (HasCompactSupport.intro hS hzb))) 0 := by
  let M := fun t => oneBoundaryCoefficientMulL (commonSupportCoefficientFamily 2 g hg S hS hz t)
  let C := fun t => coarseSphereScalarMulL (smoothSphereValue
    (coefficientSmoothData (commonSupportCoefficientFamily 2 g hg S hS hz t)))
  let G := compactCoefficient 2 b hb (HasCompactSupport.intro hS hzb)
  let I := sphereSobolevInclusionL 1 0 (by norm_num)
  have hM : DifferentiableAt ℝ M 0 :=
    (contDiff_oneBoundaryCoefficientMulL_commonSupport g hg S hS hz).differentiable (by simp) 0
  have hC := hasDerivAt_commonSupport_coarseCoefficientMul g hg S hS hz b hb hzb hSlice
  have hEq : deriv M 0 = oneBoundaryCoefficientMulL G := by
    apply ContinuousLinearMap.ext
    intro u
    apply sphereSobolevInclusionL_injective 1 0 (by norm_num)
    have hLeft := I.hasFDerivAt.comp_hasDerivAt (0:ℝ)
      (hM.hasDerivAt.clm_apply (hasDerivAt_const (0:ℝ) u))
    have hRight := hC.clm_apply (hasDerivAt_const (0:ℝ) (I u))
    have hFun : (fun t => I (M t u)) = fun t => C t (I u) :=
      funext (fun t => oneBoundaryCoefficientMulL_coarse
        (commonSupportCoefficientFamily 2 g hg S hS hz t) u)
    change HasDerivAt (fun t => I (M t u)) _ 0 at hLeft
    rw [hFun] at hLeft
    have hDer := hLeft.unique hRight
    simp only [map_zero,add_zero] at hDer
    exact hDer.trans (oneBoundaryCoefficientMulL_coarse G u).symm
  exact hEq ▸ hM.hasDerivAt

end ShrinkingSpheres

import Proof.PrincipalModelScalarForm
import Proof.NativeFrameFirstScalarForm
import Proof.PrincipalCovariantNormalForm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

lemma finite_bounded_endpoints_combination {κ Mid Lo : Type*} [Fintype κ]
    [NormedAddCommGroup Mid] [NormedSpace ℝ Mid] [NormedAddCommGroup Lo] [NormedSpace ℝ Lo]
    (I0 : Mid →L[ℝ] Lo) (Zp : κ → Mid →L[ℝ] Mid) (Zn : κ → Lo →L[ℝ] Lo)
    (hZ : ∀ a,I0.comp (Zp a)=(Zn a).comp I0) (c : κ → ℝ) :
    I0.comp (∑ a,c a • Zp a)=(∑ a,c a • Zn a).comp I0 := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  exact Finset.sum_congr rfl (fun a _ => congrArg (fun z => c a • z) (DFunLike.congr_fun (hZ a) u))

lemma native_frame_first_bounded_compatible {d : Data} {y : X} {CC CH : ℝ}
    (Q0 : SmoothCoefficientJets 2)
    (C : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH) (i : I) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (nativeFrameFirstBoundedHalfL Q0 C i)=
      (nativeFrameFirstBoundedNegativeL Q0 C i).comp
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) :=
  finite_bounded_endpoints_combination _ _ _
    (fun a => radialScalarBounded_half_negative_compatible _ (nativeAxisNormalScalarCoefficient Q0 C a))
    (fun a => d.frame y i a)

def fullFirstScalarCoefficients {d : Data} {y : X} {CC CH : ℝ}
    (Q0 : SmoothCoefficientJets 2)
    (C : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH) (j : I) :
    TaylorGeneratorIndex → ClosedCoefficientJets 3 :=
  principalModelScalarCoefficients Q0 d y j+d.radius y • (∑ i : I,
    (frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
      frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i) • nativeFrameFirstScalarCoefficients Q0 C i)

def fullFirstBoundedNegativeL {d : Data} {y : X} {CC CH : ℝ}
    (Q0 : SmoothCoefficientJets 2)
    (C : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH) (j : I) :
    SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  d.radius y • (∑ i : I,(frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
    frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i) •
    (firstFrameAdjointCorrectionAtL (-(1/2:ℝ)) d y i+nativeFrameFirstBoundedNegativeL Q0 C i))

def fullFirstBoundedHalfL {d : Data} {y : X} {CC CH : ℝ}
    (Q0 : SmoothCoefficientJets 2)
    (C : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH) (j : I) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  d.radius y • (∑ i : I,(frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
    frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i) •
    (firstFrameAdjointCorrectionAtL (1/2:ℝ) d y i+nativeFrameFirstBoundedHalfL Q0 C i))

lemma full_first_bounded_compatible {d : Data} {y : X} {CC CH : ℝ}
    (Q0 : SmoothCoefficientJets 2)
    (C : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH) (j : I) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (fullFirstBoundedHalfL Q0 C j)=
      (fullFirstBoundedNegativeL Q0 C j).comp
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
  let I0 := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hF (i : I) : I0.comp (firstFrameAdjointCorrectionAtL (1/2:ℝ) d y i)=
      (firstFrameAdjointCorrectionAtL (-(1/2:ℝ)) d y i).comp I0 :=
    ContinuousLinearMap.ext (fun u => firstFrameAdjointCorrectionAtL_inclusion _ _ (by norm_num) d y i u)
  have hBoth (i : I) : I0.comp (firstFrameAdjointCorrectionAtL (1/2:ℝ) d y i+nativeFrameFirstBoundedHalfL Q0 C i)=
      (firstFrameAdjointCorrectionAtL (-(1/2:ℝ)) d y i+nativeFrameFirstBoundedNegativeL Q0 C i).comp I0 :=
    (ContinuousLinearMap.comp_add _ _ _).trans
      ((congrArg₂ (fun U V : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => U+V)
        (hF i) (native_frame_first_bounded_compatible Q0 C i)).trans (ContinuousLinearMap.add_comp _ _ _).symm)
  have hSum := finite_bounded_endpoints_combination I0 _ _ hBoth
    (fun i => frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
      frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i)
  exact (ContinuousLinearMap.comp_smul _ _ _).trans
    ((congrArg (fun T => d.radius y • T) hSum).trans (ContinuousLinearMap.smul_comp _ _ _).symm)

def PhysicalPrincipalData.firstDerivativeHigherL {Y : Set X} {d : Data} {CF CT : ℝ}
    (D : PhysicalPrincipalData Y d CF CT) (y : X) (j : I) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  principalModelFirstDerivativeHigherL d y j+d.radius y • (∑ i : I,
    (frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
      frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i) •
      ((firstFrameAdjointCorrectionAtL (1/2:ℝ) d y i).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))+D.first.high i y))

private lemma full_first_scalar_low_aux
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K} (T : NativeTaylorGeneratorBounds s h hK CG)
    {m : ℕ} {ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) (hy : y ∈ Y)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    {CDF CDT CC CH : ℝ} (D : PhysicalPrincipalData Y d CDF CDT)
    (C : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH) (j : I) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    D.firstDerivativeHalfL y j=
      rightScalarCombinationL (taylorGeneratorLow (s.response.adjointHalfTaylor p))
        closedThreeJetHalfBoundaryScalarMultiplierL (fullFirstScalarCoefficients Q0 C j)+
      (fullFirstBoundedNegativeL Q0 C j).comp
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
  let c := fun i : I => q i j+q j i
  let Rlo := rightScalarCombinationL (taylorGeneratorLow (s.response.adjointHalfTaylor p)) closedThreeJetHalfBoundaryScalarMultiplierL
  have hFrame := T.actual_frame_first_error_scalar_endpoints hd hY hΩ hSub hy hF0 Q0 hQ0 D C
  have hModel := T.principal_model_scalar_endpoints hF0 Q0 hQ0 j
  have hML : principalModelFirstDerivativeHalfL d y j=Rlo (principalModelScalarCoefficients Q0 d y j) := by
    simpa only [Rlo,rightScalarCombinationL_apply] using hModel.1.symm
  exact scalar_model_plus_weighted_bounded Rlo _ _ _ hML
    (nativeFrameFirstScalarCoefficients Q0 C) (fun i => D.first.low i y)
    (fun i => firstFrameAdjointCorrectionAtL (-(1/2:ℝ)) d y i)
    (nativeFrameFirstBoundedNegativeL Q0 C) (fun i => (hFrame i).1) c (d.radius y)

private lemma full_first_scalar_high_aux
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K} (T : NativeTaylorGeneratorBounds s h hK CG)
    {m : ℕ} {ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) (hy : y ∈ Y)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    {CDF CDT CC CH : ℝ} (D : PhysicalPrincipalData Y d CDF CDT)
    (C : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH) (j : I) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    D.firstDerivativeHigherL y j=
      rightScalarCombinationL (taylorGeneratorHigh (T.domain.adjointHigherTaylor h hK (by norm_num) p))
        closedThreeJetHigherScalarMultiplierL (fullFirstScalarCoefficients Q0 C j)+
      (fullFirstBoundedHalfL Q0 C j).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
  let c := fun i : I => q i j+q j i
  let Rhi := rightScalarCombinationL (taylorGeneratorHigh (T.domain.adjointHigherTaylor h hK (by norm_num) p)) closedThreeJetHigherScalarMultiplierL
  have hFrame := T.actual_frame_first_error_scalar_endpoints hd hY hΩ hSub hy hF0 Q0 hQ0 D C
  have hModel := T.principal_model_scalar_endpoints hF0 Q0 hQ0 j
  have hMH : principalModelFirstDerivativeHigherL d y j=Rhi (principalModelScalarCoefficients Q0 d y j) := by
    simpa only [Rhi,rightScalarCombinationL_apply] using hModel.2.symm
  exact scalar_model_plus_weighted_bounded Rhi _ _ _ hMH
    (nativeFrameFirstScalarCoefficients Q0 C) (fun i => D.first.high i y)
    (fun i => firstFrameAdjointCorrectionAtL (1/2:ℝ) d y i)
    (nativeFrameFirstBoundedHalfL Q0 C) (fun i => (hFrame i).2) c (d.radius y)

/-- Complete actual first-base coefficient at both genuine endpoints. -/
lemma NativeTaylorGeneratorBounds.full_first_derivative_scalar_endpoints
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K} (T : NativeTaylorGeneratorBounds s h hK CG)
    {m : ℕ} {ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) (hy : y ∈ Y)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    {CDF CDT CC CH : ℝ} (D : PhysicalPrincipalData Y d CDF CDT)
    (C : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH) (j : I) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    D.firstDerivativeHalfL y j=
      rightScalarCombinationL (taylorGeneratorLow (s.response.adjointHalfTaylor p))
        closedThreeJetHalfBoundaryScalarMultiplierL (fullFirstScalarCoefficients Q0 C j)+
      (fullFirstBoundedNegativeL Q0 C j).comp
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) ∧
    D.firstDerivativeHigherL y j=
      rightScalarCombinationL (taylorGeneratorHigh (T.domain.adjointHigherTaylor h hK (by norm_num) p))
        closedThreeJetHigherScalarMultiplierL (fullFirstScalarCoefficients Q0 C j)+
      (fullFirstBoundedHalfL Q0 C j).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  exact ⟨full_first_scalar_low_aux T hd hY hΩ hSub hy hF0 Q0 hQ0 D C j,
    full_first_scalar_high_aux T hd hY hΩ hSub hy hF0 Q0 hQ0 D C j⟩
end ShrinkingSpheres

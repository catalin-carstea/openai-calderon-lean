import Proof.ActualFirstErrorNativeIdentification
import Proof.ScalarPlusBoundedCombination
import Proof.UniformPhysicalPrincipalData
import Proof.NativeFirstErrorScalarEndpoints
import Proof.FrameEndpointCombination
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def nativeAxisNormalScalarCoefficient {d : Data} {y : X} {CC CH : ℝ}
    (Q0 : SmoothCoefficientJets 2)
    (C : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH) (a : I) :
    ClosedCoefficientJets 3 :=
  ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((C a j).closed ((y,frameVectorLinear d.frame y),0))

def nativeFrameFirstScalarCoefficients {d : Data} {y : X} {CC CH : ℝ}
    (Q0 : SmoothCoefficientJets 2)
    (C : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH) (i : I) :
    TaylorGeneratorIndex → ClosedCoefficientJets 3 :=
  ∑ a : I,d.frame y i a • actualFirstErrorGeneratorCoefficients Q0 (C a)

def nativeFrameFirstBoundedNegativeL {d : Data} {y : X} {CC CH : ℝ}
    (Q0 : SmoothCoefficientJets 2)
    (C : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH) (i : I) :
    SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ a : I,d.frame y i a • radialScalarBoundedNegativeL
    (normalFrameRelativeFirstCovector d.γ d.g₁ ((y,frameVectorLinear d.frame y),0))
    (nativeAxisNormalScalarCoefficient Q0 C a)

def nativeFrameFirstBoundedHalfL {d : Data} {y : X} {CC CH : ℝ}
    (Q0 : SmoothCoefficientJets 2)
    (C : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH) (i : I) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  ∑ a : I,d.frame y i a • radialScalarBoundedHalfL
    (normalFrameRelativeFirstCovector d.γ d.g₁ ((y,frameVectorLinear d.frame y),0))
    (nativeAxisNormalScalarCoefficient Q0 C a)

private lemma native_frame_first_scalar_low_aux
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
    (C : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH) (i : I) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    D.first.low i y=
      rightScalarCombinationL (taylorGeneratorLow (s.response.adjointHalfTaylor p))
        closedThreeJetHalfBoundaryScalarMultiplierL (nativeFrameFirstScalarCoefficients Q0 C i)+
      (nativeFrameFirstBoundedNegativeL Q0 C i).comp
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let Rlo := rightScalarCombinationL (taylorGeneratorLow (s.response.adjointHalfTaylor p)) closedThreeJetHalfBoundaryScalarMultiplierL
  let Qa := fun a : I => actualFirstErrorGeneratorCoefficients Q0 (C a)
  let Zn := fun a : I => radialScalarBoundedNegativeL (normalFrameRelativeFirstCovector d.γ d.g₁ p) (nativeAxisNormalScalarCoefficient Q0 C a)
  let L := fun a : I => s.firstAdjointHalfErrorFamily (C a) p
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hE (a : I) := s.actual_first_error_coarse_native_eq T.domain hY hΩ hSub hd.1 hK hy hr.ne'
    hd.2.2.2.2.1.1 (C a) D.radial D.adjoint (D.center a) D.radial_actual D.adjoint_pair (D.center_actual a)
  have hL (a : I) : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (actualFirstAdjointErrorFamily d (axis a) D.adjoint (D.center a) y)=
      (L a).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    rw [hE a]
    exact s.firstAdjointHalfErrorFamily_coarse_compatible (C a) T.domain hF0 p T.domain.pointMem
  have hLoEq := half_endpoint_unique_of_coarse _ _ _ (D.first.low_coarse i y hy)
    (frame_low_endpoint_combination d D.adjoint D.center i y L hL)
  have hLform (a : I) : L a=Rlo (Qa a)+(Zn a).comp
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
    simpa only [Rlo,rightScalarCombinationL_apply,Qa,Zn,nativeAxisNormalScalarCoefficient] using
      (s.first_error_scalar_endpoint_realization T (C a) hF0 Q0 hQ0 hr).1
  exact hLoEq.trans (finite_scalar_plus_bounded_combination Rlo _ Qa L Zn hLform (fun a => d.frame y i a))

private lemma native_frame_first_scalar_high_aux
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
    (C : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH) (i : I) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    D.first.high i y=
      rightScalarCombinationL (taylorGeneratorHigh (T.domain.adjointHigherTaylor h hK (by norm_num) p))
        closedThreeJetHigherScalarMultiplierL (nativeFrameFirstScalarCoefficients Q0 C i)+
      (nativeFrameFirstBoundedHalfL Q0 C i).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let Rhi := rightScalarCombinationL (taylorGeneratorHigh (T.domain.adjointHigherTaylor h hK (by norm_num) p)) closedThreeJetHigherScalarMultiplierL
  let Qa := fun a : I => actualFirstErrorGeneratorCoefficients Q0 (C a)
  let Zp := fun a : I => radialScalarBoundedHalfL (normalFrameRelativeFirstCovector d.γ d.g₁ p) (nativeAxisNormalScalarCoefficient Q0 C a)
  let H := fun a : I => Rhi (Qa a)+(Zp a).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hE (a : I) := s.actual_first_error_coarse_native_eq T.domain hY hΩ hSub hd.1 hK hy hr.ne'
    hd.2.2.2.2.1.1 (C a) D.radial D.adjoint (D.center a) D.radial_actual D.adjoint_pair (D.center_actual a)
  have hH (a : I) : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (H a)=
      (actualFirstAdjointErrorFamily d (axis a) D.adjoint (D.center a) y).comp
        (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
    rw [hE a]
    simpa only [H,Rhi,rightScalarCombinationL_apply,Qa,Zp,nativeAxisNormalScalarCoefficient] using
      (s.first_error_scalar_endpoint_realization T (C a) hF0 Q0 hQ0 hr).2
  have hHiEq := higher_endpoint_unique_of_coarse _ _ _ (D.first.high_coarse i y hy)
    (frame_high_endpoint_combination d D.adjoint D.center i y H hH)
  exact hHiEq.trans (finite_scalar_plus_bounded_combination Rhi _ Qa H Zp (fun _ => rfl) (fun a => d.frame y i a))

/-- One native packet realizes all3coordinate directions and both SAME physical frame endpoints. -/
lemma NativeTaylorGeneratorBounds.actual_frame_first_error_scalar_endpoints
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
    (C : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH) (i : I) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    D.first.low i y=
      rightScalarCombinationL (taylorGeneratorLow (s.response.adjointHalfTaylor p))
        closedThreeJetHalfBoundaryScalarMultiplierL (nativeFrameFirstScalarCoefficients Q0 C i)+
      (nativeFrameFirstBoundedNegativeL Q0 C i).comp
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) ∧
    D.first.high i y=
      rightScalarCombinationL (taylorGeneratorHigh (T.domain.adjointHigherTaylor h hK (by norm_num) p))
        closedThreeJetHigherScalarMultiplierL (nativeFrameFirstScalarCoefficients Q0 C i)+
      (nativeFrameFirstBoundedHalfL Q0 C i).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  exact ⟨native_frame_first_scalar_low_aux T hd hY hΩ hSub hy hF0 Q0 hQ0 D C i,
    native_frame_first_scalar_high_aux T hd hY hΩ hSub hy hF0 Q0 hQ0 D C i⟩
end ShrinkingSpheres

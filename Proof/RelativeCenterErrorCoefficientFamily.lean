import Proof.UniformRelativeCenterErrorHorizontalMultiplier
import Proof.Archive.NativeH2SmoothMultiplierDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

structure RelativeCenterErrorCoefficientFamily (d : Data) (y a : X) (j : I) (C CH : ℝ) where
  scalar : NormalFrameRelativeParameter × X → ℝ
  smooth : ContDiff ℝ ∞ scalar
  support : Set X
  compact : IsCompact support
  supported : ∀ p z,z ∉ support → scalar (p,z)=0
  domain : Set NormalFrameRelativeParameter
  isOpen : IsOpen domain
  point : ((y,frameVectorLinear d.frame y),0) ∈ domain
  actual : ∀ p ∈ domain,∀ z ∈ Metric.closedBall (0:X) 2,scalar =ᶠ[𝓝 (p,z)]
    normalFrameRelativeCenterErrorWeight d.γ d.expMap (d.radius y) a j
  joint : ∀ n : ℕ,n ≤ 3 → ‖iteratedFDeriv ℝ n
    (commonSupportClosedCoefficientFamily 3 scalar smooth support compact supported)
    ((y,frameVectorLinear d.frame y),0)‖ ≤ C*‖a‖*(d.radius y)^2
  horizontal : NormalFrameRelativeHorizontalTaylorBounds d y
    (commonSupportClosedCoefficientFamily 3 scalar smooth support compact supported) (CH*‖a‖)

def RelativeCenterErrorCoefficientFamily.closed {d : Data} {y a : X} {j : I} {C CH : ℝ}
    (s : RelativeCenterErrorCoefficientFamily d y a j C CH) : NormalFrameRelativeParameter → ClosedCoefficientJets 3 :=
  commonSupportClosedCoefficientFamily 3 s.scalar s.smooth s.support s.compact s.supported

def RelativeCenterErrorCoefficientFamily.pointCoefficient {d : Data} {y a : X} {j : I} {C CH : ℝ}
    (s : RelativeCenterErrorCoefficientFamily d y a j C CH) : SmoothCoefficientJets 2 :=
  smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 s.scalar s.smooth s.support s.compact s.supported
    ((y,frameVectorLinear d.frame y),0))

theorem RelativeCenterErrorCoefficientFamily.point_coefficient_actual {d : Data} {y a : X} {j : I} {C CH : ℝ}
    (s : RelativeCenterErrorCoefficientFamily d y a j C CH) (z : X) (hz : z ∈ Metric.closedBall (0:X) 2) :
    coefficientValue 2 s.pointCoefficient =ᶠ[𝓝 z] (fun w => metricPair d.γ y
      ((normalizedParallelCenterJacobian d.γ d.expMap y
        (d.radius y • frameVector d.frame y w)-ContinuousLinearMap.id ℝ X) a) (d.frame y j)) := by
  have hNear := (s.actual _ s.point z hz).comp_tendsto (continuous_const.prodMk continuous_id).continuousAt.tendsto
  have hValue : coefficientValue 2 s.pointCoefficient = fun w => s.scalar (((y,frameVectorLinear d.frame y),0),w) := by
    rw [RelativeCenterErrorCoefficientFamily.pointCoefficient,coefficientValue_smoothMultiplierLowerJets]
    funext w
    exact coefficientValue_commonSupportCoefficientFamily 3 s.scalar s.smooth s.support s.compact s.supported _ w
  rw [hValue]
  filter_upwards [hNear] with w hw
  change s.scalar (((y,frameVectorLinear d.frame y),0),w) = _ at hw
  simpa only [normalFrameRelativeCenterErrorWeight,normalFrameRelativeParallelCenterError,
    normalFrameRelativeRadiusInput,normalFrameRadialParallelCenter,Function.comp_apply,
    normalFrameParallelCenterJacobian,normalFrameRadialReorderL_apply,
    add_zero,one_mul,normalFrameInput,frameVectorLinear_apply,frameVector_axis,id_eq] using hw

theorem RelativeCenterErrorCoefficientFamily.point_coefficient_local_C1 {d : Data} {y a : X} {j : I} {C CH : ℝ}
    (s : RelativeCenterErrorCoefficientFamily d y a j C CH) :
    LocalC1Bound (coefficientValue 2 s.pointCoefficient) (C*‖a‖*(d.radius y)^2) := by
  let Q := commonSupportCoefficientFamily 3 s.scalar s.smooth s.support s.compact s.supported
    ((y,frameVectorLinear d.frame y),0)
  have hNorm : ‖Q‖ ≤ C*‖a‖*(d.radius y)^2 := by
    have hh := s.joint 0 (by omega)
    rw [norm_iteratedFDeriv_zero] at hh
    change ‖Q‖ ≤ _ at hh
    exact hh
  rw [RelativeCenterErrorCoefficientFamily.pointCoefficient,coefficientValue_smoothMultiplierLowerJets]
  intro z hz
  constructor
  · have hh := norm_iteratedFDeriv_coefficientValue_le 3 Q 0 (by omega) z
    have hh0 : |coefficientValue 3 Q z| ≤ ‖Q‖ := by simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hh
    exact hh0.trans hNorm
  · have hh := norm_iteratedFDeriv_coefficientValue_le 3 Q 1 (by omega) z
    have hh1 : ‖fderiv ℝ (coefficientValue 3 Q) z‖ ≤ ‖Q‖ := by simpa only [norm_iteratedFDeriv_one] using hh
    exact hh1.trans hNorm

/-- Uniform production of the complete same-family coefficient packet. -/
theorem uniform_relative_center_error_coefficient_families {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C CH : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ 1 ≤ CH ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ a : X,∀ j : I,
      Nonempty (RelativeCenterErrorCoefficientFamily d y a j C CH) := by
  obtain ⟨η,C,CH,hη,hη1,hC,hCH,hFamilies⟩ := uniform_relative_center_error_horizontal_multiplier
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,C,CH,hη,hη1,hC,hCH,?_⟩
  intro floor hf ε hε hSmall d hd y hy a j
  obtain ⟨A,hA,S,hS,hz,V,hV,hMem,hRep,hJets,hHorizontal⟩ := hFamilies floor hf ε hε hSmall d hd y hy a j
  exact ⟨⟨A,hA,S,hS,hz,V,hV,hMem,hRep,hJets,hHorizontal⟩⟩

end ShrinkingSpheres

import Proof.UniformRelativeRadiusLowRadialEndpoints
import Proof.NormalizedMidpointRadialRealization
import Proof.CommonSupportRadialMidpointDerivativeData
import Proof.CommonSupportMidpointRadialRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Uniform actual H1-to-L2 quadratic radial Taylor derivative along the
    normalized affine parallel center family, with radius held fixed.
    Its actual endpoint realization and canonical first covector are retained. -/
theorem uniform_relative_radius_midpoint_radial_derivative {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ A A1 : ℝ × X → Mat,∃ hA : ContDiff ℝ ∞ A,∃ hA1 : ContDiff ℝ ∞ A1,
      ∃ S : Set X,∃ hS : IsCompact S,∃ hz : ∀ t z,z ∉ S → A (t,z) = 0,
      ∃ hz1 : ∀ t z,z ∉ S → A1 (t,z) = 0,
      ∃ V : Set ℝ,IsOpen V ∧ (0:ℝ) ∈ V ∧ (∀ t ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A =ᶠ[𝓝 (t,z)]
        relativeDilationFamily (normalizedFirstNormalCoefficient d y)) ∧
      (∀ t ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A1 =ᶠ[𝓝 (t,z)]
        relativeDilationFamily (scalarFirstCoefficient (firstDensityLogCovector d y))) ∧
      ∃ R : ℝ → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ContDiffOn ℝ ∞ R V ∧
        (∀ t ∈ V,(R t).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
          (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
            (actualHighRadialErrorL (commonSupportMatrixFamily 2 A hA S hS hz t))) ∧
        RealizesActualMidpointRadialError d y (R 0) ∧
        let T := fun t => R t-d.radius y •
          (coarseFirstRadialVariationL 1 ((1+t) • firstDensityLogCovector d y)).comp
            (sphereSobolevInclusionL 1 0 (by norm_num))
        DifferentiableAt ℝ T 0 ∧ ‖fderiv ℝ T 0‖ ≤ C*(d.radius y)^2 := by
  obtain ⟨ηL,CH,CL,F0,hηL,hCH,hCL,hF0,hData⟩ :=
    uniform_relative_radius_low_radial_endpoints hY hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηL 1,(CL+CH)/2,lt_min hηL zero_lt_one,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  obtain ⟨A,A1,hA,hA1,S,hS,hz,hz1,V,hV,h0V,hRep,hRep1,hInvS,hCoercive,hNormal,hHigh,hLowDiff,hLow⟩ :=
      hData floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  let r := d.radius y
  let ell : ℝ → X →L[ℝ] ℝ := fun t => (1+t) • firstDensityLogCovector d y
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε : r ≤ ε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans (min_le_right _ _))
  obtain ⟨R,hR,hRestrict⟩ := exists_commonSupport_smooth_midpoint_radial_family A hA S hS hz V hV
    hCoercive hInvS hNormal
  have hField (z : X) (hzB : z ∈ (ballOpens:Set X)) : coefficientMatrixField 2
      (commonSupportMatrixFamily 2 A hA S hS hz 0) z = normalizedFirstNormalCoefficient d y z := by
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    simpa only [relativeDilationFamily,add_zero,one_smul] using
      (hRep 0 h0V z (unitBall_subset_closedBall_two hzB)).eq_of_nhds
  have hActual := realizesActualMidpointRadialError_of_normalized_restriction d y (R 0)
    (commonSupportMatrixFamily 2 A hA S hS hz 0) hField (hInvS 0 h0V) (hRestrict 0 h0V)
  have hRDiff := (hR.contDiffAt (hV.mem_nhds h0V)).differentiableAt (by simp)
  have hEllSmooth : ContDiff ℝ ∞ ell := (contDiff_const.add contDiff_id).smul contDiff_const
  have hEllDiff : DifferentiableAt ℝ ell 0 := hEllSmooth.differentiable (by simp) 0
  have hFirst (t : ℝ) (ht : t ∈ V) (z : X) (hzB : z ∈ Metric.closedBall (0:X) 2) :
      A1 (t,z) = ell t z • (1:Mat) := ((hRep1 t ht z hzB).eq_of_nhds).trans
        (relativeDilation_scalarFirstCoefficient (firstDensityLogCovector d y) (t,z))
  have hLowBound : ‖fderiv ℝ (fun t => commonSupportLowRadialErrorL A hA S hS hz t-
      r • commonSupportLowFirstRadialL A1 hA1 S hS hz1 1 t) 0‖ ≤ CL*r^2 :=
    hLow.trans_eq (by ring)
  have hHighBound : ‖fderiv ℝ (fun t => actualHighRadialErrorL (commonSupportMatrixFamily 2 A hA S hS hz t)-
      r • highFirstRadialVariationL F0 (commonSupportMatrixFamily 2 A1 hA1 S hS hz1 t) 1) 0‖ ≤ CH*r^2 :=
    hHigh.trans_eq (by ring)
  have hMid := commonSupport_radial_midpoint_derivative_data A A1 hA hA1 S S hS hS hz hz1 F0
    (fun z hzB => hF0 z (unitBall_subset_closedBall_two hzB)) ell R 0 V hV h0V r CL CH
    hr.le hr1 hCL hCH hRDiff hEllDiff hCoercive hInvS hNormal hFirst hRestrict
    hLowDiff hLowBound hHighBound
  refine ⟨A,A1,hA,hA1,S,hS,hz,hz1,V,hV,h0V,hRep,hRep1,R,hR,hRestrict,hActual,hMid.1,hMid.2.trans_eq ?_⟩
  ring

end ShrinkingSpheres

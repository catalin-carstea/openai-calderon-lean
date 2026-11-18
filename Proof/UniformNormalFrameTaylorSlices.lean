import Proof.NormalFrameRadialTaylorModel
import Proof.CommonSupportMidpointCurveCongruence
import Proof.UniformParallelMidpointRadialDerivative
import Proof.UniformRelativeRadiusMidpointRadialDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The uniform parallel-center Taylor bound holds for any genuine master
    radial family, through exact coefficient and midpoint germ comparison. -/
theorem uniform_normalFrame_parallel_taylor_slice {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 5 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ 0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ a : X,
      ∀ (A : NormalFrameParameter × X → Mat) (hA : ContDiff ℝ ∞ A)
        (S : Set X) (hS : IsCompact S) (hz : ∀ p z,z ∉ S → A (p,z) = 0)
        (V : Set NormalFrameParameter) (hV : IsOpen V)
        (hp0 : (y,(d.radius y,frameVectorLinear d.frame y)) ∈ V)
        (hRep : ∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,
          A =ᶠ[𝓝 (p,z)] normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap)
        (R : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
        (hRestrict : ∀ p ∈ V,(R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
          (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
            (actualHighRadialErrorL (commonSupportMatrixFamily 2 A hA S hS hz p))),
      let T := fun t => normalFrameRadialTaylorFamily d R (normalFrameParallelCurve d.γ d.frame d.radius y a t)
      DifferentiableAt ℝ T 0 ∧ ‖fderiv ℝ T 0‖ ≤ C*(d.radius y)^2*‖a‖ := by
  obtain ⟨η,C,hη,hC,hData⟩ := uniform_parallel_midpoint_radial_derivative hY hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,C,hη,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy a A hA S hS hz V hV hp0 hRep R hRestrict
  obtain ⟨B,B1,hB,hB1,SB,hSB,hzB,hzB1,W,hW,h0W,hWY,hRepB,hRepB1,Q,hQ,hResQ,hActual,hDiff,hNorm⟩ :=
    hData floor hf ε hε hSmall d hd y hy a
  let c := normalFrameParallelCurve d.γ d.frame d.radius y a
  have hc : ContinuousAt c 0 := (hasDerivAt_normalFrameParallelCurve d.γ d.frame d.radius y a).continuousAt
  have h0V : c 0 ∈ V := by simpa only [c,normalFrameParallelCurve_zero] using hp0
  have hValue (t : ℝ) (ht : t ∈ W) (hcV : c t ∈ V) (z : X) (hzBall : z ∈ Metric.closedBall (0:X) 2) :
      A (c t,z) = B (t,z) := by
    exact ((hRep (c t) hcV z hzBall).eq_of_nhds).trans
      ((normalFrameNormalizedCoefficient_parallel d.γ d.g₁ d.expMap d.frame d.radius y a z t).trans
        (hRepB t ht z hzBall).eq_of_nhds.symm)
  have hGerm := commonSupport_midpoint_curve_germ_congr A hA S hS hz B hB SB hSB hzB
    c hc V hV h0V W hW h0W hValue R Q hRestrict hResQ
  have hTaylor : (fun t => normalFrameRadialTaylorFamily d R (c t)) =ᶠ[𝓝 (0:ℝ)]
      fun t => Q t-d.radius y •
        (coarseFirstRadialVariationL 1 (parallelFirstCoefficientCovector d.γ d.g₁ y a (frameVectorLinear d.frame y) t)).comp
          (sphereSobolevInclusionL 1 0 (by norm_num)) := by
    filter_upwards [hGerm] with t ht
    rw [normalFrameRadialTaylorFamily_parallel,ht]
  refine ⟨hDiff.congr_of_eventuallyEq hTaylor,?_⟩
  rw [hTaylor.fderiv_eq]
  exact hNorm

/-- The same master remainder has the uniformly quadratic relative-radius
    derivative supplied by the independently checked dilation family. -/
theorem uniform_normalFrame_radius_taylor_slice {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ 0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ (A : NormalFrameParameter × X → Mat) (hA : ContDiff ℝ ∞ A)
        (S : Set X) (hS : IsCompact S) (hz : ∀ p z,z ∉ S → A (p,z) = 0)
        (V : Set NormalFrameParameter) (hV : IsOpen V)
        (hp0 : (y,(d.radius y,frameVectorLinear d.frame y)) ∈ V)
        (hRep : ∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,
          A =ᶠ[𝓝 (p,z)] normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap)
        (R : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
        (hRestrict : ∀ p ∈ V,(R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
          (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
            (actualHighRadialErrorL (commonSupportMatrixFamily 2 A hA S hS hz p))),
      let T := fun t => normalFrameRadialTaylorFamily d R (normalFrameRadiusCurve d.frame d.radius y t)
      DifferentiableAt ℝ T 0 ∧ ‖fderiv ℝ T 0‖ ≤ C*(d.radius y)^2 := by
  obtain ⟨η,C,hη,hC,hData⟩ := uniform_relative_radius_midpoint_radial_derivative hY hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,C,hη,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy A hA S hS hz V hV hp0 hRep R hRestrict
  obtain ⟨B,B1,hB,hB1,SB,hSB,hzB,hzB1,W,hW,h0W,hRepB,hRepB1,Q,hQ,hResQ,hActual,hDiff,hNorm⟩ :=
    hData floor hf ε hε hSmall d hd y hy
  let c := normalFrameRadiusCurve d.frame d.radius y
  have hc : ContinuousAt c 0 := (hasDerivAt_normalFrameRadiusCurve d.frame d.radius y).continuousAt
  have h0V : c 0 ∈ V := by simpa only [c,normalFrameRadiusCurve_zero] using hp0
  have hValue (t : ℝ) (ht : t ∈ W) (hcV : c t ∈ V) (z : X) (hzBall : z ∈ Metric.closedBall (0:X) 2) :
      A (c t,z) = B (t,z) := by
    exact ((hRep (c t) hcV z hzBall).eq_of_nhds).trans
      ((normalFrameNormalizedCoefficient_relative_radius d y z t).trans (hRepB t ht z hzBall).eq_of_nhds.symm)
  have hGerm := commonSupport_midpoint_curve_germ_congr A hA S hS hz B hB SB hSB hzB
    c hc V hV h0V W hW h0W hValue R Q hRestrict hResQ
  have hTaylor : (fun t => normalFrameRadialTaylorFamily d R (c t)) =ᶠ[𝓝 (0:ℝ)]
      fun t => Q t-d.radius y •
        (coarseFirstRadialVariationL 1 ((1+t) • firstDensityLogCovector d y)).comp
          (sphereSobolevInclusionL 1 0 (by norm_num)) := by
    filter_upwards [hGerm] with t ht
    rw [hd.1.normalFrameRadialTaylorFamily_radius hΩ (zero_lt_one.trans_le hK) (hd.2.1.center_mem hy),ht]
  refine ⟨hDiff.congr_of_eventuallyEq hTaylor,?_⟩
  rw [hTaylor.fderiv_eq]
  exact hNorm

end ShrinkingSpheres

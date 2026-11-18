import Proof.UniformNormalFrameRadialFamily
import Proof.UniformNormalFrameTaylorSlices
import Proof.LogRadiusDirectionalBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- A single actual master radial family has a uniformly quadratic
    covariant center jet, including the actual moving radius. Its ordinary
    derivative minus the genuine frame-rotation derivatives is bounded by
    radius squared times beta. The geometric and native witnesses are shared
    for every center direction, and no frame derivative bound is assumed. -/
theorem uniform_normalFrame_covariant_radial_taylor_jet {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 5 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ 0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ A : NormalFrameParameter × X → Mat,∃ hA : ContDiff ℝ ∞ A,
      ∃ S : Set X,∃ hS : IsCompact S,∃ hz : ∀ p z,z ∉ S → A (p,z) = 0,
      ∃ V : Set NormalFrameParameter,IsOpen V ∧ (y,(d.radius y,frameVectorLinear d.frame y)) ∈ V ∧
        (∀ p ∈ V,p.1 ∈ Y) ∧
        (∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,
          A =ᶠ[𝓝 (p,z)] normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap) ∧
      ∃ R : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ContDiffOn ℝ ∞ R V ∧ ContDiffOn ℝ ∞ (normalFrameRadialTaylorFamily d R) V ∧
        (∀ x : X,(x,(d.radius x,frameVectorLinear d.frame x)) ∈ V →
          RealizesActualMidpointRadialError d x (R (x,(d.radius x,frameVectorLinear d.frame x)))) ∧
        (∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
          (commonSupportMatrixFamily 2 A hA S hS hz p)).IsInvertible) ∧
        (∀ p ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp A hA p))) ∧
        (∀ p ∈ V,(negativeBoundaryCoefficientMulL
          (normalCoefficientJet (commonSupportMatrixFamily 2 A hA S hS hz p))).IsInvertible) ∧
        (∀ p ∈ V,(R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
          (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
            (actualHighRadialErrorL (commonSupportMatrixFamily 2 A hA S hS hz p))) ∧
        ∀ a : X,
          let H := normalFrameRadialTaylorFamily d R
          ‖deriv (fun t => H (normalFrameActualCurve d.frame d.radius y a t)) 0-
            ∑ i,∑ j,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
              deriv (fun t => H (normalFrameRotationCurve d.frame d.radius y i j t)) 0‖ ≤
            C*(d.radius y)^2*beta d.γ d.radius y*‖a‖ := by
  obtain ⟨ηF,hηF,hFamily⟩ := uniform_normalFrame_local_radial_family hY hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηP,CP,hηP,hCP,hParallel⟩ := uniform_normalFrame_parallel_taylor_slice hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηR,CR,hηR,hCR,hRadius⟩ := uniform_normalFrame_radius_taylor_slice hY hΩ (by omega) K ρ c₀ M Cj hK hρ
  let C := CP+3*K*CR
  refine ⟨min ηF (min ηP ηR),C,lt_min hηF (lt_min hηP hηR),by dsimp [C];positivity,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hSF := hSmall.trans (min_le_left _ _)
  have hSP := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSR := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨A,hA,S,hS,hz,V,hV,hpV,hCenter,hRep,R,hR,hActual,hStrong,hCoercive,hNormal,hRestrict⟩ := hFamily floor hf ε hε hSF d hd y hy
  let H := normalFrameRadialTaylorFamily d R
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hCenter0 := hd.2.1.center_mem hy
  have hH : ContDiffOn ℝ ∞ H V := hd.1.contDiffOn_normalFrameRadialTaylorFamily hΩ hKpos R V hR
    (fun p hp => hd.2.1.center_mem (hCenter p hp))
  have hHDiff := (hH.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp)
  have hFrameSmooth : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Ω := hd.1.2.2.2.2.2.2.1
  have hFrameAll : ∀ x ∈ Ω,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j) = if i = j then 1 else 0 := hd.1.2.2.2.2.2.2.2
  have hFrameAt (i : I) := (hFrameSmooth i).contDiffAt (hΩ.mem_nhds hCenter0)
  have hFrameDiff (i : I) := (hFrameAt i).differentiableAt (by simp)
  have hF := (contDiffAt_frameVectorLinear d.frame y hFrameAt).differentiableAt (by simp)
  have hrDiff := ((hd.2.2.2.2.1.1).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hr0 := (hd.2.2.2.2.1.2 y hy).1.ne'
  have hBeta : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hRadial := hRadius floor hf ε hε hSR d hd y hy A hA S hS hz V hV hpV hRep R hRestrict
  have hRadialN : ‖deriv (fun t => H (normalFrameRadiusCurve d.frame d.radius y t)) 0‖ ≤ CR*(d.radius y)^2 :=
    norm_deriv_eq_norm_fderiv.le.trans hRadial.2
  refine ⟨A,hA,S,hS,hz,V,hV,hpV,hCenter,hRep,R,hR,hH,hActual,hStrong,hCoercive,hNormal,hRestrict,?_⟩
  intro a
  dsimp only
  have hParallelHere := hParallel floor hf ε hε hSP d hd y hy a A hA S hS hz V hV hpV hRep R hRestrict
  have hParallelN : ‖deriv (fun t => H (normalFrameParallelCurve d.γ d.frame d.radius y a t)) 0‖ ≤ CP*(d.radius y)^2*‖a‖ :=
    norm_deriv_eq_norm_fderiv.le.trans hParallelHere.2
  have hSkew := frameConnection_skew hΩ hd.1.1 hKpos d.frame hFrameSmooth hFrameAll hCenter0 a
  have hSplit := deriv_normalFrame_family_covariant_split d.γ d.frame d.radius y a H hrDiff hr0 hF hFrameDiff
    (hFrameAll y hCenter0) hSkew hHDiff
  change ‖deriv (fun t => H (normalFrameActualCurve d.frame d.radius y a t)) 0-
    ∑ i,∑ j,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
      deriv (fun t => H (normalFrameRotationCurve d.frame d.radius y i j t)) 0‖ ≤ _
  rw [hSplit]
  have hLog := hd.1.1.logRadius_direction_bound hK d.frame d.radius hCenter0 (hFrameAll y hCenter0) a
  have hBeta0 : 0 ≤ beta d.γ d.radius y := zero_le_one.trans hBeta
  have hPWeight : CP*(d.radius y)^2*‖a‖ ≤ CP*(d.radius y)^2*beta d.γ d.radius y*‖a‖ := by
    have hMul := mul_le_mul_of_nonneg_left hBeta (by positivity : 0 ≤ CP*(d.radius y)^2*‖a‖)
    simpa only [mul_one] using hMul.trans_eq (by ring)
  calc
    _ ≤ ‖deriv (fun t => H (normalFrameParallelCurve d.γ d.frame d.radius y a t)) 0‖+
        ‖(fderiv ℝ (fun x => Real.log (d.radius x)) y a) •
          deriv (fun t => H (normalFrameRadiusCurve d.frame d.radius y t)) 0‖ := norm_add_le _ _
    _ = ‖deriv (fun t => H (normalFrameParallelCurve d.γ d.frame d.radius y a t)) 0‖+
        |fderiv ℝ (fun x => Real.log (d.radius x)) y a| *
          ‖deriv (fun t => H (normalFrameRadiusCurve d.frame d.radius y t)) 0‖ := by rw [norm_smul,Real.norm_eq_abs]
    _ ≤ CP*(d.radius y)^2*‖a‖+(3*K*beta d.γ d.radius y*‖a‖)*(CR*(d.radius y)^2) :=
      add_le_add hParallelN (mul_le_mul hLog hRadialN (norm_nonneg _) (by positivity))
    _ ≤ CP*(d.radius y)^2*beta d.γ d.radius y*‖a‖+(3*K*beta d.γ d.radius y*‖a‖)*(CR*(d.radius y)^2) :=
      add_le_add hPWeight le_rfl
    _ = C*(d.radius y)^2*beta d.γ d.radius y*‖a‖ := by dsimp [C];ring

end ShrinkingSpheres

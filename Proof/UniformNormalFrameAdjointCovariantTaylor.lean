import Proof.UniformNormalFrameAdjointPointTaylor
import Proof.UniformNormalFrameCovariantAdjointSlice

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- The chosen actual master family has a true smooth physical adjoint,
quadratic point and covariant moving-radius Taylor bounds, and exact physical
adjunction on a direction-independent native inverse neighborhood. -/
theorem uniform_normalFrame_adjoint_covariant_taylor {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 5 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CFJ : ℝ) (hCFJ : 0 ≤ CFJ) :
    ∃ η CB CJ CD : ℝ,0 < η ∧ 0 ≤ CB ∧ 0 ≤ CJ ∧ 0 ≤ CD ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ A : NormalFrameParameter × X → Mat,∀ hA : ContDiff ℝ ∞ A,
      ∀ S : Set X,∀ hS : IsCompact S,∀ hz : ∀ p z,z ∉ S → A (p,z) = 0,
      ∀ V : Set NormalFrameParameter,IsOpen V → (y,(d.radius y,frameVectorLinear d.frame y)) ∈ V →
      (∀ p ∈ V,p.1 ∈ Y) →
      (∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,
        A =ᶠ[𝓝 (p,z)] normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap) →
      ∀ R : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ R V →
      (∀ x : X,(x,(d.radius x,frameVectorLinear d.frame x)) ∈ V →
        RealizesActualMidpointRadialError d x (R (x,(d.radius x,frameVectorLinear d.frame x)))) →
      (∀ p ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp A hA p))) →
      (∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
        (commonSupportMatrixFamily 2 A hA S hS hz p)).IsInvertible) →
      (∀ p ∈ V,(negativeBoundaryCoefficientMulL
        (normalCoefficientJet (commonSupportMatrixFamily 2 A hA S hS hz p))).IsInvertible) →
      (∀ p ∈ V,(R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
          (actualHighRadialErrorL (commonSupportMatrixFamily 2 A hA S hS hz p))) →
      ‖normalFrameRadialTaylorFamily d R (y,(d.radius y,frameVectorLinear d.frame y))‖ ≤ CFJ*(d.radius y)^2 →
      let Da := commonSupportRadialAdjointFamily A hA S hS hz R
      ∃ W : Set NormalFrameParameter,IsOpen W ∧
        (y,(d.radius y,frameVectorLinear d.frame y)) ∈ W ∧ W ⊆ V ∧
        ContDiffOn ℝ ∞ Da W ∧ ContDiffOn ℝ ∞ (normalFrameRadialAdjointTaylorFamily d Da) W ∧
        (∀ p ∈ W,(oneBoundaryCoefficientMulL
          (normalCoefficientJet (commonSupportMatrixFamily 2 A hA S hS hz p))).IsInvertible) ∧
        ‖firstRadialCorrectionL d y‖ ≤ CB ∧
        ‖normalFrameRadialAdjointTaylorFamily d Da (y,(d.radius y,frameVectorLinear d.frame y))‖ ≤ CJ*(d.radius y)^2 ∧
        (∀ a : X,
          let H := normalFrameRadialAdjointTaylorFamily d Da
          ‖deriv (fun t => H (normalFrameActualCurve d.frame d.radius y a t)) 0-
            ∑ i,∑ j,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
              deriv (fun t => H (normalFrameRotationCurve d.frame d.radius y i j t)) 0‖ ≤
            CD*(d.radius y)^2*beta d.γ d.radius y*‖a‖) ∧
        ∀ x : X,(x,(d.radius x,frameVectorLinear d.frame x)) ∈ W → ∀ u v,
          ⟪(R (x,(d.radius x,frameVectorLinear d.frame x))+sphereSobolevDegreeL) u,
            sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
          ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Da (x,(d.radius x,frameVectorLinear d.frame x)) v⟫_ℝ := by
  obtain ⟨ηP,CB,CJ,hηP,hCB,hCJ,hPoint⟩ := uniform_normalFrame_adjoint_point_taylor (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηD,CD,hηD,hCD,hDerivative⟩ := uniform_normalFrame_covariant_adjoint_taylor_slice hY hΩ hm K ρ c₀ M Cj hK hρ CFJ hCFJ
  refine ⟨min ηP ηD,CB,CJ,CD,lt_min hηP hηD,hCB,hCJ,hCD,?_⟩
  intro floor hf ε hε hSmall d hd y hy A hA S hS hz V hV hp0 hCenter hRep R hR hActual hCoercive hStrong hNormal hRestrict hForwardPoint
  obtain ⟨W,hW,hpW,hSub,hDa,hModel,hOne,hB,hJ,hPair⟩ := hPoint floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
    A hA S hS hz V hV hp0 hCenter hRep R hR hActual hCoercive hStrong hNormal hRestrict
  have hHDiff := (hModel.contDiffAt (hW.mem_nhds hpW)).differentiableAt (by simp)
  have hJet := hDerivative floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy
    A hA S hS hz V hV hp0 hRep R hR hRestrict hForwardPoint hHDiff
  exact ⟨W,hW,hpW,hSub,hDa,hModel,hOne,hB,hJ,hJet,hPair⟩

end ShrinkingSpheres

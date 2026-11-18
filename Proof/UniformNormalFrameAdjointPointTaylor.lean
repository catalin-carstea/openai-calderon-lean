import Proof.NormalFrameRadialAdjointLift
import Proof.ActualRadialAdjointRepresentativeTaylor
import Proof.NormalFrameRadialAdjointTaylorModel

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

/-- The same chosen master family has a true smooth physical adjoint,
    canonical quadratic point remainder and genuine H1 normal inverses. The
    neighborhood is independent of every later differentiation direction. -/
theorem uniform_normalFrame_adjoint_point_taylor {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CB CJ : ℝ,0 < η ∧ 0 ≤ CB ∧ 0 ≤ CJ ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
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
      let Da := commonSupportRadialAdjointFamily A hA S hS hz R
      ∃ W : Set NormalFrameParameter,IsOpen W ∧
        (y,(d.radius y,frameVectorLinear d.frame y)) ∈ W ∧ W ⊆ V ∧
        ContDiffOn ℝ ∞ Da W ∧ ContDiffOn ℝ ∞ (normalFrameRadialAdjointTaylorFamily d Da) W ∧
        (∀ p ∈ W,(oneBoundaryCoefficientMulL
          (normalCoefficientJet (commonSupportMatrixFamily 2 A hA S hS hz p))).IsInvertible) ∧
        ‖firstRadialCorrectionL d y‖ ≤ CB ∧
        ‖normalFrameRadialAdjointTaylorFamily d Da (y,(d.radius y,frameVectorLinear d.frame y))‖ ≤ CJ*(d.radius y)^2 ∧
        ∀ x : X,(x,(d.radius x,frameVectorLinear d.frame x)) ∈ W → ∀ u v,
          ⟪(R (x,(d.radius x,frameVectorLinear d.frame x))+sphereSobolevDegreeL) u,
            sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
          ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Da (x,(d.radius x,frameVectorLinear d.frame x)) v⟫_ℝ := by
  obtain ⟨ηL,hηL,hLift⟩ := uniform_normalFrame_radial_adjoint_lift hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηT,CB,CJ,hηT,hCB,hCJ,hPoint⟩ :=
    uniform_actual_radial_adjoint_representative_taylor (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηL ηT,CB,CJ,lt_min hηL hηT,hCB,hCJ,?_⟩
  intro floor hf ε hε hSmall d hd y hy A hA S hS hz V hV hp0 hCenter hRep R hR hActual hCoercive hStrong hNormal hRestrict
  obtain ⟨W,hW,hpW,hSub,hDa,hOne,hPair⟩ := hLift floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
    A hA S hS hz V hV hp0 hCenter hRep R hR hCoercive hStrong hNormal hRestrict
  let Da := commonSupportRadialAdjointFamily A hA S hS hz R
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hModel := hd.1.contDiffOn_normalFrameRadialAdjointTaylorFamily hΩ hKpos Da W hDa
    (fun p hp => hd.2.1.center_mem (hCenter p (hSub hp)))
  have hT := hPoint floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy
    (R (y,(d.radius y,frameVectorLinear d.frame y))) (Da (y,(d.radius y,frameVectorLinear d.frame y)))
    (hActual y hp0) (hPair y hpW)
  refine ⟨W,hW,hpW,hSub,hDa,hModel,hOne,hT.1,?_,hPair⟩
  rw [hd.1.normalFrameRadialAdjointTaylorFamily_actual hΩ hKpos (hd.2.1.center_mem hy)]
  exact hT.2

end ShrinkingSpheres

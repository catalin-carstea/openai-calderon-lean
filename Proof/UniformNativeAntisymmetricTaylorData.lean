import Proof.NativeAntisymmetricTaylorJets
import Proof.UniformNativeAntisymmetricTaylorGraph
import Proof.UniformNativeRelativeSymmetricHigherData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

theorem uniform_native_antisymmetric_taylor_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) :
    ∃ η CR CK : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ CR ∧ 0 ≤ CK ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ CF CA CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∃ R : RelativeNormalScalarRemainderFamily d y CR,
      ∃ ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
        ((volume:Measure X).restrict ballOpens),
      ∃ _V : s.response.SymmetricAdjointDomain,
      let KF := fun p => s.response.antisymmetricTaylorKernel F0 ha0 (R.normalCoefficient Q p)
        (linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ p)) p
      SmoothFiniteJetBound KF ((y,frameVectorLinear d.frame y),0) 3 (CK*(d.radius y)^2) ∧
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
        (s.response.adjointTaylor ((y,frameVectorLinear d.frame y),0)-s.response.forwardTaylor ((y,frameVectorLinear d.frame y),0))=
        (KF ((y,frameVectorLinear d.frame y),0)).comp (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)) := by
  obtain ⟨ηR,CR,hηR,hηR1,hCR,hR⟩ := uniform_relative_normal_scalar_remainder_family hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηG,hηG,hGraph⟩ := uniform_native_antisymmetric_taylor_graph (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηS,CSF,CSA,hηS,hηS1,hCSF,hCSA,hSym⟩ := uniform_native_relative_symmetric_higher_data
    hY hΩ 0 (by omega) K ρ c₀ M Cj hK hρ CI CW hCI hCW F0 hF0
  have ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens) :=
    memLp_nativeEnergyIntegrand_of_continuous _ _ _
      (continuous_pi (fun i => continuous_pi (fun j => (contDiff_coefficientValue 2 (F0 i j)).continuous)))
      continuous_const continuous_const
  let BM := ‖closedThreeJetNegativeScalarMultiplierL‖*(‖linearScalarClosedCoefficientL Q‖*CQ+CR)
  have hCR0 := zero_le_one.trans hCR
  have hBM : 0 ≤ BM := by dsimp only [BM];positivity
  let ηN := 1/(2*(1+BM))
  have hηN : 0 < ηN := by dsimp only [ηN];positivity
  let CK := nativeAntisymmetricTaylorJetBudget F0 ha0 Q CQ CI CW CR
  have hCK : 0 ≤ CK := by dsimp only [CK,nativeAntisymmetricTaylorJetBudget];positivity
  refine ⟨min ηR (min ηG (min ηS ηN)),CR,CK,
    lt_min hηR (lt_min hηG (lt_min hηS hηN)),(min_le_left _ _).trans hηR1,hCR,hCK,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF CA CM s
  have hSmallR := hSmall.trans (min_le_left _ _)
  have hSmallG := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallS := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hSmallN := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨R⟩ := hR floor hf ε hε hSmallR d hd y hy
  obtain ⟨V⟩ := hSym floor hf ε hε hSmallS d hd y hy CQ CF CA CM s
  have hr : 0 ≤ d.radius y := (hd.2.2.2.2.1.2 y hy).1.le
  have hrε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 := hrε.trans (hSmallR.trans hηR1)
  have hNear : BM*d.radius y ≤ (1/2:ℝ) := by
    have hP : 0 < 1+BM := by linarith
    have hMul := mul_le_mul_of_nonneg_left (hrε.trans hSmallN) hP.le
    have hEq : (1+BM)*ηN=(1/2:ℝ) := by dsimp only [ηN];field_simp
    rw [hEq] at hMul
    nlinarith only [hMul,hr]
  refine ⟨R,ha0,V.neighborhood,?_,?_⟩
  · exact s.antisymmetricTaylor_three_jets ha0 hF0 R Q hQ hCQ hCI hCW hCR0 hr hr1 hNear
  · exact hGraph floor hf ε hε hSmallG d hd y hy F0 CQ CI CW CF CA CM CR s R Q hQ ha0 hF0 V.neighborhood
end ShrinkingSpheres

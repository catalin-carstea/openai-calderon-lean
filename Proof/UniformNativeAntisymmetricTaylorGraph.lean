import Proof.NativeAntisymmetricTaylorGraph
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap OAI.AnisotropicCalderon.SphereHarmonic

theorem uniform_native_antisymmetric_taylor_graph {Y Ω : Set X}
    (hΩ : IsOpen Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ (F0 : SmoothCoefficientMatrix 2) (CQ CI CW CF CA CM C : ℝ),
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∀ R : RelativeNormalScalarRemainderFamily d y C,∀ Q : SmoothCoefficientJets 2,
      (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) →
      ∀ ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
        ((volume:Measure X).restrict ballOpens),
      (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1) →
      ∀ _V : s.response.SymmetricAdjointDomain,
      let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
        (s.response.adjointTaylor p-s.response.forwardTaylor p)=
        (s.response.antisymmetricTaylorKernel F0 ha0 (R.normalCoefficient Q p)
          (linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ p)) p).comp
            (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)) := by
  obtain ⟨η,hη,hProduce⟩ := uniform_native_radial_adjoint_defect (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy F0 CQ CI CW CF CA CM C s R Q hQ ha0 hF0 V p
  have hDefect := hProduce floor hf ε hε hSmall d hd y hy F0 CQ CI CW CF CA CM C s R Q hQ ha0 hF0 V
  exact s.response.antisymmetricTaylor_graph (by norm_num) F0 hF0 ha0 s.point.flatStrong Q hQ p
    s.response.pointMem (R.normalCoefficient Q p) hDefect
end ShrinkingSpheres

import Proof.UniformNativeNormalScalarFlux
import Proof.NativeFullAdjointScalarCommutator
import Proof.ScalarConjugationDefect
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap OAI.AnisotropicCalderon.SphereHarmonic

theorem uniform_native_radial_adjoint_defect {Y Ω : Set X}
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
      ∀ V : s.response.SymmetricAdjointDomain,
      let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
      let Qn := R.normalCoefficient Q p
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
        (s.response.fullAdjoint p-(s.response.response p+sphereSobolevDegreeL)) =
        (-(closedThreeJetNegativeScalarMultiplierL Qn).inverse.comp
          (s.response.fullAdjointScalarCommutator F0 ha0 Qn p)).comp
            (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)) := by
  obtain ⟨η,hη,hProduce⟩ := uniform_native_normal_scalar_flux (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy F0 CQ CI CW CF CA CM C s R Q hQ ha0 hF0 V p Qn
  obtain ⟨hFlux,hMN⟩ := hProduce floor hf ε hε hSmall d hd y hy F0 CQ CI CW CF CA CM C s R Q hQ
  have hCompat : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (closedThreeJetCoarseScalarMultiplierL Qn)=
      (closedThreeJetNegativeScalarMultiplierL Qn).comp (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)) :=
    ContinuousLinearMap.ext (closedThreeJet_negative_scalar_multiplier_coarse Qn)
  have hComm := s.response.fullAdjoint_closed_scalar_commutator V (by norm_num) F0 ha0 hF0
    s.point.flatStrong Qn p V.pointMem
  exact scalar_conjugation_adjoint_defect _ _ _ _ _ _ _ _ hMN hFlux hCompat hComm
end ShrinkingSpheres

import Proof.UniformNativeNormalScalarFluxNeighborhood
import Proof.SkewNegativeHalfCompatibility
import Proof.NativeAntisymmetricTaylorGraph
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap OAI.AnisotropicCalderon.SphereHarmonic

theorem uniform_native_antisymmetric_taylor_neighborhood {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ (F0 : SmoothCoefficientMatrix 2) (CQ CI CW CF CA CM CR : ℝ),
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∀ R : RelativeNormalScalarRemainderFamily d y CR,∀ Q : SmoothCoefficientJets 2,
      (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) →
      ∀ ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
        ((volume:Measure X).restrict ballOpens),
      (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1) →
      ∀ V : s.response.SymmetricAdjointDomain,
      let KN := fun p => s.response.antisymmetricTaylorKernel F0 ha0 (R.normalCoefficient Q p)
        (linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ p)) p
      ∃ W : Set NormalFrameRelativeParameter,IsOpen W ∧ ((y,frameVectorLinear d.frame y),0) ∈ W ∧ W ⊆ V.domain ∧
        ∀ p ∈ W,
          (closedThreeJetNegativeScalarMultiplierL (R.normalCoefficient Q p)).IsInvertible ∧
          (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
            (s.response.adjointTaylor p-s.response.forwardTaylor p)=
            (KN p).comp (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)) ∧
          (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
            (-(KN p).adjoint : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))=
            (KN p).comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
  obtain ⟨η,hη,hFlux⟩ := uniform_native_normal_scalar_flux_neighborhood hY hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy F0 CQ CI CW CF CA CM CR s R Q hQ ha0 hF0 V KN
  obtain ⟨W,hW,hpW,hWV,hFluxW⟩ := hFlux floor hf ε hε hSmall d hd y hy F0 CQ CI CW CF CA CM CR s R Q hQ V
  refine ⟨W,hW,hpW,hWV,?_⟩
  intro p hp
  have hCompat : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (closedThreeJetCoarseScalarMultiplierL (R.normalCoefficient Q p))=
      (closedThreeJetNegativeScalarMultiplierL (R.normalCoefficient Q p)).comp
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)) :=
    ContinuousLinearMap.ext (closedThreeJet_negative_scalar_multiplier_coarse _)
  have hComm := s.response.fullAdjoint_closed_scalar_commutator V (by norm_num) F0 ha0 hF0 s.point.flatStrong
    (R.normalCoefficient Q p) p (hWV hp)
  have hDefect := scalar_conjugation_adjoint_defect _ _ _ _ _ _ _ _ (hFluxW p hp).2 (hFluxW p hp).1 hCompat hComm
  have hGraph := s.response.antisymmetricTaylor_graph (by norm_num) F0 hF0 ha0 s.point.flatStrong Q hQ p
    (V.sub (hWV hp)) (R.normalCoefficient Q p) hDefect
  refine ⟨(hFluxW p hp).2,hGraph,?_⟩
  apply negative_skew_half_compatible (s.response.adjointTaylor p-s.response.forwardTaylor p) (KN p) _ hGraph
  intro u v
  have hPa : ⟪s.response.adjointTaylor p u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,s.response.forwardTaylor p v⟫_ℝ :=
    (real_inner_comm _ _).trans ((V.taylorPair p (hWV hp) v u).symm.trans (real_inner_comm _ _))
  simp only [_root_.sub_apply,inner_sub_left,inner_sub_right,hPa,V.taylorPair p (hWV hp) u v]
  ring
end ShrinkingSpheres

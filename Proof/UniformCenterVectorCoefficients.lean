import Proof.CompactCenterErrorCoefficient
import Proof.FrameCoordinateCovectors

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

/-- Shared compact scalar representatives of the actual parallel-center error
    in the chosen frame, with uniform angular C1 control. The frame itself is
    arbitrary; only its pointwise coframe norm is used. -/
theorem uniform_center_error_vector_coefficients {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CG : ℝ,0 < η ∧ 0 ≤ CG ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ a : X,
      ∃ F : I → SmoothCoefficientJets 2,
        (∀ j,∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 (F j) =ᶠ[𝓝 z]
          (fun w => metricPair d.γ y
            ((normalizedParallelCenterJacobian d.γ d.expMap y
              (d.radius y • frameVector d.frame y w)-ContinuousLinearMap.id ℝ X) a) (d.frame y j))) ∧
        (∀ j,LocalC1Bound (coefficientValue 2 (F j)) (CG*‖a‖*(d.radius y)^2)) ∧
        ∀ z ∈ Metric.closedBall (0:X) 1,
          (∑ j : I,coefficientValue 2 (F j) z • d.frame y j) =
            (normalizedParallelCenterJacobian d.γ d.expMap y
              (d.radius y • frameVector d.frame y z)-ContinuousLinearMap.id ℝ X) a := by
  obtain ⟨η,CS,hη,hCS,hScalar⟩ := uniform_compact_center_error_coefficient hY hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,CS*(9*|M 0| *K),hη,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd y hy a
  have hCenter := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hCenter
  have hL (j : I) : ‖frameCoordinateLinear d.γ d.frame y j‖ ≤ 9*|M 0| *K :=
    hd.1.1.norm_frameCoordinateLinear_le hK hCenter d.frame hFrame |M 0| (abs_nonneg _)
      (fun i l => (hd.1.reference_entry_bound hCenter i l).trans (le_abs_self _)) j
  have hEach (j : I) := hScalar floor hf ε hε hSmall d hd y hy a (frameCoordinateLinear d.γ d.frame y j)
  choose F hRep hBound using hEach
  refine ⟨F,?_,?_,?_⟩
  · intro j z hz
    simpa only [frameCoordinateLinear_apply] using hRep j z hz
  · intro j z hz
    obtain ⟨hValue,hDerivative⟩ := hBound j z hz
    have hq : CS*‖frameCoordinateLinear d.γ d.frame y j‖*‖a‖*(d.radius y)^2 ≤
        (CS*(9*|M 0| *K))*‖a‖*(d.radius y)^2 := by gcongr;exact hL j
    exact ⟨hValue.trans hq,hDerivative.trans hq⟩
  · intro z hz
    calc
      _ = ∑ j : I,frameCoordinateLinear d.γ d.frame y j
          ((normalizedParallelCenterJacobian d.γ d.expMap y
            (d.radius y • frameVector d.frame y z)-ContinuousLinearMap.id ℝ X) a) • d.frame y j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [(hRep j z hz).eq_of_nhds]
      _ = _ := frameCoordinateLinear_reconstruct d.γ d.frame y _ hFrame

end ShrinkingSpheres

import Proof.PhysicalCenterErrorAdjoint
import Proof.MovingBoundaryAdjunction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

def fixedCenterCoefficient (Q : SmoothCoefficientJets 2) (g : MetricField) (e : Frame)
    (y a : X) (j : I) : SmoothCoefficientJets 2 :=
  constantBoundaryCoefficient Q (frameCoordinateLinear g e y j a)

/-- The leading center-gradient term uses one fixed compact cutoff and the
    actual coframe values. It acts on the same physical Poisson solution. -/
theorem uniform_physical_fixed_center_gradient {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,∃ Q : SmoothCoefficientJets 2,0 < η ∧
      (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ a : X,
      ∀ Fp : SmoothCoefficientMatrix 2,
      (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (Fp i j) =ᶠ[𝓝 x]
        (fun z => principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z i j)) →
      (strongDirichletOperator fixedSobolevCalculus 0 Fp).IsInvertible →
      ∀ D : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ f : SphereSobolev (3/2:ℝ),D (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f) =
        sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
          (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace (strongPoissonL Fp f))) →
      ∀ u : X → ℝ,HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u →
      ∀ f : SphereSobolev (3/2:ℝ),
      (fixedBoundaryValueL f =ᵐ[sphereProbability] fun w : UnitSphere =>
        u (normalChart d.expMap d.frame y (d.radius y) w.val)) →
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
        (boundaryGradientL (fixedCenterCoefficient Q d.γ d.frame y a) D
          (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f)) =ᵐ[sphereProbability]
            fun w : UnitSphere => fderiv ℝ (ballPullback d.expMap d.radius y u) (frameVector d.frame y w.val) a := by
  have hPhysicalTheorem := uniform_physical_strong_poisson_realization (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η,hη,hPhysical⟩ := hPhysicalTheorem
  obtain ⟨Q,hQ⟩ := exists_unit_boundary_coefficient
  refine ⟨η,Q,hη,hQ,?_⟩
  intro floor hf ε hε hSmall d hd y hy a Fp hRep hInv D hD u hu f hBoundary
  have hPHere := hPhysical floor hf ε hε hSmall d hd y hy Fp hRep hInv u hu f hBoundary
  obtain ⟨U,hCompact,hNear,hIdent⟩ := hPHere
  let v := sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f
  have hInput : sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v =
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f :=
    congrArg (fun I : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => I f)
      (sphereSobolevInclusionL_trans (3/2:ℝ) 1 (1/2:ℝ) (by norm_num) (by norm_num))
  have hValue := fixedHalfValueTrace_strongPoisson Fp f
  change OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.nativeHalfTraceL
    sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace
      (TauCeti.Wkp.firstOrder 1 (strongPoissonL Fp f)) = _ at hValue
  have hCoordinate (j : I) : strongCoordinateTraceL fixedSobolevCalculus fixedUnitBallValueTrace j (strongPoissonL Fp f)
      =ᵐ[sphereProbability] fun w : UnitSphere =>
        fderiv ℝ (u ∘ normalChart d.expMap d.frame y (d.radius y)) w.val (axis j) := by
    rw [← hIdent]
    exact strongCoordinateTrace_representative_ae U _ hNear j
  have hValues := boundaryGradientL_value_ae (fixedCenterCoefficient Q d.γ d.frame y a) D
    (strongPoissonL Fp f) v (hValue.trans hInput.symm) (hD f)
      (fun j w => fderiv ℝ (u ∘ normalChart d.expMap d.frame y (d.radius y)) w.val (axis j)) hCoordinate
  filter_upwards [hValues] with w hw
  have hClosed : w.val ∈ Metric.closedBall (0:X) 1 := by
    have hn : ‖w.val‖ = 1 := by simpa [UnitSphere,Metric.sphere,dist_eq_norm] using w.property
    simpa [Metric.mem_closedBall,dist_zero_right,hn]
  have hReconstruct : (∑ j : I,coefficientValue 2 (fixedCenterCoefficient Q d.γ d.frame y a j) w.val • d.frame y j) = a := by
    calc
      _ = ∑ j : I,frameCoordinateLinear d.γ d.frame y j a • d.frame y j := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [fixedCenterCoefficient]
        rw [(constantBoundaryCoefficient_germ Q hQ (frameCoordinateLinear d.γ d.frame y j a) w.val hClosed).eq_of_nhds]
      _ = _ := frameCoordinateLinear_reconstruct d.γ d.frame y a (hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy))
  exact hw.trans (hd.frame_gradient_eq hY hy u hu a w
    (fun j => coefficientValue 2 (fixedCenterCoefficient Q d.γ d.frame y a j) w.val) hReconstruct)

end ShrinkingSpheres

import Proof.UniformActualRadialAdjoint
import Proof.ActualHighRadialEndpoint
import Proof.ActualMidpointRadialEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The actual physical radial response and its physical L2 adjoint admit the
    uniform adjoint Taylor estimate for every admitted radius profile. -/
theorem uniform_physical_radial_adjoint_taylor {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CB CJ : ℝ,0 < η ∧ 0 ≤ CB ∧ 0 ≤ CJ ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ D Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ∃ B : SphereSobolev 0 →L[ℝ] SphereSobolev 0,
        ‖B‖ ≤ CB ∧
        ‖Da-sphereSobolevDegreeL-d.radius y • B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ CJ*(d.radius y)^2 ∧
        (∀ f g,⟪D f,sphereSobolevInclusionL 1 0 (by norm_num) g⟫_ℝ =
          ⟪sphereSobolevInclusionL 1 0 (by norm_num) f,Da g⟫_ℝ) ∧
        ∀ u : X → ℝ,HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u →
        ∀ f : SphereSobolev (3/2:ℝ),
        (fixedBoundaryValueL f =ᵐ[sphereProbability] fun w : UnitSphere =>
          u (normalChart d.expMap d.frame y (d.radius y) w.val)) →
        (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
          (D (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f)) =ᵐ[sphereProbability]
            fun w : UnitSphere => radialTrace d.expMap d.radius y (frameVector d.frame y w.val) u := by
  obtain ⟨ηA,CB,CJ,hηA,hCB,hCJ,hAdjoint⟩ := uniform_actual_midpoint_radial_adjoint_taylor
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηP,CP,hηP,hCP,hPhysical⟩ := uniform_physical_high_radial_endpoint
    (Y:=Y) hY hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηA ηP,CB,CJ,lt_min hηA hηP,hCB,hCJ,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hAHere := hAdjoint floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  obtain ⟨F,D,Da,B,hRep,hInv,hB,hDa,hPair,hD⟩ := hAHere
  have hPHere := hPhysical floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy
  obtain ⟨FP,hRepP,hInvP,hResponse⟩ := hPHere
  have hFG (x : X) (hx : x ∈ (ballOpens:Set X)) : coefficientMatrixField 2 F x = coefficientMatrixField 2 FP x := by
    ext i j
    exact (hRep x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds.trans
      (hRepP x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds.symm
  have hPoisson := strongPoissonL_congr_on_ball F FP hFG
  refine ⟨D,Da,B,hB,hDa,hPair,?_⟩
  intro u hu f hBoundary
  obtain ⟨hActual,hUnused⟩ := hResponse u hu f hBoundary
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  have hPf := congrArg (fun P : SphereSobolev (3/2:ℝ) →L[ℝ] BallSobolev 2 => P f) hPoisson
  have hRad := congrArg (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace) hPf
  have hEq : Z.symm (D (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f)) =
      outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace (strongPoissonL FP f) :=
    (congrArg Z.symm (hD f)).trans ((Z.symm_apply_apply _).trans hRad)
  exact hEq.symm ▸ hActual

end ShrinkingSpheres

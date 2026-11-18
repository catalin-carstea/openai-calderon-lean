import Proof.ActualSmoothRadialPair
import Proof.ActualSmoothRadialTaylor
import Proof.UniformActualRadialAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier

/-- Smooth actual forward/adjoint quadratic radial remainders, with uniform
    pointwise bounds and one canonical first correction. This asserts no
    uniform parameter derivative bound. -/
theorem uniform_actual_smooth_radial_taylor_pair {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CB CJ : ℝ,0 < η ∧ 0 ≤ CB ∧ 0 ≤ CJ ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∃ J Ja : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ContDiffOn ℝ ∞ J Y ∧ ContDiffOn ℝ ∞ Ja Y ∧ ∀ y ∈ Y,
        let B := firstRadialCorrectionL d y
        let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
        let R := J y+d.radius y • B.comp I0
        let Da := sphereSobolevDegreeL+d.radius y • B.adjoint.comp I0+Ja y
        ‖B‖ ≤ CB ∧ ‖J y‖ ≤ CJ*(d.radius y)^2 ∧ ‖Ja y‖ ≤ CJ*(d.radius y)^2 ∧
          RealizesActualMidpointRadialError d y R ∧ ∀ u v,
            ⟪(R+sphereSobolevDegreeL) u,I0 v⟫_ℝ = ⟪I0 u,Da v⟫_ℝ := by
  have hPairTheorem := uniform_actual_smooth_radial_pair hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηP,hηP,hProduce⟩ := hPairTheorem
  have hForwardTheorem := uniform_actual_midpoint_radial_taylor_canonical (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηF,CBF,CJF,hηF,hCBF,hCJF,hForward⟩ := hForwardTheorem
  have hAdjointTheorem := uniform_actual_midpoint_radial_adjoint_canonical (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηA,CBA,CJA,hηA,hCBA,hCJA,hAdjoint⟩ := hAdjointTheorem
  let CJ := max CJF CJA
  refine ⟨min ηP (min ηF ηA),max CBF CBA,CJ,lt_min hηP (lt_min hηF hηA),
    hCBF.trans (le_max_left _ _),hCJF.trans (le_max_left _ _),?_⟩
  intro floor hf ε hε hSmall d hd
  have hSmallP := hSmall.trans (min_le_left _ _)
  have hSmallF := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallA := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨R,A,hR,hA,hActual⟩ := hProduce floor hf ε hε hSmallP d hd
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let J := fun y => R y-d.radius y • (firstRadialCorrectionL d y).comp I0
  let Ja := fun y => A y-sphereSobolevDegreeL-d.radius y • (firstRadialCorrectionL d y).adjoint.comp I0
  have hB := (hd.1.firstRadialCorrectionL_smooth hΩ (zero_lt_one.trans_le hK)).mono
    (fun y hy => hd.2.1.center_mem hy)
  have hBa : ContDiffOn ℝ ∞ (fun y => (firstRadialCorrectionL d y).adjoint) Y :=
    (realHilbertOperatorAdjointL (SphereSobolev 0)).contDiff.comp_contDiffOn hB
  have hJ : ContDiffOn ℝ ∞ J Y := hR.sub (hd.2.2.2.2.1.1.smul (hB.clm_comp contDiffOn_const))
  have hJa : ContDiffOn ℝ ∞ Ja Y := (hA.sub contDiffOn_const).sub
    (hd.2.2.2.2.1.1.smul (hBa.clm_comp contDiffOn_const))
  refine ⟨J,Ja,hJ,hJa,?_⟩
  intro y hy
  dsimp only
  have hJDef : J y+d.radius y • (firstRadialCorrectionL d y).comp I0 = R y := sub_add_cancel _ _
  have hJaDef : sphereSobolevDegreeL+d.radius y • (firstRadialCorrectionL d y).adjoint.comp I0+Ja y = A y := by
    dsimp only [Ja]
    abel
  have hFHere := hForward floor hf ε hε hSmallF d hd y hy
  dsimp only at hFHere
  obtain ⟨F,J0,hRep,hInv,hBNorm,hJNorm,hRestriction⟩ := hFHere
  have hF (z : X) (hz : z ∈ (ballOpens : Set X)) : coefficientMatrixField 2 F z =
      principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z := by
    ext i j
    exact (hRep z (unitBall_subset_closedBall_two hz) i j).eq_of_nhds
  have hJ0 := realizesActualMidpointRadialError_of_restriction d y
    (J0+d.radius y • (firstRadialCorrectionL d y).comp I0) F hF hRestriction
  have hREq := ((hActual y hy).1).unique d y (R y)
    (J0+d.radius y • (firstRadialCorrectionL d y).comp I0) hJ0 F hF
  have hJEq : J y = J0 := by
    dsimp only [J]
    rw [hREq]
    abel
  have hAHere := hAdjoint floor hf ε hε hSmallA d hd y hy
  dsimp only at hAHere
  obtain ⟨G,D,Da,hRepG,hInvG,hBAG,hDa,hPair,hHigh⟩ := hAHere
  have hG (z : X) (hz : z ∈ (ballOpens : Set X)) : coefficientMatrixField 2 G z =
      principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z := by
    ext i j
    exact (hRepG z (unitBall_subset_closedBall_two hz) i j).eq_of_nhds
  have hDEq : R y+sphereSobolevDegreeL = D := by
    apply continuousLinearMap_eq_of_high_restriction
    intro f
    exact (((hActual y hy).1).full_high d y (R y) G hG f).trans (hHigh f).symm
  have hAPair : ∀ u v,⟪D u,I0 v⟫_ℝ = ⟪I0 u,A y v⟫_ℝ := by
    intro u v
    rw [← hDEq]
    exact (hActual y hy).2 u v
  have hAEq := radial_physical_adjoint_unique D (A y) Da hAPair hPair
  refine ⟨hBNorm.trans (le_max_left _ _),?_,?_,?_,?_⟩
  · rw [hJEq]
    exact hJNorm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  · dsimp only [Ja]
    rw [hAEq]
    exact hDa.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
  · rw [hJDef]
    exact (hActual y hy).1
  · intro u v
    have hLeft := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
      ⟪(T+sphereSobolevDegreeL) u,I0 v⟫_ℝ) hJDef
    have hRight := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
      ⟪I0 u,T v⟫_ℝ) hJaDef
    exact hLeft.trans (((hActual y hy).2 u v).trans hRight.symm)

end ShrinkingSpheres

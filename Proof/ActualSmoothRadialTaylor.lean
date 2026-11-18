import Proof.ActualSmoothMidpointRadialFamily
import Proof.QuadraticMidpointRadial
import Proof.CanonicalFirstRadialFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

/-- A genuine smooth quadratic radial remainder with the canonical first
    correction. The norm constant is uniform over the admitted class. -/
theorem uniform_actual_smooth_radial_taylor {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CB CJ : ℝ,0 < η ∧ 0 ≤ CB ∧ 0 ≤ CJ ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∃ J : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,ContDiffOn ℝ ∞ J Y ∧
        ∀ y ∈ Y,‖firstRadialCorrectionL d y‖ ≤ CB ∧ ‖J y‖ ≤ CJ*(d.radius y)^2 ∧
          RealizesActualMidpointRadialError d y
            (J y+d.radius y • (firstRadialCorrectionL d y).comp (sphereSobolevInclusionL 1 0 (by norm_num))) := by
  obtain ⟨ηS,hηS,hSmooth⟩ := uniform_actual_smooth_midpoint_radial_family hY hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηT,CB,CJ,hηT,hCB,hCJ,hTaylor⟩ :=
    uniform_actual_midpoint_radial_taylor_canonical (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηS ηT,CB,CJ,lt_min hηS hηT,hCB,hCJ,?_⟩
  intro floor hf ε hε hSmall d hd
  obtain ⟨R,hR,hRealizes⟩ := hSmooth floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd
  let J : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0 := fun y =>
    R y-d.radius y • (firstRadialCorrectionL d y).comp (sphereSobolevInclusionL 1 0 (by norm_num))
  have hB := (hd.1.firstRadialCorrectionL_smooth hΩ (zero_lt_one.trans_le hK)).mono
    (fun y hy => hd.2.1.center_mem hy)
  have hJ : ContDiffOn ℝ ∞ J Y := hR.sub (hd.2.2.2.2.1.1.smul (hB.clm_comp contDiffOn_const))
  refine ⟨J,hJ,?_⟩
  intro y hy
  have hHere := hTaylor floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy
  dsimp only at hHere
  obtain ⟨F,J0,hRep,hInv,hBNorm,hJNorm,hRestriction⟩ := hHere
  have hF (z : X) (hz : z ∈ (ballOpens : Set X)) : coefficientMatrixField 2 F z =
      principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z := by
    ext i j
    exact (hRep z (unitBall_subset_closedBall_two hz) i j).eq_of_nhds
  have hJ0 := realizesActualMidpointRadialError_of_restriction d y
    (J0+d.radius y • (firstRadialCorrectionL d y).comp (sphereSobolevInclusionL 1 0 (by norm_num)))
      F hF hRestriction
  have hEq := (hRealizes y hy).unique d y (R y)
    (J0+d.radius y • (firstRadialCorrectionL d y).comp (sphereSobolevInclusionL 1 0 (by norm_num))) hJ0 F hF
  have hJEq : J y = J0 := by
    dsimp only [J]
    rw [hEq]
    abel
  refine ⟨hBNorm,?_,?_⟩
  · rw [hJEq]
    exact hJNorm
  · rw [hJEq]
    exact hJ0

end ShrinkingSpheres

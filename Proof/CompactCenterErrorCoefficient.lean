import Proof.UniformCenterAngularDerivative
import Proof.Archive.FiniteDimensionalLocalSmoothExtension
import Proof.BoundaryGradientAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

def scalarEndomorphismL (L : X →L[ℝ] ℝ) (a : X) : (X →L[ℝ] X) →L[ℝ] ℝ :=
  L.comp (ContinuousLinearMap.apply ℝ X a)

lemma norm_scalarEndomorphismL_le (L : X →L[ℝ] ℝ) (a : X) :
    ‖scalarEndomorphismL L a‖ ≤ ‖L‖*‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro T
  calc
    _ ≤ ‖L‖*‖T a‖ := L.le_opNorm _
    _ ≤ ‖L‖*(‖T‖*‖a‖) := mul_le_mul_of_nonneg_left (T.le_opNorm a) (norm_nonneg L)
    _ = _ := by ring

/-- Compact scalar jets for the actual Jacobi center error. The arbitrary
    exterior extension is qualitative; its H1 multiplier bound uses only the
    actual value and first derivative on the unit ball. -/
theorem uniform_compact_center_error_coefficient {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CG : ℝ,0 < η ∧ 0 ≤ CG ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ a : X,∀ L : X →L[ℝ] ℝ,
      ∃ F : SmoothCoefficientJets 2,
        (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 F =ᶠ[𝓝 z]
          (fun w => L ((normalizedParallelCenterJacobian d.γ d.expMap y
            (d.radius y • frameVector d.frame y w)-ContinuousLinearMap.id ℝ X) a))) ∧
        LocalC1Bound (coefficientValue 2 F) (CG*‖L‖*‖a‖*(d.radius y)^2) := by
  obtain ⟨ηA,CG,hηA,hCG,hAngular⟩ := uniform_normal_parallel_center_angular_C1 hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηG,hηG,hControl⟩ := uniform_normal_control_on_disk (Y:=Y) hΩ
    (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨min ηA ηG,CG,lt_min hηA hηG,hCG,?_⟩
  intro floor hf ε hε hSmall d hd y hy a L
  let G : X → X →L[ℝ] X := fun w => normalizedParallelCenterJacobian d.γ d.expMap y
    (d.radius y • frameVector d.frame y w)
  let A := scalarEndomorphismL L a
  let f : X → ℝ := fun w => A (G w-ContinuousLinearMap.id ℝ X)
  have hCenter := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hCenter
  have hG (z : X) (hz : z ∈ Metric.ball (0:X) 2) : ContDiffAt ℝ ∞ G z := by
    have hw := frameVector_mem_disk d.γ d.frame y z 2 hFrame (Metric.ball_subset_closedBall hz)
    have hPack := hControl floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy
      (frameVector d.frame y z) hw
    have hPoint := hd.2.1.contDiffAt_normalizedParallelCenterJacobian hy
      (d.radius y • frameVector d.frame y z) (interior_subset hPack.1.1)
    exact hPoint.comp z ((contDiff_frameVector_fixed d.frame y).contDiffAt.const_smul (d.radius y))
  have hSmooth : ContDiffOn ℝ ∞ f (Metric.ball (0:X) 2) := by
    intro z hz
    exact (A.contDiff.contDiffAt.comp z ((hG z hz).sub contDiffAt_const)).contDiffWithinAt
  have h12 : Metric.closedBall (0:X) 1 ⊆ Metric.ball (0:X) 2 := by
    intro z hz
    change dist z 0 < 2
    change dist z 0 ≤ 1 at hz
    linarith
  obtain ⟨fhat,hfhat,hCompact,hNear⟩ := exists_contDiff_eq_near_compact_of_contDiffOn
    (Metric.closedBall (0:X) 1) (Metric.ball (0:X) 2) (isCompact_closedBall _ _)
    Metric.isOpen_ball h12 f hSmooth
  let F := compactCoefficient 2 fhat hfhat hCompact
  have hF : coefficientValue 2 F = fhat := coefficientValue_compactCoefficient 2 _ _ _
  refine ⟨F,?_,?_⟩
  · intro z hz
    rw [hF]
    exact hNear z hz
  · intro z hz
    have hzClosed : z ∈ Metric.closedBall (0:X) 1 := Metric.ball_subset_closedBall hz
    have hAHere := hAngular floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy z hzClosed
    obtain ⟨hValue,hDerivative⟩ := hAHere
    have hActual := hG z (h12 hzClosed)
    have hOuter : HasFDerivAt G (fderiv ℝ G z) z := (hActual.differentiableAt (by simp)).hasFDerivAt
    have hDifference : HasFDerivAt (fun w => G w-ContinuousLinearMap.id ℝ X) (fderiv ℝ G z) z := by
      change HasFDerivAt (G-fun _ => ContinuousLinearMap.id ℝ X) (fderiv ℝ G z) z
      exact (hOuter.sub (hasFDerivAt_const (𝕜:=ℝ) (ContinuousLinearMap.id ℝ X) z)).congr_fderiv (sub_zero _)
    have hDf : fderiv ℝ f z = A.comp (fderiv ℝ G z) :=
      (A.hasFDerivAt.comp z hDifference).fderiv
    have hBoundValue : |f z| ≤ CG*‖L‖*‖a‖*(d.radius y)^2 := by
      calc
        _ ≤ ‖A‖*‖G z-ContinuousLinearMap.id ℝ X‖ := A.le_opNorm _
        _ ≤ (‖L‖*‖a‖)*(CG*(d.radius y)^2) :=
          mul_le_mul (norm_scalarEndomorphismL_le L a) hValue (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hBoundDerivative : ‖fderiv ℝ f z‖ ≤ CG*‖L‖*‖a‖*(d.radius y)^2 := by
      rw [hDf]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul (norm_scalarEndomorphismL_le L a) hDerivative (norm_nonneg _) (by positivity)).trans_eq (by ring))
    have hEq := hNear z hzClosed
    rw [hF,hEq.eq_of_nhds,hEq.fderiv_eq]
    exact ⟨hBoundValue,hBoundDerivative⟩

end ShrinkingSpheres

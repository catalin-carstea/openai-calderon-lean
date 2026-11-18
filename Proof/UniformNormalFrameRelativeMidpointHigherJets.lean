import Proof.NormalFrameRelativeMidpointHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Actual midpoint Taylor remainders have every prescribed uniform joint
    center/frame/relative-radius jet, from background metric budgets alone. -/
theorem uniform_normalFrameRelative_midpoint_higher_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (N : ℕ) (hNm : N+5 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C CA CI CW : ℝ,∃ F0 : SmoothCoefficientMatrix 2,
      0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ 1 ≤ CA ∧ 0 ≤ CI ∧ 0 ≤ CW ∧
      (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
        (frameVectorLinear d.frame y) (d.radius y) (N+1) 2 CA,
      NormalFrameRelativeNativePointData q F0 CI CW ∧
      ∃ V : Set NormalFrameRelativeParameter,IsOpen V ∧ ((y,frameVectorLinear d.frame y),0) ∈ V ∧ V ⊆ q.domain ∧
        ∃ R : NormalFrameRelativeParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
          ContDiffOn ℝ ∞ R V ∧
          (∀ p ∈ V,(R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
            (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
              (actualHighRadialErrorL (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p))) ∧
          let T := fun p => R p-d.radius y •
            (coarseFirstRadialVariationL 1 (normalFrameRelativeFirstCovector d.γ d.g₁ p)).comp
              (sphereSobolevInclusionL 1 0 (by norm_num))
          ContDiffAt ℝ ∞ T ((y,frameVectorLinear d.frame y),0) ∧ ∀ n : ℕ,n ≤ N →
            ‖iteratedFDeriv ℝ n T ((y,frameVectorLinear d.frame y),0)‖ ≤ C*(d.radius y)^2 := by
  obtain ⟨ηG,CA,hηG,hηG1,hCA,hFamily⟩ := uniform_normalFrameRelativeCoefficient_jet_family
    hY hΩ (N+1) (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨ηP,CI,CW,F0,hηP,hηP1,hCI,hCW,hF0,hPoint⟩ :=
    uniform_normalFrameRelative_native_point_data (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ
  let C0 := normalFrameRelativeMidpointJetBudget N CI CW CA
  have hC0 : 0 ≤ C0 := by dsimp only [C0,normalFrameRelativeMidpointJetBudget];positivity
  have hC : 1 ≤ 1+C0 := by linarith only [hC0]
  refine ⟨min ηG ηP,1+C0,CA,CI,CW,F0,lt_min hηG hηP,(min_le_left _ _).trans hηG1,
    hC,hCA,hCI,hCW,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  let L := frameVectorLinear d.frame y
  have he (i j : I) : metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0 := by
    simpa only [L,frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy) i j
  have hr : 0 < d.radius y := (hd.2.2.2.2.1.2 y hy).1
  have hrε : d.radius y ≤ ε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : d.radius y ≤ 1 := hrε.trans (hSmall.trans ((min_le_left _ _).trans hηG1))
  have hrAbs : |d.radius y| ≤ d.radius y := by rw [abs_of_nonneg hr.le]
  obtain ⟨q⟩ := hFamily floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy L he (d.radius y) hrAbs
  have t : NormalFrameRelativeNativePointData q F0 CI CW :=
    hPoint floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy (N+1) 2 CA le_rfl q
  obtain ⟨V,hV,hpV,hSub,R,hR,hRestrict,hSmooth,hJets⟩ := q.native_midpoint_higher_jets N le_rfl
    (zero_le_one.trans hCA) hCI hCW hr.le hr1 F0 hF0 t
  refine ⟨q,t,V,hV,hpV,hSub,R,hR,hRestrict,hSmooth,?_⟩
  intro n hn
  exact (hJets n hn).trans (mul_le_mul_of_nonneg_right (by change C0 ≤ 1+C0;linarith) (sq_nonneg (d.radius y)))

end ShrinkingSpheres

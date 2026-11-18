import Proof.NormalizedStrongInverseBound
import Proof.UniformFirstStrongTaylorData
import Proof.NormalizedFirstCoefficientTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- Uniform normalized point inverse and local affine Taylor data transfer to
    EVERY compact representative of the same actual coefficient and first model. -/
theorem uniform_normalized_strong_taylor_point_data {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C P Q : ℝ,∃ F0 : SmoothCoefficientMatrix 2,0 < η ∧ 0 ≤ C ∧ 0 ≤ P ∧ 0 ≤ Q ∧
      (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ F F1 : SmoothCoefficientMatrix 2,
      (∀ z ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F i j) =ᶠ[𝓝 z]
        (fun w => normalizedFirstNormalCoefficient d y w i j)) →
      (∀ z ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) =ᶠ[𝓝 z]
        (fun w => firstDensityLogCovector d y w*(1:Mat) i j)) →
      (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
      ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖ ≤ C ∧
      (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible ∧
      ‖(strongDirichletOperator fixedSobolevCalculus 0 F0).inverse‖ ≤ C ∧
      (∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 (F1 i j) z| ≤ P) ∧
      (∀ i j,∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F1 i j)) z‖ ≤ P) ∧
      (∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 ((F-F0-d.radius y • F1) i j) z| ≤ Q*(d.radius y)^2) ∧
      (∀ i j,∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 ((F-F0-d.radius y • F1) i j)) z‖ ≤ Q*(d.radius y)^2) := by
  obtain ⟨ηI,CI,PI,QI,F0,hηI,hCI,hPI,hQI,hF0,hSource⟩ :=
    uniform_first_strong_taylor_data (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηT,Q,hηT,hQ,hTaylor⟩ := uniform_normalized_first_coefficient_taylor (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  let P := K^2*|M ⟨1,by omega⟩|
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hP : 0 ≤ P := by dsimp [P];positivity
  refine ⟨min ηI ηT,K*CI,P,Q,F0,lt_min hηI hηT,mul_nonneg hKpos.le hCI,hP,hQ,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy F F1 hRep hRep1
  let c := firstMetricDensityFactor d.γ d.g₁ y
  have hc : 0 < c := firstMetricDensityFactor_pos _ _ _
  have hcK : c ≤ K := hd.1.firstMetricDensityFactor_le hKpos (hd.2.1.center_mem hy)
  obtain ⟨G,G1,hGRep,hGRep1,hGInv,hGINorm,hG0Inv,hG0Norm,hValG1,hDerG1,hValGR,hDerGR⟩ :=
    hSource floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  have hGF (z : X) (hz : z ∈ Metric.closedBall (0:X) 2) :
      coefficientMatrixField 2 G z = principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z := by
    ext i j;exact (hGRep z hz i j).eq_of_nhds
  have hFF (z : X) (hz : z ∈ Metric.closedBall (0:X) 2) : coefficientMatrixField 2 F z = normalizedFirstNormalCoefficient d y z := by
    ext i j;exact (hRep z hz i j).eq_of_nhds
  have hNormF := strong_inverse_normalized_coefficient_bound F G c K CI hc hKpos.le hCI hcK hGInv hGINorm (fun z hz => by
    rw [hFF z (unitBall_subset_closedBall_two hz),hGF z (unitBall_subset_closedBall_two hz)];rfl)
  have hNorm0 := strong_inverse_normalized_coefficient_bound F0 (c • F0) c K CI hc hKpos.le hCI hcK hG0Inv hG0Norm (fun z _ => by
    rw [coefficientMatrixField_smul,smul_smul,inv_mul_cancel₀ hc.ne',one_smul])
  have hCov := hd.1.norm_firstDensityLogCovector_le hΩ hK (by omega) (hd.2.1.center_mem hy)
  obtain ⟨hVal1,hDer1⟩ := linear_scalar_coefficient_local_bounds F1 (firstDensityLogCovector d y) P hP hCov hRep1
  have hAD (i j : I) (z : X) (hz : z ∈ (ballOpens:Set X)) :
      DifferentiableAt ℝ (fun w => normalizedFirstNormalCoefficient d y w i j) z :=
    ((contDiff_coefficientValue 2 (F i j)).differentiable (by simp) z).congr_of_eventuallyEq
      (hRep z (unitBall_subset_closedBall_two hz) i j).symm
  have hT (z : X) (hz : z ∈ (ballOpens:Set X)) (i j : I) :=
    hTaylor floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy z (unitBall_subset_closedBall_two hz) i j
  have hResidual := coefficient_affine_remainder_local_bounds F F0 F1 1 (d.radius y) Q (firstDensityLogCovector d y)
    hRep hF0 hRep1 hAD hT
  refine ⟨hNormF.1,hNormF.2,hNorm0.1,hNorm0.2,hVal1,hDer1,?_,?_⟩
  · simpa only [one_smul] using hResidual.1
  · simpa only [one_smul] using hResidual.2

end ShrinkingSpheres

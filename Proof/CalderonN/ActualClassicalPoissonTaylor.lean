module

public import Proof.CalderonN.NormalizedStrongPoissonTaylor
public import Proof.CalderonN.NativeCoefficientBallPoisson

import Proof.CalderonN.GreenSourceCutoff
import Proof.CalderonN.ClassicalBallDirichlet
import Mathlib.Tactic

public section

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option maxHeartbeats 3100000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem fullBallDivergenceL_flat_smooth
    (F0 : SmoothCoefficientMatrix dim 2)
    (hF0 : ∀ z ∈ closedBall (0 : X dim) 2, coefficientMatrixField 2 F0 z = 1)
    (u : SmoothData dim)
    (hu : EqOn (laplace (fun _ => (1 : Mat dim)) u.1) 0 (ball (0 : X dim) 1)) :
    fullBallDivergenceL 0 F0 (smoothBallSobolev 2 u) = 0 := by
  let a := coefficientMatrixField 2 F0
  obtain ⟨hSmooth,hOp⟩ := fullBallDivergence_native_smooth 0 F0 u
  change fullBallDivergenceL 0 F0 (smoothBallSobolev 2 u) =
    smoothBallSobolev 0 ⟨negativeBallDivergence a u.1,hSmooth⟩ at hOp
  rw [hOp]
  have hMetric : SmoothMetric univ (fun _ : X dim => (1 : Mat dim)) :=
    ⟨fun _ _ => contDiffOn_const,fun _ _ => Matrix.PosDef.one⟩
  have hZero (z : X dim) (hz : z ∈ ball (0 : X dim) 1) : negativeBallDivergence a u.1 z = 0 := by
    have hz₂ : z ∈ ball (0 : X dim) 2 := ball_subset_ball (by norm_num) hz
    have hEq : a =ᶠ[𝓝 z] (fun _ : X dim => (1 : Mat dim)) := by
      filter_upwards [isOpen_ball.mem_nhds hz₂] with x hx
      exact hF0 x (ball_subset_closedBall hx)
    rw [negativeBallDivergence_congr_germ hEq (EventuallyEq.rfl (f := u.1))]
    have hdg : ∀ x ∈ (univ : Set (X dim)), ∀ i j,
        (fun _ : X dim => (1 : Mat dim)) x i j =
        divergenceCoeff (fun _ : X dim => (1 : Mat dim)) x i j := by
      intro x hx i j
      simp [divergenceCoeff,chartVolume]
    rw [negativeBallDivergence_eq_neg_laplace isOpen_univ hMetric hdg u.2.contDiffOn (mem_univ z)]
    simp [hu hz]
  apply TauCeti.Wkp.ext 0
  simp only [← TauCeti.Wkp.valueL_apply,map_zero]
  apply Lp.ext
  have hvol := ae_restrict_mem (μ := (volume : Measure (X dim)))
    (show MeasurableSet (fixedBallOpens dim : Set (X dim)) from (fixedBallOpens dim).isOpen.measurableSet)
  filter_upwards [value_smoothBallSobolev_ae 0 ⟨negativeBallDivergence a u.1,hSmooth⟩,
    Lp.coeFn_zero ℝ 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim)),hvol] with x hx hx₀ hBall
  rw [TauCeti.Wkp.valueL_apply,hx,hx₀,Pi.zero_apply]
  exact hZero x hBall

/-- The uniform bulk expansion applies to the actual smooth harmonic
replacement of a flat harmonic boundary lift. Both terms use the same
physical ball and the same affine coefficient. -/
theorem uniform_actual_classical_normalizedPoisson_taylor (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ F0 : SmoothCoefficientMatrix dim 2,
      (∀ z ∈ closedBall (0 : X dim) 2, coefficientMatrixField 2 F0 z = 1) ∧
      ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ F1 : SmoothCoefficientMatrix dim 2,
        EqOn (coefficientMatrixField 2 F1) (fun z => firstDensityCenterLinear d y z • (1 : Mat dim))
          (ball (0 : X dim) (5/4)) ∧
        ∀ u : SmoothData dim,
          EqOn (laplace (fun _ => (1 : Mat dim)) u.1) 0 (ball (0 : X dim) 1) →
          ∃ b : X dim → ℝ, ∃ hb : ContDiff ℝ ∞ b,
            EqOn b u.1 (standardSphere dim) ∧
            EqOn (negativeBallDivergence (fun z =>
              firstNormalVelocityCoefficient d y (d.radius y • frameVector d.frame y z)) b)
              0 (ball (0 : X dim) 1) ∧
            let U := smoothBallSobolev 2 u
            let j := (strongDirichletSubmodule dim 0).toSubmodule.subtypeL
            let I₀ := (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse
            let U1 := -j (I₀ (fullBallDivergenceL 0 F1 U))
            ‖smoothBallSobolev 2 ⟨b,hb⟩-U-(d.radius y) • U1‖ ≤ B*‖U‖*(d.radius y)^2 := by
  obtain ⟨F0,hF0,η,B,hη,hB,hP⟩ :=
    uniform_normalized_fixedBall_poisson_first_variation (Y := Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨F0,hF0,η,B,hη,hB,?_⟩
  intro floor hf ε hε hεη d hd y hy
  obtain ⟨F,F1,hF,hF1,⟨lo,hi,hEll⟩,hT⟩ := hP floor hf ε hε hεη d hd y hy
  refine ⟨F1,hF1,?_⟩
  intro u hu
  obtain ⟨b,hb,hbT,hbL,hbRep⟩ := exists_native_classicalBallPoisson 0 F hEll u
  have hEq (z : X dim) (hz : z ∈ ball (0 : X dim) 1) :
      (coefficientMatrixField 2 F) =ᶠ[𝓝 z]
        (fun w => firstNormalVelocityCoefficient d y (d.radius y • frameVector d.frame y w)) := by
    filter_upwards [isOpen_ball.mem_nhds (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 5/4) hz)]
      with w hw using hF hw
  refine ⟨b,hb,hbT,fun z hz => ?_,?_⟩
  · rw [← negativeBallDivergence_congr_germ (hEq z hz) (EventuallyEq.rfl (f := b))]
    exact hbL hz
  let U := smoothBallSobolev 2 u
  let P0 := ContinuousLinearMap.toSpanSingleton ℝ U
  have hFlat : (fullBallDivergenceL 0 F0).comp P0 = 0 := by
    apply ContinuousLinearMap.ext
    intro t
    simp only [P0,ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,map_smul,zero_apply]
    rw [fullBallDivergenceL_flat_smooth F0 hF0 u hu,smul_zero]
  let j := (strongDirichletSubmodule dim 0).toSubmodule.subtypeL
  let I₀ := (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse
  let W := (ballPoissonOperatorL 0 F).comp P0 - P0 -
    d.radius y • (-(j.comp (I₀.comp ((fullBallDivergenceL 0 F1).comp P0))))
  have hOp : ‖W‖ ≤ B*‖P0‖*(d.radius y)^2 := hT ℝ P0 hFlat
  have hW : W 1 = ballPoissonOperatorL 0 F U - U -
      d.radius y • (-j (I₀ (fullBallDivergenceL 0 F1 U))) := by
    change ballPoissonOperatorL 0 F ((1 : ℝ) • U) - (1 : ℝ) • U -
      d.radius y • (-j (I₀ (fullBallDivergenceL 0 F1 ((1 : ℝ) • U)))) = _
    rw [one_smul]
  have h := (W.le_opNorm (1 : ℝ)).trans
    (mul_le_mul_of_nonneg_right hOp (norm_nonneg (1 : ℝ)))
  have hbRep' : ballPoissonOperatorL 0 F U = smoothBallSobolev 2 ⟨b,hb⟩ := hbRep
  rwa [hW,hbRep',norm_one,mul_one,show ‖P0‖ = ‖U‖ from
    ContinuousLinearMap.norm_toSpanSingleton U] at h

end CalderonN

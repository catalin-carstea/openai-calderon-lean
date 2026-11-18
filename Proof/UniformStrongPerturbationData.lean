import Proof.CoefficientOperatorLocality
import Proof.UniformActualCoefficientPerturbation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- One common representative carries the actual coefficient germ, the strong
    inverse and the local flat perturbation bounds used by the Poisson caller. -/
def StrongFlatCoefficientData (a : X → Mat) (F0 : SmoothCoefficientMatrix 2) (C q : ℝ) : Prop :=
  ∃ F : SmoothCoefficientMatrix 2,∃ c : ℝ,0 < c ∧
    (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,
      coefficientValue 2 (F i j) =ᶠ[𝓝 x] (fun z => a z i j)) ∧
    (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
    ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖ ≤ C ∧
    (∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 ((F-c • F0) i j) x| ≤ q) ∧
    (∀ i j,∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 ((F-c • F0) i j)) x‖ ≤ q)

theorem uniform_actual_strong_flat_data {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C Q : ℝ,∃ F0 : SmoothCoefficientMatrix 2,0 < η ∧ 0 ≤ C ∧ 0 ≤ Q ∧
      (∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      StrongFlatCoefficientData
        (principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))) F0 C (Q*d.radius y) := by
  obtain ⟨ηI,C,hηI,hC,hI⟩ := uniform_actual_strong_dirichlet_inverse
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηP,Q,F0,hηP,hQ,hF0,hP⟩ := uniform_actual_local_flat_comparison
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,hηE,hE⟩ := uniform_enlarged_framed_normal_elliptic
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨min ηI (min ηP ηE),C,Q,F0,lt_min hηI (lt_min hηP hηE),hC,hQ,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hSI := hSmall.trans (min_le_left _ _)
  have hSP := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSE := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨FI,hRepI,hInvI⟩ := hI floor hf ε hε hSI d hd y hy
  obtain ⟨F,c,hc,hRep,hValue,hDerivative⟩ := hP floor hf ε hε hSP d hd y hy
  let H := framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)
  have hPoint (x : X) (hx : x ∈ (ballOpens : Set X)) :
      coefficientMatrixField 2 F x = principalCoefficient H x := by
    ext i j
    exact (hRep x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds
  have hPointI (x : X) (hx : x ∈ (ballOpens : Set X)) :
      coefficientMatrixField 2 FI x = principalCoefficient H x := by
    ext i j
    exact (hRepI x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds
  have hEq := strongDirichletOperator_congr_on_ball fixedSobolevCalculus 0 F FI
    (fun x hx => (hPoint x hx).trans (hPointI x hx).symm)
  have hInv : ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖ ≤ C := by
    rw [hEq]
    exact hInvI
  have hEll : Elliptic (Metric.closedBall (0:X) 2) (4*K^2) H :=
    hE floor hf ε hε hSE d hd y hy d.g₁ (by simp)
  have hKP : 1 ≤ 4*K^2 := by nlinarith only [hK,sq_nonneg (K-1)]
  have hUE0 := (hEll.principalCoefficient_tau hKP).mono_set unitBall_subset_closedBall_two
  have hUE := hUE0.congr hPoint
  have hInvertible := strongDirichletOperator_isInvertible_of_elliptic
    fixedSobolevCalculus fixedDirichletRegularity 0 F hUE
  exact ⟨F,c,hc,hRep,hInvertible,hInv,hValue,hDerivative⟩

end ShrinkingSpheres

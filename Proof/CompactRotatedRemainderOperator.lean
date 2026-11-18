import Proof.AngleLowJetDerivative
import Proof.UniformCoefficientRotationRemainder
import Proof.LocalCommonSupportCoefficientFamily
import Proof.Archive.TauCutoff

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Function
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SmoothSphereRotation

/-- A compact smooth representative of a true local coefficient remainder
    gives actual whole-angle strong/full operator families. The derivative
    constants use only its true local rotation generator and first spatial jet. -/
theorem exists_rotated_remainder_operator_family
    (R B : X → Mat) (hB : ContDiff ℝ ∞ B) (hCompact : HasCompactSupport B)
    (hRep : ∀ z ∈ Metric.closedBall (0:X) 2,B =ᶠ[𝓝 z] R)
    (i j : I) (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ z ∈ (ballOpens:Set X),‖rotationPrincipalCoefficientDerivative i j R z‖ ≤ q)
    (hSpatial : ∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (rotationPrincipalCoefficientDerivative i j R) z‖ ≤ q) :
    ∃ a : ℝ × X → Mat,∃ ha : ContDiff ℝ ∞ a,∃ S : Set X,∃ hS : IsCompact S,
      ∃ hz : ∀ θ z,z ∉ S → a (θ,z) = 0,
      (∀ θ z,z ∈ Metric.closedBall (0:X) 2 → a (θ,z) = coordinateRotationPrincipalFamily i j
        (fun v : ℝ × X => R v.2) ((θ,0),z)) ∧
      ‖fderiv ℝ (fun θ => strongDirichletOperator fixedSobolevCalculus 0
        (commonSupportMatrixFamily 2 a ha S hS hz θ)) 0‖ ≤ 2*strongC1OperatorBudget fixedSobolevCalculus*q ∧
      ‖fderiv ℝ (fun θ => fullCoefficientOperatorL fixedSobolevCalculus 0
        (commonSupportMatrixFamily 2 a ha S hS hz θ)) 0‖ ≤ 2*fullC1OperatorBudget fixedSobolevCalculus*q := by
  obtain ⟨L0,hL0⟩ := hCompact.exists_bound_of_continuousOn
    (show ContinuousOn (fun z : X => z) (tsupport B) from continuous_id.continuousOn)
  let L := max L0 2
  have hzB (p z : X) (hz : z ∉ Metric.closedBall (0:X) L) : B z = 0 := by
    by_contra hn
    apply hz
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (hL0 z (subset_closure hn)).trans (le_max_left _ _)
  let A : ℝ × X → Mat := fun v => B v.2
  have hA : ContDiff ℝ ∞ A := hB.comp contDiff_snd
  have hzA (p : ℝ) (z : X) (hz : z ∉ Metric.closedBall (0:X) L) : A (p,z) = 0 := hzB 0 z hz
  let a : ℝ × X → Mat := fun v => coordinateRotationPrincipalFamily i j A ((v.1,0),v.2)
  have ha : ContDiff ℝ ∞ a := (contDiff_coordinateRotationPrincipalFamily i j A hA).comp
    ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)
  have hz (θ : ℝ) (z : X) (hz : z ∉ Metric.closedBall (0:X) L) : a (θ,z) = 0 :=
    coordinateRotationPrincipalFamily_zero_outside i j A L hzA (θ,0) z hz
  have hEquality (θ : ℝ) (z : X) (hz : z ∈ Metric.closedBall (0:X) 2) :
      a (θ,z) = coordinateRotationPrincipalFamily i j (fun v : ℝ × X => R v.2) ((θ,0),z) := by
    have hRot : coordinateRotation i j θ z ∈ Metric.closedBall (0:X) 2 := by
      simpa only [Metric.mem_closedBall,dist_zero_right,coordinateRotation_norm] using hz
    change _ * B (coordinateRotation i j θ z) * _ = _ * R (coordinateRotation i j θ z) * _
    rw [(hRep _ hRot).eq_of_nhds]
  let b := rotationPrincipalCoefficientDerivative i j B
  have hbSmooth : ContDiff ℝ ∞ b := by
    have h := ((generatorPairMatrixL i j).contDiff.comp hB).add
      ((hB.fderiv_right (by simp)).clm_apply (rotationVectorL i j).contDiff)
    exact h
  have hb (z : X) : HasDerivAt (fun θ => a (θ,z)) (b z) 0 :=
    hasDerivAt_coordinateRotationPrincipal_zero i j B z (hB.differentiable (by simp) z)
  have hGen (z : X) (hz : z ∈ (ballOpens:Set X)) :
      b =ᶠ[𝓝 z] rotationPrincipalCoefficientDerivative i j R := by
    filter_upwards [(hRep z (unitBall_subset_closedBall_two hz)).eventuallyEq_nhds] with w hw
    simp only [b,rotationPrincipalCoefficientDerivative,hw.eq_of_nhds,hw.fderiv_eq]
  have hv (z : X) (hz : z ∈ (ballOpens:Set X)) : ‖b z‖ ≤ q := by
    rw [(hGen z hz).eq_of_nhds]
    exact hValue z hz
  have hs (z : X) (hz : z ∈ (ballOpens:Set X)) : ‖fderiv ℝ b z‖ ≤ q := by
    rw [(hGen z hz).fderiv_eq]
    exact hSpatial z hz
  obtain ⟨hStrong,hFull⟩ := norm_fderiv_angle_commonSupport_operators_le fixedSobolevCalculus
    a ha (Metric.closedBall (0:X) L) (isCompact_closedBall _ _) hz b
    (hbSmooth.differentiable (by simp)) hb q hq hv hs
  exact ⟨a,ha,Metric.closedBall (0:X) L,isCompact_closedBall _ _,hz,hEquality,hStrong,hFull⟩

/-- A genuine compact smooth representative of the selected quadratic
    coefficient remainder, agreeing as a germ along the entire closed ball. -/
theorem uniform_actual_compact_firstCoefficientRemainder {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ B : X → Mat,ContDiff ℝ ∞ B ∧ HasCompactSupport B ∧
        ∀ z ∈ Metric.closedBall (0:X) 2,B =ᶠ[𝓝 z] firstCoefficientRemainder d y := by
  obtain ⟨η,hη,hFamily⟩ := uniform_actual_normal_local_coefficient_family hY hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨ψ,hψ,hRange,hOne,hSupport,hSub⟩ := (isCompact_closedBall (0:X) 2).exists_contDiff_cutoff
    isOpen_univ (subset_univ _)
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  obtain ⟨A,hA,S,hS,hz,V,hV,hyV,hVY,hRep⟩ := hFamily floor hf ε hε hSmall d hd y hy d.g₁ (by simp)
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let r := d.radius y
  let ell := firstDensityCenterLinearL d y
  let B : X → Mat := fun z => ψ z • (A (y,z)-(c+r*ell z) • (1:Mat))
  have hB : ContDiff ℝ ∞ B := hψ.smul
    ((hA.comp (contDiff_const.prodMk contDiff_id)).sub
      ((contDiff_const.add (contDiff_const.mul ell.contDiff)).smul contDiff_const))
  have hBS : support B ⊆ tsupport ψ := by
    intro z hzB
    apply subset_closure
    intro hzψ
    exact hzB (by simp only [B,hzψ,zero_smul])
  have hCompact : HasCompactSupport B := HasCompactSupport.of_support_subset_isCompact hSupport hBS
  refine ⟨B,hB,hCompact,?_⟩
  intro z hzB
  have hψOne : ∀ᶠ w in 𝓝 z,ψ w = 1 := by
    filter_upwards [mem_interior_iff_mem_nhds.mp (hOne hzB)] with w hw
    exact hw
  have hAGerm := (hRep y hyV z hzB).comp_tendsto
    (show Tendsto (fun w : X => (y,w)) (𝓝 z) (𝓝 (y,z)) from
      (continuousAt_const.prodMk continuousAt_id).tendsto)
  filter_upwards [hψOne,hAGerm] with w hw hAw
  simp only [Function.comp_def] at hAw
  simp only [B,hw,one_smul,hAw,firstCoefficientRemainder,affineMatrixRemainder,c,r,ell]

/-- Uniformly quadratic actual whole-angle coefficient-remainder operator
    derivatives, for every admitted radius profile and unrestricted smooth
    orthonormal frame. No ellipticity is required of the remainder itself. -/
theorem uniform_actual_first_remainder_rotated_operator_C1 {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ 0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i j : I,
      ∃ a : ℝ × X → Mat,∃ ha : ContDiff ℝ ∞ a,∃ S : Set X,∃ hS : IsCompact S,
        ∃ hz : ∀ θ z,z ∉ S → a (θ,z) = 0,
        (∀ θ z,z ∈ Metric.closedBall (0:X) 2 → a (θ,z) = coordinateRotationPrincipalFamily i j
          (fun v : ℝ × X => firstCoefficientRemainder d y v.2) ((θ,0),z)) ∧
        ‖fderiv ℝ (fun θ => strongDirichletOperator fixedSobolevCalculus 0
          (commonSupportMatrixFamily 2 a ha S hS hz θ)) 0‖ ≤ C*(d.radius y)^2 ∧
        ‖fderiv ℝ (fun θ => fullCoefficientOperatorL fixedSobolevCalculus 0
          (commonSupportMatrixFamily 2 a ha S hS hz θ)) 0‖ ≤ C*(d.radius y)^2 := by
  have hCompactTheorem := uniform_actual_compact_firstCoefficientRemainder hY hΩ
    (by omega : 2 ≤ m) K ρ c₀ M Cj hK hρ
  obtain ⟨ηB,hηB,hCompact⟩ := hCompactTheorem
  have hRotationTheorem := uniform_first_coefficient_rotation_remainder_C1 hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηR,Q,hηR,hQ,hRotation⟩ := hRotationTheorem
  let S := strongC1OperatorBudget fixedSobolevCalculus
  let F := fullC1OperatorBudget fixedSobolevCalculus
  have hS : 0 ≤ S := strongC1OperatorBudget_nonneg _
  have hF : 0 ≤ F := fullC1OperatorBudget_nonneg _
  refine ⟨min ηB ηR,2*(S+F)*Q,lt_min hηB hηR,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd y hy i j
  obtain ⟨B,hB,hSupport,hRep⟩ := hCompact floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  have hAt (z : X) (hz : z ∈ (ballOpens:Set X)) := hRotation floor hf ε hε
    (hSmall.trans (min_le_right _ _)) d hd y hy i j z (unitBall_subset_closedBall_two hz)
  obtain ⟨a,ha,T,hT,hz,hEquality,hStrong,hFull⟩ := exists_rotated_remainder_operator_family
    (firstCoefficientRemainder d y) B hB hSupport hRep i j (Q*(d.radius y)^2)
    (by positivity) (fun z hz => (hAt z hz).2.1) (fun z hz => (hAt z hz).2.2)
  refine ⟨a,ha,T,hT,hz,hEquality,hStrong.trans ?_,hFull.trans ?_⟩
  · change 2*S*(Q*(d.radius y)^2) ≤ 2*(S+F)*Q*(d.radius y)^2
    have h := mul_le_mul_of_nonneg_right (show S ≤ S+F from le_add_of_nonneg_right hF) (by positivity : 0 ≤ 2*Q*(d.radius y)^2)
    nlinarith only [h]
  · change 2*F*(Q*(d.radius y)^2) ≤ 2*(S+F)*Q*(d.radius y)^2
    have h := mul_le_mul_of_nonneg_right (show F ≤ S+F from le_add_of_nonneg_left hS) (by positivity : 0 ≤ 2*Q*(d.radius y)^2)
    nlinarith only [h]

end ShrinkingSpheres

import Proof.WeakEnergyAngleDerivative
import Proof.CompactRotatedRemainderOperator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Function
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SmoothSphereRotation
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- A compact actual rotated coefficient family has the same local weak energy
    derivative budgets, independently of every exterior cutoff. -/
theorem exists_rotated_remainder_weakEnergy_family
    (R B : X → Mat) (hB : ContDiff ℝ ∞ B) (hCompact : HasCompactSupport B)
    (hRep : ∀ z ∈ Metric.closedBall (0:X) 2,B =ᶠ[𝓝 z] R)
    (i j : I) (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ z ∈ (ballOpens:Set X),‖rotationPrincipalCoefficientDerivative i j R z‖ ≤ q) :
    ∃ a : ℝ × X → Mat,∃ ha : ContDiff ℝ ∞ a,∃ S : Set X,∃ hS : IsCompact S,
      ∃ hz : ∀ θ z,z ∉ S → a (θ,z) = 0,
      (∀ θ z,z ∈ Metric.closedBall (0:X) 2 → a (θ,z) = coordinateRotationPrincipalFamily i j
        (fun v : ℝ × X => R v.2) ((θ,0),z)) ∧
      ‖fderiv ℝ (commonSupportFullWeakEnergy a ha) 0‖ ≤ weakFullDerivativeBudget*q ∧
      ‖fderiv ℝ (commonSupportWeakEnergy a ha) 0‖ ≤ weakFullDerivativeBudget*q ∧
      ‖fderiv ℝ (commonSupportZeroWeakEnergy a ha) 0‖ ≤ weakFullDerivativeBudget*q := by
  have hBound : ∃ L0 : ℝ,∀ z ∈ tsupport B,‖z‖ ≤ L0 :=
    hCompact.exists_bound_of_continuousOn
      (show ContinuousOn (fun z : X => z) (tsupport B) from continuous_id.continuousOn)
  obtain ⟨L0,hL0⟩ := hBound
  let L := max L0 2
  have hzB (z : X) (hz : z ∉ Metric.closedBall (0:X) L) : B z = 0 := by
    by_contra hn
    apply hz
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (hL0 z (subset_closure hn)).trans (le_max_left _ _)
  let A : ℝ × X → Mat := fun v => B v.2
  have hA : ContDiff ℝ ∞ A := hB.comp contDiff_snd
  have hzA (p : ℝ) (z : X) (hz : z ∉ Metric.closedBall (0:X) L) : A (p,z) = 0 := hzB z hz
  let a : ℝ × X → Mat := fun v => coordinateRotationPrincipalFamily i j A ((v.1,0),v.2)
  have ha : ContDiff ℝ ∞ a := (contDiff_coordinateRotationPrincipalFamily i j A hA).comp
    ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)
  have hz (θ : ℝ) (z : X) (hz : z ∉ Metric.closedBall (0:X) L) : a (θ,z) = 0 :=
    coordinateRotationPrincipalFamily_zero_outside i j A L hzA (θ,0) z hz
  have hEquality (θ : ℝ) (z : X) (hz : z ∈ Metric.closedBall (0:X) 2) :
      a (θ,z) = coordinateRotationPrincipalFamily i j (fun v : ℝ × X => R v.2) ((θ,0),z) := by
    have hRot : coordinateRotation i j θ z ∈ Metric.closedBall (0:X) 2 := by
      simpa only [Metric.mem_closedBall,dist_zero_right,coordinateRotation_norm] using hz
    change _*B (coordinateRotation i j θ z)*_ = _*R (coordinateRotation i j θ z)*_
    rw [(hRep _ hRot).eq_of_nhds]
  let b := rotationPrincipalCoefficientDerivative i j B
  have hb (z : X) (_ : z ∈ (ballOpens:Set X)) : HasDerivAt (fun θ => a (θ,z)) (b z) 0 :=
    hasDerivAt_coordinateRotationPrincipal_zero i j B z (hB.differentiable (by simp) z)
  have hLocal (z : X) (hzB : z ∈ (ballOpens:Set X)) : ‖b z‖ ≤ q := by
    have hGen : b =ᶠ[𝓝 z] rotationPrincipalCoefficientDerivative i j R := by
      filter_upwards [(hRep z (unitBall_subset_closedBall_two hzB)).eventuallyEq_nhds] with w hw
      simp only [b,rotationPrincipalCoefficientDerivative,hw.eq_of_nhds,hw.fderiv_eq]
    rw [hGen.eq_of_nhds]
    exact hValue z hzB
  have hF := norm_fderiv_angle_commonSupport_fullWeakEnergy_le a ha (Metric.closedBall (0:X) L) (isCompact_closedBall _ _) hz b hb q hq hLocal
  have hWZ := norm_fderiv_angle_commonSupport_weakEnergy_le a ha (Metric.closedBall (0:X) L) (isCompact_closedBall _ _) hz b hb q hq hLocal
  obtain ⟨hW,hZ⟩ := hWZ
  exact ⟨a,ha,Metric.closedBall (0:X) L,isCompact_closedBall _ _,hz,hEquality,hF,hW,hZ⟩

/-- For every admitted radius, the actual rotated quadratic coefficient
    remainder has uniform quadratic full/restricted/zero energy derivatives. -/
theorem uniform_actual_rotated_remainder_weakEnergy_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ 0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i j : I,
      ∃ a : ℝ × X → Mat,∃ ha : ContDiff ℝ ∞ a,∃ S : Set X,∃ hS : IsCompact S,
        ∃ hz : ∀ θ z,z ∉ S → a (θ,z) = 0,
        (∀ θ z,z ∈ Metric.closedBall (0:X) 2 → a (θ,z) = coordinateRotationPrincipalFamily i j
          (fun v : ℝ × X => firstCoefficientRemainder d y v.2) ((θ,0),z)) ∧
        ‖fderiv ℝ (commonSupportFullWeakEnergy a ha) 0‖ ≤ C*(d.radius y)^2 ∧
        ‖fderiv ℝ (commonSupportWeakEnergy a ha) 0‖ ≤ C*(d.radius y)^2 ∧
        ‖fderiv ℝ (commonSupportZeroWeakEnergy a ha) 0‖ ≤ C*(d.radius y)^2 := by
  have hBTheorem := uniform_actual_compact_firstCoefficientRemainder hY hΩ (by omega : 2 ≤ m)
    K ρ c₀ M Cj hK hρ
  obtain ⟨ηB,hηB,hCompact⟩ := hBTheorem
  have hRTheorem := uniform_first_coefficient_rotation_remainder_C1 hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηR,Q,hηR,hQ,hRotation⟩ := hRTheorem
  let C := weakFullDerivativeBudget*Q
  have hC : 0 ≤ C := mul_nonneg weakFullDerivativeBudget_nonneg hQ
  refine ⟨min ηB ηR,C,lt_min hηB hηR,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy i j
  have hPointCompact := hCompact floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  obtain ⟨B,hB,hSupport,hRep⟩ := hPointCompact
  have hAt (z : X) (hzB : z ∈ (ballOpens:Set X)) := hRotation floor hf ε hε
    (hSmall.trans (min_le_right _ _)) d hd y hy i j z (unitBall_subset_closedBall_two hzB)
  have hPointFamily := exists_rotated_remainder_weakEnergy_family
    (firstCoefficientRemainder d y) B hB hSupport hRep i j (Q*(d.radius y)^2)
    (by positivity) (fun z hzB => (hAt z hzB).2.1)
  obtain ⟨a,ha,S,hS,hz,hEquality,hFull,hWeak,hZero⟩ := hPointFamily
  exact ⟨a,ha,S,hS,hz,hEquality,hFull.trans_eq (by dsimp [C];ring),
    hWeak.trans_eq (by dsimp [C];ring),hZero.trans_eq (by dsimp [C];ring)⟩

end ShrinkingSpheres

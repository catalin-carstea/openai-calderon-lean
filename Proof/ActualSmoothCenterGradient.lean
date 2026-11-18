import Proof.ActualCenterGradientGerms
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

lemma contDiffOn_actual_center_gradient_adjoint {Y : Set X} {d : Data} {a : X} {CC CH : ℝ}
    (hY : IsOpen Y) (hr : ∀ x ∈ Y,d.radius x ≠ 0)
    (hrSm : ContDiffOn ℝ ∞ d.radius Y)
    (heSm : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hC : ∀ y ∈ Y,∀ j : I,Nonempty (RelativeCenterErrorCoefficientFamily d y a j CC CH))
    (A G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (hA : ContDiffOn ℝ ∞ A Y)
    (hG : ∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) :
    ContDiffOn ℝ ∞ G Y := by
  intro y hy
  let C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH := fun j => Classical.choice (hC y hy j)
  have hGerm := actual_center_gradient_local_germ hY hy (hr y hy) hrSm heSm C A G hG
  have hParam := (contDiffOn_normalFrameRelativeActualParameter d (d.radius y) hrSm heSm).contDiffAt (hY.mem_nhds hy)
  have hQ (j : I) : ContDiffAt ℝ ∞ (fun x => (C j).closed (normalFrameRelativeActualParameter d (d.radius y) x)) y :=
    (contDiff_commonSupportClosedCoefficientFamily 3 (C j).scalar (C j).smooth (C j).support (C j).compact (C j).supported).contDiffAt.comp y hParam
  have hGrad := contDiffAt_closedBoundaryGradientAdjoint _ A y hQ (hA.contDiffAt (hY.mem_nhds hy))
  have hInv := (hrSm.contDiffAt (hY.mem_nhds hy)).inv (hr y hy)
  exact ((hInv.smul hGrad).congr_of_eventuallyEq hGerm).contDiffWithinAt

lemma exists_smooth_actual_center_gradient_adjoint {Y : Set X} {d : Data} {a : X} {CC CH : ℝ}
    (hY : IsOpen Y) (hr : ∀ x ∈ Y,d.radius x ≠ 0)
    (hrSm : ContDiffOn ℝ ∞ d.radius Y)
    (heSm : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hC : ∀ y ∈ Y,∀ j : I,Nonempty (RelativeCenterErrorCoefficientFamily d y a j CC CH))
    (A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (hA : ContDiffOn ℝ ∞ A Y) :
    ∃ G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ G Y ∧ ∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x) := by
  classical
  have hPoint (x : X) (hx : x ∈ Y) : ∃ G,RealizesActualCenterGradientAdjoint d x a (A x) G := by
    let C : (j : I) → RelativeCenterErrorCoefficientFamily d x a j CC CH := fun j => Classical.choice (hC x hx j)
    let W : I → SmoothCoefficientJets 2 := fun j => (C j).pointCoefficient
    have hW (j : I) (w : UnitSphere) : coefficientValue 2 (W j) w.val = actualCenterErrorWeight d x a j w.val := by
      have hw2 : w.val ∈ Metric.closedBall (0:X) 2 :=
        Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall w.property)
      exact ((C j).point_coefficient_actual w.val hw2).eq_of_nhds
    exact ⟨_,realizesActualCenterGradientAdjoint_of_coefficients d x a (A x) W hW⟩
  let G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0 := fun x =>
    if hx : x ∈ Y then Classical.choose (hPoint x hx) else 0
  have hG (x : X) (hx : x ∈ Y) : RealizesActualCenterGradientAdjoint d x a (A x) (G x) := by
    dsimp only [G]
    rw [dite_eq_left hx]
    exact Classical.choose_spec (hPoint x hx)
  exact ⟨G,contDiffOn_actual_center_gradient_adjoint hY hr hrSm heSm hC A G hA hG,hG⟩

theorem uniform_actual_smooth_center_gradient_adjoint {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,ContDiffOn ℝ ∞ A Y → ∀ a : X,
      ∃ G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ContDiffOn ℝ ∞ G Y ∧ ∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x) := by
  obtain ⟨η,CC,CH,hη,hη1,hCC,hCH,hC⟩ :=
    uniform_relative_center_error_coefficient_families hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd A hA a
  exact exists_smooth_actual_center_gradient_adjoint hY
    (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne') hd.2.2.2.2.1.1
    (fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub)
    (fun y hy j => hC floor hf ε hε hSmall d hd y hy a j) A hA
end ShrinkingSpheres

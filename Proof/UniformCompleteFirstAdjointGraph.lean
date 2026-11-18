import Proof.CompleteAdjointTensorGraph
import Proof.CompleteFirstAdjointCovariantGraph
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- The complete actual first adjoint has a uniform genuine covariant graph;
    the SAME small error jet is retained for the principal second-trace caller. -/
theorem uniform_complete_first_adjoint_covariant_graph {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (C0 : ℝ) (hC0 : 0 ≤ C0) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ A Y →
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      ∀ G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ a,ContDiffOn ℝ ∞ (G a) Y) →
      (∀ a,∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x (axis a) (A x) (G a x)) →
      (∀ a,∀ x ∈ Y,‖actualFirstAdjointErrorFamily d (axis a) A (G a) x‖ ≤ C0*d.radius x) →
      ∃ S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        (∀ i j,ContDiffOn ℝ ∞ (S i j) Y) ∧ ∀ y ∈ Y,∀ i j,
          CoarseCovariantRotationGraph d y (d.frame y i) (completeFirstAdjointFamily d A G j)
            ((∑ k : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) j k • completeFirstAdjointFamily d A G k y)+
              (-(d.radius y)⁻¹*fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i)) • flatOneRaisingL j+
              hessianBilinear d.γ (fun x => Real.log (d.radius x)) y (d.frame y i) (d.frame y j) • sphereSobolevDegreeL+
              (firstFrameAdjointCovariantJetL d y (d.frame y i) j).comp (sphereSobolevInclusionL 1 0 (by norm_num))+S i j y) ∧
          ‖S i j y‖ ≤ CE*d.radius y*beta d.γ d.radius y := by
  obtain ⟨η,CE,hη,hη1,hCE,hProduce⟩ :=
    uniform_complete_first_adjoint_covariant_graph_with_error_graph hY hΩ hSub hm K ρ c₀ M Cj hK hρ C0 hC0
  refine ⟨η,CE,hη,hη1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd R A hAS hR hA G hGS hG hE
  obtain ⟨S,hSS,hAll⟩ := hProduce floor hf ε hε hSmall d hd R A hAS hR hA G hGS hG hE
  exact ⟨S,hSS,fun y hy i j => (hAll y hy i j).2⟩
end ShrinkingSpheres

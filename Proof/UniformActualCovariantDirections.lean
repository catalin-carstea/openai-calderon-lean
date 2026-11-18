import Proof.CompatibleEndpointDirectionScaling
import Proof.UniformActualCovariantEndpoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- The SAME selected coarse covariant jet has genuine endpoints in every
    physical direction, uniformly with its exact direction-norm factor. -/
theorem uniform_actual_covariant_direction_endpoints {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ _hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ A Y →
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      ∀ a : X,∀ G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ G Y →
      (∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) →
      ∀ y ∈ Y,∀ S : X →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0),
      (∀ b,CoarseCovariantRotationGraph d y b (actualFirstAdjointErrorFamily d a A G) (S b)) →
      ∀ b : X,
      ∃ Lo : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ∃ Hi : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (S b)=
          Lo.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hi=
          (S b).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) ∧
        ‖Lo‖ ≤ CE*‖a‖*d.radius y*beta d.γ d.radius y*‖b‖ ∧
        ‖Hi‖ ≤ CE*‖a‖*d.radius y*beta d.γ d.radius y*‖b‖ := by
  obtain ⟨η,CE,hη,hη1,hCE,hProduce⟩ :=
    uniform_actual_covariant_error_endpoints hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,CE,hη,hη1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd R A hAS hR hA a G hGS hG y hy S hS b
  exact compatible_endpoints_all_directions S (CE*‖a‖*d.radius y*beta d.γ d.radius y)
    (fun u hu => hProduce floor hf ε hε hSmall d hd R A hAS hR hA a G hGS hG y hy u hu (S u) (hS u)) b
end ShrinkingSpheres

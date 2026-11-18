import Proof.UniformActualFirstErrorAdjointHigherEndpoints
import Proof.UniformFrameFirstErrorHigherAdjointCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- SAME selected frame first errors admit genuine higher adjoints with
    a common linear-radius norm bound. No frame derivative bound is used. -/
theorem uniform_actual_frame_first_error_adjoint_higher_endpoints {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CADJ : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CADJ ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ∀ G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      (∀ a,∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x (axis a) (A x) (G a x)) →
      ∀ CE : ℝ,∀ P : ActualFrameErrorEndpointPair Y d A G CE,∀ y ∈ Y,∀ j : I,
        ∃ Ha : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
          (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ha=
            (P.low j y).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
          ‖Ha‖ ≤ CADJ*d.radius y := by
  classical
  obtain ⟨ηE,CE,hηE,hηE1,hCE,hEndpoints⟩ := uniform_actual_first_adjoint_error_endpoints
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηA,CA,hηA,hηA1,hCA,hAdj⟩ := uniform_actual_first_error_adjoint_higher_endpoints
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηE ηA,3*K*CA,lt_min hηE hηA,(min_le_left _ _).trans hηE1,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd R A G hR hA hG C0 P y hy
  choose Lo Hi hLS hHS hAll using fun a : I => hEndpoints floor hf ε hε
    (hSmall.trans (min_le_left _ _)) d hd (axis a) R A (G a) hR hA (hG a)
  have hPoint (a : I) := hAdj floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd (axis a)
    R A (G a) hR hA (hG a) y hy (Lo a y) (hAll a y hy).1
  choose Adj hAdj hNorm using hPoint
  have hNorm' (a : I) : ‖Adj a‖ ≤ CA*d.radius y := by
    simpa only [norm_axis,mul_one] using hNorm a
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hCoeff (l a : I) : |d.frame y l a| ≤ K := hd.1.1.frame_component_abs_le hK d.frame (hSub hy) hFrame l a
  have hLEq (l : I) := half_endpoint_unique_of_coarse (actualFrameFirstAdjointErrorFamily d A G l y)
    (P.low l y) (∑ a : I,d.frame y l a • Lo a y) (P.low_coarse l y hy)
    (frame_low_endpoint_combination d A G l y (fun a => Lo a y) (fun a => (hAll a y hy).1))
  let H (l : I) := ∑ a : I,d.frame y l a • Adj a
  have hPair (l : I) : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (H l)=
      (P.low l y).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
    have hh := finite_real_adjoint_balanced_combination
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) (fun a => Lo a y) Adj hAdj
      (fun a => d.frame y l a)
    exact hh.trans (congrArg (fun T => T.adjoint.comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) (hLEq l).symm)
  intro j
  refine ⟨H j,hPair j,?_⟩
  exact (norm_weighted_sum_three_le (fun a => d.frame y j a) Adj K (CA*d.radius y)
    (zero_le_one.trans hK) (hCoeff j) hNorm').trans_eq (by ring)
end ShrinkingSpheres

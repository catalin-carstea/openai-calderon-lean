import Proof.FrameEndpointCombination
import Proof.UniformActualFirstAdjointEndpoints
import Proof.ActualFrameFirstAdjointError
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- The SAME actual frame error has smooth half and higher endpoints, with
    common uniform radius gain. Transport uses frame values only. -/
theorem uniform_actual_frame_first_adjoint_error_endpoints {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ _hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ∀ G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      (∀ a,∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x (axis a) (A x) (G a x)) →
      ∃ L : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ∃ H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
        (∀ i,ContDiffOn ℝ ∞ (L i) Y) ∧ (∀ i,ContDiffOn ℝ ∞ (H i) Y) ∧
        ∀ i,∀ x ∈ Y,
          (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (actualFrameFirstAdjointErrorFamily d A G i x)=
            (L i x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
          (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (H i x)=
            (actualFrameFirstAdjointErrorFamily d A G i x).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) ∧
          ‖L i x‖ ≤ CE*d.radius x ∧ ‖H i x‖ ≤ CE*d.radius x := by
  classical
  obtain ⟨η,CE,hη,hη1,hCE,hProduce⟩ :=
    uniform_actual_first_adjoint_error_endpoints hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,3*K*CE,hη,hη1,mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hK)) hCE,?_⟩
  intro floor hf ε hε hSmall d hd R A G hR hA hG
  choose L H hLS hHS hAll using fun a : I =>
    hProduce floor hf ε hε hSmall d hd (axis a) R A (G a) hR hA (hG a)
  let LF := fun i x => ∑ a : I,d.frame x i a • L a x
  let HF := fun i x => ∑ a : I,d.frame x i a • H a x
  have hFrameSmooth (i a : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i a) Y :=
    ((EuclideanSpace.proj (𝕜:=ℝ) a).contDiff.comp_contDiffOn (hd.1.2.2.2.2.2.2.1 i)).mono hSub
  refine ⟨LF,HF,(fun i => ContDiffOn.sum (fun a _ => (hFrameSmooth i a).smul (hLS a))),
    (fun i => ContDiffOn.sum (fun a _ => (hFrameSmooth i a).smul (hHS a))),?_⟩
  intro i x hx
  have hCompatL (a : I) := (hAll a x hx).1
  have hCompatH (a : I) := (hAll a x hx).2.1
  have hNL (a : I) : ‖L a x‖ ≤ CE*d.radius x := by simpa only [norm_axis,mul_one] using (hAll a x hx).2.2.1
  have hNH (a : I) : ‖H a x‖ ≤ CE*d.radius x := by simpa only [norm_axis,mul_one] using (hAll a x hx).2.2.2
  have hFrame := hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hCoeff (a : I) : |d.frame x i a| ≤ K := hd.1.1.frame_component_abs_le hK d.frame (hSub hx) hFrame i a
  refine ⟨?_,?_,?_,?_⟩
  · exact frame_low_endpoint_combination d A G i x (fun a => L a x) hCompatL
  · exact frame_high_endpoint_combination d A G i x (fun a => H a x) hCompatH
  · exact (norm_weighted_sum_three_le (fun a => d.frame x i a) (fun a => L a x)
      K (CE*d.radius x) (zero_le_one.trans hK) hCoeff hNL).trans_eq (by ring)
  · exact (norm_weighted_sum_three_le (fun a => d.frame x i a) (fun a => H a x)
      K (CE*d.radius x) (zero_le_one.trans hK) hCoeff hNH).trans_eq (by ring)
end ShrinkingSpheres

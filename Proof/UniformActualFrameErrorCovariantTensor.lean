import Proof.FrameConnectionGeometryBounds
import Proof.FrameTensorOperatorCombination
import Proof.UniformActualFirstErrorSmoothCovariant
import Proof.FrameErrorCovariantTensor
import Proof.UniformNormalGeodesicBounds
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

/-- The SAME actual frame error has a globally smooth tensor covariant
    derivative with radius-beta gain and no frame derivative budget. -/
theorem uniform_actual_frame_error_covariant_tensor {Y Ω : Set X}
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
          CoarseCovariantRotationGraph d y (d.frame y i) (actualFrameFirstAdjointErrorFamily d A G j)
            ((∑ k : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) j k •
              actualFrameFirstAdjointErrorFamily d A G k y)+S i j y) ∧
          ‖S i j y‖ ≤ CE*d.radius y*beta d.γ d.radius y := by
  classical
  obtain ⟨η,C1,hη,hη1,hC1,hCov⟩ :=
    uniform_actual_first_error_smooth_covariant hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let CΓ := 243*K*|M ⟨1,by omega⟩|
  let CE := 3*K^2*C1+3*CΓ*K^2*C0
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hΓ : 0 ≤ CΓ := by dsimp only [CΓ];positivity
  have hCE : 0 ≤ CE := by dsimp only [CE];positivity
  refine ⟨η,CE,hη,hη1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd R A hAS hR hA G hGS hG hE
  choose S hSS hS using fun a : I =>
    hCov floor hf ε hε hSmall d hd R A hAS hR hA (axis a) (G a) (hGS a) (hG a)
  let F : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0 := fun a => actualFirstAdjointErrorFamily d (axis a) A (G a)
  let T : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
    fun i j y => frameWeightedCovariantTensorJet d F S y (d.frame y i) j
  have he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y :=
    fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFS (a : I) : ContDiffOn ℝ ∞ (F a) Y :=
    contDiffOn_actualFirstAdjointErrorFamily (axis a) hY hΩ hSub hd.1 hKp hd.2.2.2.2.1.1
      (fun x hx => (hd.2.2.2.2.1.2 x hx).1) A (G a) hAS (hGS a)
  have hEll : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  refine ⟨T,fun i j => contDiffOn_frameWeightedCovariantTensorJet hY d hEll hKp he F S hFS hSS
    (fun y => d.frame y i) (he i) j,?_⟩
  intro y hy i j
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hGeometry := hd.frame_connection_geometry_bounds (by omega) hK hy
  have heN := hGeometry.1
  refine ⟨?_,?_⟩
  · exact frameWeighted_covariant_graph d F S y (d.frame y i) j
      (fun a => ((hFS a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      (((he j).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) hFrame
      (fun a => (hS a y hy).1 (d.frame y i))
  · have hr : 0 ≤ d.radius y := (hd.2.2.2.2.1.2 y hy).1.le
    have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
    have hβ0 : 0 ≤ beta d.γ d.radius y := zero_le_one.trans hβ
    have hSN (a : I) : ‖S a y (d.frame y i)‖ ≤ C1*K*d.radius y*beta d.γ d.radius y := by
      have hh := (S a y).le_opNorm (d.frame y i)
      have hSA : ‖S a y‖ ≤ C1*d.radius y*beta d.γ d.radius y := by
        simpa only [norm_axis,mul_one] using (hS a y hy).2
      exact hh.trans ((mul_le_mul hSA (heN i) (norm_nonneg _) (by positivity)).trans_eq (by ring))
    have hc : ∀ a : I,|(connection d.γ y (d.frame y i) (d.frame y j)) a| ≤ CΓ*K^2 :=
      fun a => hGeometry.2 i j a

    have hBound := norm_frameWeightedCovariantTensorJet_le d F S y (d.frame y i) j hK0
      (show 0 ≤ CΓ*K^2 by positivity)
      (fun a => hd.1.1.frame_component_abs_le hK d.frame (hSub hy) hFrame j a) hc
      (fun a => hE a y hy) hSN
    change ‖frameWeightedCovariantTensorJet d F S y (d.frame y i) j‖ ≤ _
    exact hBound.trans (by
      simpa only [CE] using frame_tensor_radius_beta_budget K CΓ C0 C1
        (d.radius y) (beta d.γ d.radius y) hΓ hC0 hr hβ)
end ShrinkingSpheres

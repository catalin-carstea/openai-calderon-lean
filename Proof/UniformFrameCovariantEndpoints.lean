import Proof.UniformActualCovariantDirections
import Proof.SelectedFrameTensor
import Proof.FrameConnectionGeometryBounds
import Proof.UniformActualFirstErrorSmoothCovariant
import Proof.UniformActualFirstAdjointEndpoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- Uniform genuine endpoints of ANY selected actual frame covariant error
    tensor. The physical second-trace tensor witness is preserved by graph
    uniqueness; only frame values enter the common norm bound. -/
theorem uniform_actual_frame_covariant_error_endpoints {Y Ω : Set X}
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
      ∀ G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ a,ContDiffOn ℝ ∞ (G a) Y) →
      (∀ a,∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x (axis a) (A x) (G a x)) →
      ∀ y ∈ Y,∀ i j : I,∀ T : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      CoarseCovariantRotationGraph d y (d.frame y i) (actualFrameFirstAdjointErrorFamily d A G j)
        ((∑ k : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) j k •
          actualFrameFirstAdjointErrorFamily d A G k y)+T) →
      ∃ Lo : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ∃ Hi : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T=
          Lo.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hi=
          T.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) ∧
        ‖Lo‖ ≤ CE*d.radius y*beta d.γ d.radius y ∧
        ‖Hi‖ ≤ CE*d.radius y*beta d.γ d.radius y := by
  classical
  obtain ⟨ηS,CS,hηS,hηS1,hCS,hCov⟩ :=
    uniform_actual_first_error_smooth_covariant hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηD,CD,hηD,hηD1,hCD,hDirs⟩ :=
    uniform_actual_covariant_direction_endpoints hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηF,CF,hηF,hηF1,hCF,hEndpoints⟩ :=
    uniform_actual_first_adjoint_error_endpoints hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let CΓ := 243*K*|M ⟨1,by omega⟩|
  let CE := 3*K^2*CD+3*CΓ*K^2*CF
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hΓ : 0 ≤ CΓ := by dsimp only [CΓ];positivity
  have hCE : 0 ≤ CE := by dsimp only [CE];positivity
  refine ⟨min ηS (min ηD ηF),CE,lt_min hηS (lt_min hηD hηF),
    (min_le_left _ _).trans hηS1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd R A hAS hR hA G hGS hG
  have hSmallS := hSmall.trans (min_le_left _ _)
  have hSmallD := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallF := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  choose S hSS hS using fun a : I =>
    hCov floor hf ε hε hSmallS d hd R A hAS hR hA (axis a) (G a) (hGS a) (hG a)
  choose L H hLS hHS hE using fun a : I =>
    hEndpoints floor hf ε hε hSmallF d hd (axis a) R A (G a) hR hA (hG a)
  let F : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
    fun a => actualFirstAdjointErrorFamily d (axis a) A (G a)
  have he (j : I) : ContDiffOn ℝ ∞ (fun x => d.frame x j) Y :=
    (hd.1.2.2.2.2.2.2.1 j).mono hSub
  have hFS (a : I) : ContDiffOn ℝ ∞ (F a) Y :=
    contDiffOn_actualFirstAdjointErrorFamily (axis a) hY hΩ hSub hd.1 hKp hd.2.2.2.2.1.1
      (fun x hx => (hd.2.2.2.2.1.2 x hx).1) A (G a) hAS (hGS a)
  intro y hy i j T hT
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hGeometry := hd.frame_connection_geometry_bounds (by omega) hK hy
  have heN := hGeometry.1
  choose LC HC hD using fun a : I =>
    hDirs floor hf ε hε hSmallD d hd R A hAS hR hA (axis a) (G a) (hGS a) (hG a)
      y hy (S a y) (fun b => (hS a y hy).1 b) (d.frame y i)
  let Lo := frameTensorOperatorCombination d y (d.frame y i) j (fun a => L a y) LC
  let Hi := frameTensorOperatorCombination d y (d.frame y i) j (fun a => H a y) HC
  have hMid : T=frameTensorOperatorCombination d y (d.frame y i) j
      (fun a => F a y) (fun a => S a y (d.frame y i)) :=
    selected_frame_tensor_eq d F S y (d.frame y i) j T
      (fun a => ((hFS a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      (((he j).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) hFrame
      (fun a => (hS a y hy).1 (d.frame y i)) hT
  have hLow := frameTensorOperatorCombination_compatible d y (d.frame y i) j
    (fun a => F a y) (fun a => S a y (d.frame y i)) (fun a => L a y) LC
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num))
    (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
    (fun a => (hE a y hy).1) (fun a => (hD a).1)
  have hHigh := frameTensorOperatorCombination_compatible d y (d.frame y i) j
    (fun a => H a y) HC (fun a => F a y) (fun a => S a y (d.frame y i))
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num))
    (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))
    (fun a => (hE a y hy).2.1) (fun a => (hD a).2.1)
  have hr : 0 ≤ d.radius y := (hd.2.2.2.2.1.2 y hy).1.le
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβ0 : 0 ≤ beta d.γ d.radius y := zero_le_one.trans hβ
  have hScale : CD*d.radius y*beta d.γ d.radius y*‖d.frame y i‖ ≤
      CD*K*d.radius y*beta d.γ d.radius y :=
    (mul_le_mul_of_nonneg_left (heN i) (by positivity)).trans_eq (by ring)
  have hLCN (a : I) : ‖LC a‖ ≤ CD*K*d.radius y*beta d.γ d.radius y := by
    have hRaw : ‖LC a‖ ≤ CD*d.radius y*beta d.γ d.radius y*‖d.frame y i‖ := by
      simpa only [norm_axis,mul_one] using (hD a).2.2.1
    exact hRaw.trans hScale
  have hHCN (a : I) : ‖HC a‖ ≤ CD*K*d.radius y*beta d.γ d.radius y := by
    have hRaw : ‖HC a‖ ≤ CD*d.radius y*beta d.γ d.radius y*‖d.frame y i‖ := by
      simpa only [norm_axis,mul_one] using (hD a).2.2.2
    exact hRaw.trans hScale
  have hLFN (a : I) : ‖L a y‖ ≤ CF*d.radius y := by
    simpa only [norm_axis,mul_one] using (hE a y hy).2.2.1
  have hHFN (a : I) : ‖H a y‖ ≤ CF*d.radius y := by
    simpa only [norm_axis,mul_one] using (hE a y hy).2.2.2
  have hConn : ∀ a : I,|(connection d.γ y (d.frame y i) (d.frame y j)) a| ≤ CΓ*K^2 :=
    fun a => hGeometry.2 i j a
  have hFrameCoeff : ∀ a : I,|d.frame y j a| ≤ K :=
    fun a => hd.1.1.frame_component_abs_le hK d.frame (hSub hy) hFrame j a
  have hBudget : 3*K*(CD*K*d.radius y*beta d.γ d.radius y)+3*(CΓ*K^2)*(CF*d.radius y) ≤
      CE*d.radius y*beta d.γ d.radius y := by
    simpa only [CE] using frame_tensor_radius_beta_budget K CΓ CF CD
      (d.radius y) (beta d.γ d.radius y) hΓ hCF hr hβ
  refine ⟨Lo,Hi,?_,?_,?_,?_⟩
  · exact (congrArg (fun U : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp U) hMid).trans hLow
  · exact hHigh.trans (congrArg (fun U : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
      U.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) hMid.symm)
  · exact (norm_frameTensorOperatorCombination_le d y (d.frame y i) j (fun a => L a y) LC
      hK0 (by positivity : 0 ≤ CΓ*K^2) hFrameCoeff hConn hLFN hLCN).trans hBudget
  · exact (norm_frameTensorOperatorCombination_le d y (d.frame y i) j (fun a => H a y) HC
      hK0 (by positivity : 0 ≤ CΓ*K^2) hFrameCoeff hConn hHFN hHCN).trans hBudget
end ShrinkingSpheres

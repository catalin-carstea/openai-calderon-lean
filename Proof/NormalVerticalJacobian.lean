import Proof.UniformNormalJacobiBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres

def normalVerticalJacobian (expMap : X × X → X) (y v : X) : X →L[ℝ] X :=
  (fderiv ℝ expMap (y,v)).comp (ContinuousLinearMap.inr ℝ X X)

lemma NormalCoordinates.position_parameter_derivative {Y Ω : Set X} {g : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v u : X) (t : ℝ) (hv : t • v ∈ disk g y (R y)) :
    fderiv ℝ (normalGeodesicPosition expMap y) (v,t) (u,0) =
      normalVerticalJacobian expMap y (t • v) (t • u) := by
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hE : HasFDerivAt expMap (fderiv ℝ expMap (y,t • v)) (y,t • v) :=
    ((hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,hv⟩))).differentiableAt (by simp)).hasFDerivAt
  have hF : HasFDerivAt (fun p : X × ℝ => p.1) (ContinuousLinearMap.fst ℝ X ℝ) (v,t) := hasFDerivAt_fst
  have hS : HasFDerivAt (fun p : X × ℝ => p.2) (ContinuousLinearMap.snd ℝ X ℝ) (v,t) := hasFDerivAt_snd
  have hScaled : HasFDerivAt (fun p : X × ℝ => p.2 • p.1)
      (t • ContinuousLinearMap.fst ℝ X ℝ+(ContinuousLinearMap.snd ℝ X ℝ).smulRight v) (v,t) := hS.smul hF
  have hInput := (hasFDerivAt_const (𝕜:=ℝ) y (v,t)).prodMk hScaled
  have hd := hE.comp (v,t) hInput
  have hh := congrArg (fun L : (X × ℝ) →L[ℝ] X => L (u,0)) hd.fderiv
  change fderiv ℝ (normalGeodesicPosition expMap y) (v,t) (u,0) =
    fderiv ℝ expMap (y,t • v) (0,t • u+(0:ℝ) • v) at hh
  simpa only [zero_smul,add_zero,normalVerticalJacobian,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply] using hh

lemma NormalCoordinates.variation_position_eq {Y Ω : Set X} {g : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v u : X) (t : ℝ) (hv : t • v ∈ disk g y (R y)) :
    (normalVelocityVariation expMap y v u t).1 = normalVerticalJacobian expMap y (t • v) (t • u) := by
  have hPhase := hN.contDiffAt_phase hy (v,t) hv
  have hd := (hPhase.differentiableAt (by simp)).hasFDerivAt.fst
  have hh := congrArg (fun L : (X × ℝ) →L[ℝ] X => L (u,0)) hd.fderiv
  have hfst : fderiv ℝ (normalGeodesicPosition expMap y) (v,t) (u,0) =
      (normalVelocityVariation expMap y v u t).1 := hh
  exact hfst.symm.trans (hN.position_parameter_derivative hy v u t hv)

/-- Uniform operator norm of the vertical differential of the actual normal endpoint,
    with an explicit constant from the frozen background budgets. -/
theorem Background.normalVerticalJacobian_bound {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 2 ≤ m)
    {expMap : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    {y : X} (hy : y ∈ Y) (v : X) (hv : v ∈ interior (disk g y (R y))) (hv1 : ‖v‖ ≤ 1) :
    ‖normalVerticalJacobian expMap y v‖ ≤ Real.exp (normalVariationBudget hm K M) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro u
  have ht : (1:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hJ := h.normal_velocity_variation_bound hΩ hK hm hN hy v u hv hv1 ht
  have hvd : (1:ℝ) • v ∈ disk g y (R y) := by simpa only [one_smul] using interior_subset hv
  have he := hN.variation_position_eq hy v u 1 hvd
  simp only [one_smul] at he
  have hh := (norm_fst_le (normalVelocityVariation expMap y v u 1)).trans hJ
  rw [he] at hh
  simpa only [mul_one,one_mul,mul_comm] using hh

end ShrinkingSpheres

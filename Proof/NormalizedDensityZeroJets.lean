import Proof.NormalizedJointDensityJets
import Proof.CanonicalFirstRadialCorrection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

def firstDensityLogDifferential (g g₁ : MetricField) (y : X) : X →L[ℝ] ℝ :=
  (firstMetricDensityFactor g g₁ y)⁻¹ • fderiv ℝ (firstMetricDensityFactor g g₁) y

theorem Background.firstDensityLogDifferential_eq_depth {Ω : Set X} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hΩ : IsOpen Ω) {y : X} (hy : y ∈ Ω) :
    firstDensityLogDifferential g g₁ y = -fderiv ℝ (firstMetricConformalDepth g g₁) y := by
  let c := firstMetricDensityFactor g g₁ y
  have ht := (h.firstMetricConformalDepth_smooth hK).contDiffAt (hΩ.mem_nhds hy)
  have hd : fderiv ℝ (firstMetricDensityFactor g g₁) y = c • (-fderiv ℝ (firstMetricConformalDepth g g₁) y) :=
    ((ht.differentiableAt (by simp)).hasFDerivAt.neg.exp).fderiv
  unfold firstDensityLogDifferential
  rw [hd,smul_smul,inv_mul_cancel₀ (firstMetricDensityFactor_pos g g₁ y).ne',one_smul]

lemma Background.firstDensityLogDifferential_smooth {Ω : Set X} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hΩ : IsOpen Ω) :
    ContDiffOn ℝ ∞ (firstDensityLogDifferential g g₁) Ω := by
  have hc := h.firstMetricDensityFactor_smooth hK
  exact (hc.inv (fun y _ => (firstMetricDensityFactor_pos g g₁ y).ne')).smul
    (hc.fderiv_of_isOpen (m:=∞) hΩ (by simp))

lemma NormalCoordinates.normalized_joint_density_zero {Y Ω : Set X} {g g₁ : MetricField}
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R)
    {y : X} (hy : y ∈ Y) : normalizedJointFirstDensityFactor g g₁ E (y,0) = 1 := by
  simp only [normalizedJointFirstDensityFactor,hN.exp_zero hy]
  exact div_self (firstMetricDensityFactor_pos g g₁ y).ne'

/-- The actual normalized scalar first vertical jet is the same canonical
    logarithmic differential used by the analytic radial first model. -/
theorem Background.normalized_joint_density_vertical_zero {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R)
    {y : X} (hy : y ∈ Y) (b : X) :
    fderiv ℝ (normalizedJointFirstDensityFactor g g₁ E) (y,0) (0,b) = firstDensityLogDifferential g g₁ y b := by
  let c := firstMetricDensityFactor g g₁
  have hyΩ := hN.center_mem hy
  have hc := h.firstMetricDensityFactor_smooth hK
  have hci := hc.inv (fun x _ => (firstMetricDensityFactor_pos g g₁ x).ne')
  have hExp := hN.hasFDerivAt_zero hY hy e (h.2.2.2.2.2.2.2 y hyΩ)
  have hC : HasFDerivAt c (fderiv ℝ c y) (E (y,0)) := by
    rw [hN.exp_zero hy]
    exact (hc.contDiffAt (hΩ.mem_nhds hyΩ)).differentiableAt (by simp) |>.hasFDerivAt
  have hA := hC.comp (y,0) hExp
  have hB := ((hci.contDiffAt (hΩ.mem_nhds hyΩ)).differentiableAt (by simp)).hasFDerivAt.comp
    (y,(0:X)) (hasFDerivAt_fst (𝕜:=ℝ) (p:=(y,(0:X))))
  have hProd := hA.mul hB
  have hFun : normalizedJointFirstDensityFactor g g₁ E = fun p => c (E p)*(c p.1)⁻¹ := by
    funext p
    exact div_eq_mul_inv _ _
  rw [hFun]
  have hh := congrArg (fun L : (X × X) →L[ℝ] ℝ => L (0,b)) hProd.fderiv
  have hFst : (ContinuousLinearMap.fst ℝ X X) ((0:X),b) = 0 := rfl
  have hSnd : (ContinuousLinearMap.snd ℝ X X) ((0:X),b) = b := rfl
  simp only [Function.comp_def,_root_.add_apply,ContinuousLinearMap.comp_apply,_root_.smul_apply,
    hFst,hSnd,map_zero,zero_add,hN.exp_zero hy] at hh
  exact hh.trans (by
    change c y • (0:ℝ)+(c y)⁻¹ • fderiv ℝ c y b = (c y)⁻¹*fderiv ℝ c y b
    simp only [smul_eq_mul,mul_zero,zero_add])

lemma Background.firstDensityLogCovector_eq_differential {Ω : Set X} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {d : Data} (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K)
    (hΩ : IsOpen Ω) {y : X} (hy : y ∈ Ω) :
    firstDensityLogCovector d y = (firstDensityLogDifferential d.γ d.g₁ y).comp (frameVectorLinear d.frame y) := by
  rw [h.firstDensityLogCovector_eq_depth hΩ hK hy,h.firstDensityLogDifferential_eq_depth hK hΩ hy]
  rfl

end ShrinkingSpheres

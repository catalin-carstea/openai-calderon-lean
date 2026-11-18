import Proof.ModelAdjointDefectCoefficient
import Proof.CoarsePotentialSmoothParts
import Proof.HessianCoordinateBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma contDiffOn_modelAdjointDefectFirstCoarseL {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y) (a : X) :
    ContDiffOn ℝ ∞ (modelAdjointDefectFirstCoarseL d a) Y := by
  have hH := contDiffOn_hessianBilinear_of_smooth hY hlog (hg.contDiffOn_connectionBilinear hY hK)
  exact ContDiffOn.sum (fun i _ => ((hH.clm_apply contDiffOn_const).clm_apply (he i)).smul contDiffOn_const)

lemma Profile.logRadius_hessian_axis_frame_bound {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 1 ≤ K)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y d.γ d.frame d.radius floor c₀ Cj)
    {y : X} (hy : y ∈ Y)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) (a j : I) :
    |hessianBilinear d.γ (fun x => Real.log (d.radius x)) y (axis a) (d.frame y j)| ≤
      3*K*|Cj 2| *(beta d.γ d.radius y)^2 := by
  let H := hessianBilinear d.γ (fun x => Real.log (d.radius x)) y
  let J := |Cj 2| *(beta d.γ d.radius y)^2
  have hJ : 0 ≤ J := by dsimp only [J];positivity
  have hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y := hp.1.log (fun x hx => (hp.2 x hx).1.ne')
  have hDLog : DifferentiableAt ℝ (fderiv ℝ (fun x => Real.log (d.radius x))) y :=
    ((hlog.fderiv_of_isOpen (m:=∞) hY (by simp)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hJet : jetNorm d.γ d.frame (fun x => Real.log (d.radius x)) 2 y ≤ J :=
    ((hp.2 y hy).2.2.2 2 (by norm_num)).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
  have hH (k : I) : |H (d.frame y k) (d.frame y j)| ≤ J := by
    rw [hessianBilinear_eq_coordinate d.γ (fun x => Real.log (d.radius x)) y hDLog]
    exact (frameHessian_abs_le_jetNorm d.γ d.frame _ y k j).trans hJet
  have hExpand : H (axis a) (d.frame y j)=
      ∑ k : I,metricPair d.γ y (axis a) (d.frame y k)*H (d.frame y k) (d.frame y j) := by
    have hh := congrArg (H.flip (d.frame y j)) ((frameBasis d.γ d.frame y hFrame).sum_repr (axis a))
    simpa only [map_sum,map_smul,frameBasis_apply,frameBasis_repr,ContinuousLinearMap.flip_apply,smul_eq_mul] using hh.symm
  change |H (axis a) (d.frame y j)| ≤ _
  rw [hExpand]
  calc
    _ ≤ ∑ k : I,|metricPair d.γ y (axis a) (d.frame y k)*H (d.frame y k) (d.frame y j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : I,K*J := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (hg.frame_coordinate_abs_bound hK d.frame hy hFrame a k) (hH k)
        (abs_nonneg _) (zero_le_one.trans hK)
    _ = _ := by simp only [Fin.sum_univ_three,J];ring

theorem Profile.norm_modelAdjointDefectFirstCoarseL_axis_le {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 1 ≤ K)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y d.γ d.frame d.radius floor c₀ Cj)
    {y : X} (hy : y ∈ Y)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) (a : I) :
    ‖modelAdjointDefectFirstCoarseL d (axis a) y‖ ≤
      (3*K*|Cj 2| *(∑ i : I,‖flatOneLoweringL i‖))*(beta d.γ d.radius y)^2 := by
  calc
    _ ≤ ∑ i : I,‖hessianBilinear d.γ (fun x => Real.log (d.radius x)) y (axis a) (d.frame y i) • flatOneLoweringL i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : I,(3*K*|Cj 2| *(beta d.γ d.radius y)^2)*‖flatOneLoweringL i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hp.logRadius_hessian_axis_frame_bound hY d hg hK hy hFrame a i) (norm_nonneg _)
    _ = _ := by rw [←Finset.mul_sum];ring

end ShrinkingSpheres

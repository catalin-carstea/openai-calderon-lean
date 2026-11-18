import Proof.PhysicalCorrectionCoframeGraph
import Proof.HalfCovariantDirectionLinear
import Proof.CovariantHalfCoarseBridge
import Proof.BalancedCoarsePotential
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def physicalFirstCorrectionHalfBudget (K M0 M1 M2 C2 : ℝ) : ℝ :=
  3*K*(firstCorrectionGradeBound (-(1/2:ℝ)) K M1+firstCorrectionGradeBound (1/2:ℝ) K M1+
    physicalFirstCorrectionJetBudget K M0 M1 M2 C2)

lemma physicalFirstCorrectionHalfBudget_nonneg (K M0 M1 M2 C2 : ℝ) (hK : 0 ≤ K) :
    0 ≤ physicalFirstCorrectionHalfBudget K M0 M1 M2 C2 :=
  mul_nonneg (mul_nonneg (by norm_num) hK)
    (add_nonneg (add_nonneg (firstCorrectionGradeBound_nonneg _ _ _) (firstCorrectionGradeBound_nonneg _ _ _))
      (physicalFirstCorrectionJetBudget_nonneg _ _ _ _ _ hK))

/-- Genuine physical-axis correction endpoints, with common coefficient
    and literal covariant derivative bounds. Frame derivatives have canceled
    before any quantitative estimate is applied. -/
theorem Admissible.physicalFirstCorrection_half_data {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (b : I) :
    let Q := physicalFirstCorrectionHalfBudget K (M 0) (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2)
    ContDiffOn ℝ ∞ (fun x => physicalFirstCorrectionHalfL d x (axis b)) Y ∧
      ContDiffOn ℝ ∞ (fun x => physicalFirstCorrectionHigherL d x (axis b)) Y ∧
      ∀ x ∈ Y,
        ‖physicalFirstCorrectionHalfL d x (axis b)‖ ≤ Q ∧
        ‖physicalFirstCorrectionHigherL d x (axis b)‖ ≤ Q ∧
        ∀ i : I,‖halfOperatorCovariantDerivativeL d
          (fun y => physicalFirstCorrectionHalfL d y (axis b))
          (fun y => physicalFirstCorrectionHigherL d y (axis b)) x (axis i)‖ ≤ Q := by
  let Glo := firstCorrectionGradeBound (-(1/2:ℝ)) K (M ⟨1,by omega⟩)
  let Ghi := firstCorrectionGradeBound (1/2:ℝ) K (M ⟨1,by omega⟩)
  let CJ := physicalFirstCorrectionJetBudget K (M 0) (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2)
  let Q := physicalFirstCorrectionHalfBudget K (M 0) (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2)
  have hK0 := zero_lt_one.trans_le hK
  have hGlo : 0 ≤ Glo := firstCorrectionGradeBound_nonneg _ _ _
  have hGhi : 0 ≤ Ghi := firstCorrectionGradeBound_nonneg _ _ _
  have hCJ : 0 ≤ CJ := physicalFirstCorrectionJetBudget_nonneg _ _ _ _ _ hK0.le
  have hloQ : 3*K*Glo ≤ Q := mul_le_mul_of_nonneg_left (by linarith only [hGhi,hCJ]) (by positivity)
  have hhiQ : 3*K*Ghi ≤ Q := mul_le_mul_of_nonneg_left (by linarith only [hGlo,hCJ]) (by positivity)
  have hJQ : 3*K*CJ ≤ Q := mul_le_mul_of_nonneg_left (by linarith only [hGlo,hGhi]) (by positivity)
  have hLS : ContDiffOn ℝ ∞ (fun x => physicalFirstCorrectionHalfL d x (axis b)) Y :=
    (hd.contDiffOn_physicalFirstCorrectionAtL hY hΩ hK0 (-(1/2:ℝ)) (axis b)).clm_comp contDiffOn_const
  have hHS : ContDiffOn ℝ ∞ (fun x => physicalFirstCorrectionHigherL d x (axis b)) Y :=
    (hd.contDiffOn_physicalFirstCorrectionAtL hY hΩ hK0 (1/2:ℝ) (axis b)).clm_comp contDiffOn_const
  have hCS : ContDiffOn ℝ ∞ (physicalFirstCorrectionCoarseFamily d (axis b)) Y :=
    (hd.contDiffOn_physicalFirstCorrectionAtL hY hΩ hK0 0 (axis b)).clm_comp contDiffOn_const
  refine ⟨hLS,hHS,?_⟩
  intro x hx
  have hLo : ‖physicalFirstCorrectionHalfL d x (axis b)‖ ≤ 3*K*Glo :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (((mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le _ _ _)
        (norm_nonneg (physicalFirstCorrectionAtL (-(1/2:ℝ)) d x (axis b)))).trans_eq (mul_one _)).trans
          (hd.norm_physicalFirstCorrectionAtL_axis_le hΩ hm hK hf hε hε1 _ hx b))
  have hHi : ‖physicalFirstCorrectionHigherL d x (axis b)‖ ≤ 3*K*Ghi :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (((mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le _ _ _)
        (norm_nonneg (physicalFirstCorrectionAtL (1/2:ℝ) d x (axis b)))).trans_eq (mul_one _)).trans
          (hd.norm_physicalFirstCorrectionAtL_axis_le hΩ hm hK hf hε hε1 _ hx b))
  have hFrame := hd.1.2.2.2.2.2.2.2 x (hd.2.1.center_mem hx)
  have hD (i : I) : ‖halfOperatorCovariantDerivativeL d
      (fun y => physicalFirstCorrectionHalfL d y (axis b))
      (fun y => physicalFirstCorrectionHigherL d y (axis b)) x (d.frame x i)‖ ≤ CJ := by
    have hGraph := hd.physicalFirstCorrection_covariant_graph hY hΩ hK0 hx (d.frame x i) (axis b)
    have hEq := halfOperatorCovariantDerivativeL_eq_coarse
      (physicalFirstCorrectionCoarseFamily d (axis b))
      (fun y => physicalFirstCorrectionHalfL d y (axis b))
      (fun y => physicalFirstCorrectionHigherL d y (axis b))
      (physicalFirstCorrectionCovariantJetL d x (d.frame x i) (axis b))
      ((hCS.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp))
      ((hLS.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp))
      (Eventually.of_forall (fun y => physicalFirstCorrectionHalfL_coarse d y (axis b)))
      (physicalFirstCorrectionHigherL_coarse d x (axis b)) hGraph
    rw [hEq]
    exact (norm_balancedCoarsePotentialL_le _).trans
      (hd.norm_physicalFirstCorrectionCovariantJetL_frame_le hY hΩ hm hK hf hε hε1 hx i b)
  have hSub : Y ⊆ Ω := fun y hy => hd.2.1.center_mem hy
  have hg : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun y hy => hd.1.1.2 y (hSub hy)⟩
  refine ⟨hLo.trans hloQ,hHi.trans hhiQ,?_⟩
  intro i
  exact (norm_halfOperatorCovariantDerivativeL_axis_le d hg hK hx hFrame _ _ CJ hD i).trans hJQ
end ShrinkingSpheres

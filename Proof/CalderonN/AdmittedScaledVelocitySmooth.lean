module

public import Proof.CalderonN.AdmittedNormalBallPullback
public import Proof.CalderonN.NormalTraceVelocity

import Proof.CalderonN.MetricCalculus
import Mathlib.Tactic

/-! Local smoothness of the exact scaled physical moving velocity
on the normal chart supplied by the frozen admissibility condition. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem exists_admitted_scaledVelocity_smooth
    {Y Ω : Set (X dim)} {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    {y : X dim} (hy : y ∈ Y) (hrρ : 2*d.radius y < ρ) (a : X dim) (b : ℝ) :
    ∃ V : Set (X dim), IsOpen V ∧ closedBall (0 : X dim) 1 ⊆ V ∧
      ContDiffOn ℝ ∞ (fun z => scaledNormalTraceVelocity d.γ d.expMap d.frame y (d.radius y) b z a) V ∧
      ∀ z ∈ V, (coordinateMatrix (normalizedBallDerivative d.expMap d.frame y (d.radius y) z)).det ≠ 0 := by
  let r := d.radius y
  let F₀ := frameVectorLinear d.frame y
  let N (z : X dim) := coordinateMatrix (normalizedBallDerivative d.expMap d.frame y r z)
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have he := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  obtain ⟨V,hV,hCV,hVU,F,hF,_,_,_,hBij,hDer,_⟩ := exists_admitted_normalBallChart_extension hd hy hrρ
  have hScale (z : X dim) (hz : z ∈ V) : coordinateJacobian F z = r • N z := by
    unfold coordinateJacobian
    rw [hDer z hz]
    ext i j
    simp only [N,coordinateMatrix_apply,_root_.smul_apply,Matrix.smul_apply,PiLp.smul_apply,smul_eq_mul,r]
  have hEntry (i j : I dim) : ContDiffOn ℝ ∞ (fun z => N z i j) V := by
    have h : ContDiffOn ℝ ∞ (fun z => r⁻¹*coordinateJacobian F z i j) V :=
      contDiffOn_const.mul (contDiff_coordinateJacobian_entry F hF i j).contDiffOn
    refine h.congr (fun z hz => ?_)
    rw [hScale z hz,Matrix.smul_apply,smul_eq_mul,← mul_assoc,inv_mul_cancel₀ hr.ne',one_mul]
  have hDet (z : X dim) (hz : z ∈ V) : (N z).det ≠ 0 := by
    intro h
    have hh := coordinateJacobian_det_ne_zero (hBij z hz)
    rw [hScale z hz,Matrix.det_smul,h,mul_zero] at hh
    exact hh rfl
  have hVel (z : X dim) (hz : z ∈ V) : r • F₀ z ∈ disk d.γ y (max ρ r) := by
    change metricPair d.γ y (r • F₀ z) (r • F₀ z) ≤ (max ρ r)^2
    rw [show F₀ z = frameVector d.frame y z from frameVectorLinear_apply d.frame y z,
      metricPair_scaled_frameVector d.γ d.frame y he,← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    have hzN := (mem_ball_zero_iff.mp (hVU hz)).le
    exact ((mul_le_mul_of_nonneg_left hzN hr.le).trans_eq (mul_comm _ _)).trans
      (hrρ.le.trans (le_max_left _ _))
  let p (z : X dim) := (y,r • F₀ z)
  let L (z : X dim) := (a,b • F₀ z-r • connection d.γ y a (F₀ z))
  let c (z : X dim) := fderiv ℝ d.expMap (p z) (L z)
  have hP : ContDiff ℝ ∞ p := contDiff_const.prodMk (F₀.contDiff.const_smul r)
  have hL : ContDiff ℝ ∞ L := by
    have h : ContDiff ℝ ∞ (fun z => connection d.γ y a (F₀ z)) := by
      simp only [← connectionBilinear_apply]
      exact
      (connectionBilinear d.γ y a).contDiff.comp F₀.contDiff
    exact contDiff_const.prodMk ((F₀.contDiff.const_smul b).sub (h.const_smul r))
  obtain ⟨Z,hZ,hTube,hEZ⟩ := hd.2.1.1
  have hC : ContDiffOn ℝ ∞ c V := by
    intro z hz
    have hp : p z ∈ Z := hTube ⟨hy,hVel z hz⟩
    have hdif := (hEZ.contDiffAt (hZ.mem_nhds hp)).fderiv_right (m:=∞) (by simp)
    exact ((hdif.comp z hP.contDiffAt).clm_apply hL.contDiffAt).contDiffWithinAt
  refine ⟨V,hV,(closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 3/2)).trans hCV,?_,hDet⟩
  apply (contDiffOn_piLp 2).mpr
  intro i
  have hh : ContDiffOn ℝ ∞ (fun z => ∑ j, (N z)⁻¹ i j*c z j) V :=
    ContDiffOn.sum fun j _ =>
      (contDiffOn_inv_entry_of_entries hEntry (fun z hz => hDet z hz) i j).mul
        ((EuclideanSpace.proj (𝕜:=ℝ) j).contDiff.comp_contDiffOn hC)
  refine hh.congr (fun z _ => ?_)
  simp only [scaledNormalTraceVelocity,PiLp.toLp_apply,Matrix.mulVec,dotProduct,N,c,p,L,
    r,F₀,frameVectorLinear_apply]

end CalderonN

module

public import Proof.CalderonN.NormalBallHarmonic
public import Proof.CalderonN.ActualConormalRadialRow
public import Proof.CalderonN.NormalizedBallMetric

import Proof.CalderonN.NormalCenterBoundaryChainRule
import Proof.CalderonN.GreenWeak
import Proof.CalderonN.ConstantMetricScale

import Proof.CalderonN.CompactSmoothExtension
import Proof.CalderonN.NormalMapDerivativeTaylor
import Proof.CalderonN.NormalizedVelocityAtZero
import Mathlib.Tactic

/-! Extend only the rescaled normal chart at the selected center.
Its physical metric and the exact Dirichlet tests are preserved on a
neighborhood of the closed ball. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5600000
set_option maxSynthPendingDepth 31
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Metric
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem exists_admitted_normalBallChart_extension
    {Y Ω : Set (X dim)} {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    {y : X dim} (hy : y ∈ Y) (hrρ : 2*d.radius y < ρ) :
    ∃ V : Set (X dim), IsOpen V ∧ closedBall (0 : X dim) (3/2) ⊆ V ∧ V ⊆ ball (0 : X dim) 2 ∧
      ∃ F : X dim → X dim, ContDiff ℝ ∞ F ∧
        EqOn F (normalBallChartMap d.expMap d.frame y (d.radius y)) V ∧
        InjOn F V ∧ MapsTo F V Ω ∧ (∀ z ∈ V, Function.Bijective (fderiv ℝ F z)) ∧
        (∀ z ∈ V, fderiv ℝ F z = d.radius y • normalizedBallDerivative d.expMap d.frame y (d.radius y) z) ∧
        EqOn (pullbackMetric d.g₁ F)
          ((d.radius y)^2 • normalizedBallMetric d.g₁ d.expMap d.frame y (d.radius y)) V := by
  let r := d.radius y
  let U := ball (0 : X dim) 2
  let T := frameVectorLinear d.frame y
  let D := r • T
  let F₀ := normalBallChartMap d.expMap d.frame y r
  have hDval (z : X dim) : D z = r • frameVector d.frame y z := by
    change r • frameVectorLinear d.frame y z = _
    rw [frameVectorLinear_apply]
  have hF₀ : F₀ = (fun v => d.expMap (y,v)) ∘ D := by
    funext z
    change d.expMap (y,r • frameVector d.frame y z) = d.expMap (y,D z)
    rw [hDval]
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have he := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hT : Function.Bijective T := by
    rw [show ⇑T = frameVector d.frame y from funext (frameVectorLinear_apply d.frame y)]
    exact bijective_frameVector d.γ d.frame y he
  have hD : Function.Bijective D := by
    refine ⟨fun a b h => hT.1 (smul_right_injective (X dim) hr.ne' h),?_⟩
    intro z
    obtain ⟨x,hx⟩ := hT.2 (r⁻¹ • z)
    exact ⟨x,by change r • T x = z; rw [hx,smul_inv_smul₀ hr.ne']⟩
  have hVel (z : X dim) (hz : z ∈ U) : D z ∈ disk d.γ y (max ρ r) := by
    change metricPair d.γ y (r • frameVectorLinear d.frame y z)
      (r • frameVectorLinear d.frame y z) ≤ _
    rw [frameVectorLinear_apply,metricPair_scaled_frameVector d.γ d.frame y he]
    have hzN := (mem_ball_zero_iff.mp hz).le
    have h : r*‖z‖ ≤ max ρ r := ((mul_le_mul_of_nonneg_left hzN hr.le).trans_eq (mul_comm _ _)).trans
      (hrρ.le.trans (le_max_left _ _))
    exact (by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h 2)
  obtain ⟨J,hJ,hTube,hE⟩ := hd.2.1.1
  have hF (z : X dim) (hz : z ∈ U) : ContDiffAt ℝ ∞ F₀ z := by
    have hE' : ContDiffAt ℝ ∞ d.expMap (y,D z) := hE.contDiffAt
      (hJ.mem_nhds (hTube ⟨hy,hVel z hz⟩))
    have hArg : ContDiffAt ℝ ∞ (fun w : X dim => (y,D w)) z :=
      contDiffAt_const.prodMk D.contDiff.contDiffAt
    have hComp : ContDiffAt ℝ ∞ (d.expMap ∘ fun w : X dim => (y,D w)) z :=
      hE'.comp z hArg
    rw [hF₀]
    exact hComp
  have hFD (z : X dim) (hz : z ∈ U) :
      fderiv ℝ F₀ z = (normalVerticalJacobian d.expMap y (D z)).comp D := by
    rw [hF₀]
    exact ((hd.2.1.hasFDerivAt_velocity_slice hy (D z) (hVel z hz)).comp z D.hasFDerivAt).fderiv
  obtain ⟨F,hFsm,_,V,hV,hCV,hVU,hEq⟩ := exists_contDiff_extension_near_compact
    (U:=U) isOpen_ball (isCompact_closedBall (0 : X dim) (3/2))
    (closedBall_subset_ball (by norm_num : (3/2:ℝ) < 2)) (fun z hz => (hF z hz).contDiffWithinAt)
  have hGerm (z : X dim) (hz : z ∈ V) : F =ᶠ[𝓝 z] F₀ := by
    filter_upwards [hV.mem_nhds hz] with w hw using hEq hw
  have hDer (z : X dim) (hz : z ∈ V) :
      fderiv ℝ F z = r • normalizedBallDerivative d.expMap d.frame y r z := by
    have hL : frameVectorL (d.frame y) = T := by
      ext1 w
      rw [frameVectorL_apply_frame,show T w = frameVectorLinear d.frame y w from rfl,frameVectorLinear_apply]
    rw [(hGerm z hz).fderiv_eq,hFD z (hVU hz)]
    have hh := (hd.2.1.hasFDerivAt_velocity_slice hy (D z) (hVel z (hVU hz))).fderiv
    change fderiv ℝ (fun v => d.expMap (y,v)) (D z) = _ at hh
    rw [normalizedBallDerivative,← hDval z,hh,hL,show D = r • T from rfl,ContinuousLinearMap.comp_smul]
  refine ⟨V,hV,hCV,hVU,F,hFsm,hEq,?_,?_,?_,hDer,?_⟩
  · intro z hz w hw hzw
    rw [hEq hz,hEq hw,hF₀] at hzw
    exact hD.1 ((hd.2.1.2 y hy).2.1 (hVel z (hVU hz)) (hVel w (hVU hw)) hzw)
  · intro z hz
    rw [hEq hz,hF₀]
    exact ((hd.2.1.2 y hy).2.2 (D z) (hVel z (hVU hz))).1
  · intro z hz
    rw [(hGerm z hz).fderiv_eq,hFD z (hVU hz)]
    exact (hd.2.1.normalVerticalJacobian_isInvertible hy (D z) (hVel z (hVU hz))).bijective.comp hD
  · intro z hz
    have hCoord : coordinateJacobian F z =
        r • coordinateMatrix (normalizedBallDerivative d.expMap d.frame y r z) := by
      unfold coordinateJacobian
      rw [hDer z hz]
      ext i j
      simp only [coordinateMatrix_apply,smul_apply,Matrix.smul_apply,PiLp.smul_apply,smul_eq_mul]
    change pullbackMetric d.g₁ F z = r^2 • normalizedBallMetric d.g₁ d.expMap d.frame y r z
    rw [pullbackMetric,hCoord,hEq hz]
    simp only [normalizedBallMetric,F₀,Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,pow_two]

/-- The protected harmonic test, pulled back through the selected local
chart, solves the actual first-metric equation on the unit ball. -/
theorem harmonicOnBall_admitted_normalChart
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X dim} (hy : y ∈ Y) (hrρ : 2*d.radius y < ρ) {u : X dim → ℝ}
    (hu : HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u) :
    let F := normalBallChartMap d.expMap d.frame y (d.radius y)
    let g := normalizedBallMetric d.g₁ d.expMap d.frame y (d.radius y)
    ∃ U : Set (X dim), IsOpen U ∧ closedBall (0 : X dim) 1 ⊆ U ∧ SmoothMetric U g ∧
      ContDiffOn ℝ ∞ (u ∘ F) U ∧ ∀ z ∈ ball (0 : X dim) 1, laplace g (u ∘ F) z = 0 := by
  let C := closedBall (0 : X dim) 1
  let r := d.radius y
  let F₀ := normalBallChartMap d.expMap d.frame y r
  let g := normalizedBallMetric d.g₁ d.expMap d.frame y r
  let N := closedBallImage d.γ d.expMap d.radius y
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have he := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  obtain ⟨V,hV,hV₀,_,F,hF,hEq,hInj,hMap,hBij,_,hP⟩ := exists_admitted_normalBallChart_extension hd hy hrρ
  have hCV : C ⊆ V := (closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 3/2)).trans hV₀
  have hFC : F '' C = N := by
    rw [image_congr (hEq.mono hCV)]
    exact (closedBallImage_eq_scaledFrameImage d.γ d.expMap d.frame y he hr).symm
  have hOpen : IsOpen (F '' ball (0 : X dim) 1) :=
    (exists_smooth_inverse_on_image isOpen_ball hF.contDiffOn
      (hInj.mono (ball_subset_closedBall.trans hCV))
      (fun z hz => hBij z (hCV (ball_subset_closedBall hz)))).1
  have hInt : F '' ball (0 : X dim) 1 ⊆ interior N :=
    hOpen.subset_interior_iff.mpr ((image_mono ball_subset_closedBall).trans_eq hFC)
  obtain ⟨S,hS,hNS,huS⟩ := hu.1
  let U := V ∩ F ⁻¹' S
  have hU : IsOpen U := hV.inter (hS.preimage hF.continuous)
  have hCU : C ⊆ U := by
    intro z hz
    refine ⟨hCV hz,hNS ?_⟩
    change F z ∈ N
    rw [← hFC]
    exact mem_image_of_mem F hz
  have hUV : MapsTo F U (Ω ∩ S) := fun z hz => ⟨hMap hz.1,hz.2⟩
  have hG : SmoothMetric (Ω ∩ S) d.g₁ := ⟨
    fun i j => (hd.1.2.1.1 i j).mono inter_subset_left,
    fun x hx => hd.1.2.1.posDef hK hx.1⟩
  have hDet (z : X dim) (hz : z ∈ U) : (coordinateJacobian F z).det ≠ 0 :=
    coordinateJacobian_det_ne_zero (hBij z hz.1)
  have hPull := smoothMetric_pullbackMetric hG hF hUV hDet
  have hEqG : EqOn g ((r^2)⁻¹ • pullbackMetric d.g₁ F) U := by
    intro z hz
    rw [Pi.smul_apply]
    have h := hP hz.1
    change pullbackMetric d.g₁ F z = r^2 • g z at h
    rw [h,smul_smul,inv_mul_cancel₀ (pow_ne_zero 2 hr.ne'),one_smul]
  have hSm : SmoothMetric U g := by
    constructor
    · intro i j
      have hm : ContDiffOn ℝ ∞ (fun z => (r^2)⁻¹*pullbackMetric d.g₁ F z i j) U :=
        (contDiffOn_const (c:=(r^2)⁻¹)).mul (hPull.1 i j)
      refine hm.congr (fun z hz => ?_)
      exact congrArg (fun A : Mat dim => A i j) (hEqG hz)
    · intro z hz
      rw [hEqG hz]
      exact (hPull.2 z hz).smul (inv_pos.mpr (sq_pos_of_pos hr))
  have hUu : ContDiffOn ℝ ∞ (u ∘ F₀) U :=
    (huS.comp hF.contDiffOn (fun _ h => h.2)).congr
      (fun z hz => congrArg u (hEq hz.1).symm)
  refine ⟨U,hU,hCU,hSm,hUu,?_⟩
  intro z hz
  have hzU := hCU (ball_subset_closedBall hz)
  have hp := laplace_pullbackMetric (hΩ.inter hS) hG hF (huS.mono inter_subset_right) (hUV hzU) (hDet z hzU)
  have hH : laplace (pullbackMetric d.g₁ F) (u ∘ F) z = 0 :=
    hp.trans (hu.2 (F z) (hInt (mem_image_of_mem F hz)))
  change laplace g (u ∘ F₀) z = 0
  have hEqU : EqOn (u ∘ F₀) (u ∘ F) U := fun w hw => congrArg u (hEq hw.1).symm
  rw [laplace_congrOn hU hEqG hEqU hzU,
    laplace_const_smul (inv_ne_zero (pow_ne_zero 2 hr.ne')) (hPull.2 z hzU).det_pos.ne'
      (fun i j => ((hPull.1 i j).contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)),
    hH,mul_zero]

end CalderonN

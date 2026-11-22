module

public import Proof.CalderonN.UniformCenterAngularDerivative
public import Proof.CalderonN.MovingBallFamilies

import Proof.CalderonN.FrameOperators
import Proof.CalderonN.NormalizedVelocityAtZero
import Mathlib.Tactic

/-! The normalized physical velocity is the flat translation plus the
logarithmic-radius term, with a quadratic C1 spatial error. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Topology
set_option maxHeartbeats 2350000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem scaledNormalTraceVelocity_eq_center_add_radius
    {Y Ω : Set (X dim)} {γ : MetricField dim} {E : X dim × X dim → X dim} {R : X dim → ℝ}
    (hN : NormalCoordinates Y Ω γ E R) (e : Frame dim)
    {y : X dim} (hy : y ∈ Y) (hframe : ∀ k l, metricPair γ y (e y k) (e y l) = if k=l then 1 else 0)
    (s b : ℝ) (z a : X dim) (hv : s • frameVector e y z ∈ disk γ y (R y)) :
    scaledNormalTraceVelocity γ E e y s b z a =
      frameCoordinatesL γ y (e y) (normalizedParallelCenterJacobian γ E y (s • frameVector e y z) a)+b • z := by
  let v := s • frameVector e y z
  let w := frameVector e y z
  let J := normalVerticalJacobian E y v
  let C := normalParallelCenterJacobian γ E y v
  let G := normalizedParallelCenterJacobian γ E y v
  let F := frameVectorLinear e y
  let H := frameCoordinatesL γ y (e y)
  let D := normalizedBallDerivative E e y s z
  have hJ := hN.normalVerticalJacobian_isInvertible hy v hv
  have hU : Function.Bijective F := by
    simpa only [show ⇑F = frameVector e y from funext (frameVectorLinear_apply e y)] using
      bijective_frameVector γ e y hframe
  have hD : D = J.comp F := by
    obtain ⟨U,hU,hTube,hReg⟩ := hN.1
    have hP : (y,v) ∈ {q : X dim × X dim | q.1 ∈ Y ∧ q.2 ∈ disk γ q.1 (R q.1)} := ⟨hy,hv⟩
    have hE : DifferentiableAt ℝ E (y,v) :=
      (hReg.contDiffAt (hU.mem_nhds (hTube hP))).differentiableAt (by simp)
    have hd := (hE.hasFDerivAt.comp v (hasFDerivAt_prodMk_right y v)).fderiv
    change fderiv ℝ (fun x => E (y,x)) v = _ at hd
    have hFr : frameVectorL (e y) = F := by
      ext x : 1
      rw [frameVectorL_apply _ _ y,frameVectorLinear_apply e y]
      rfl
    change (fderiv ℝ (fun x => E (y,x)) v).comp (frameVectorL (e y)) = _
    rw [hd,hFr]
    rfl
  have hDbi : Function.Bijective D := by
    rw [hD]
    exact hJ.bijective.comp hU
  let Deq : X dim ≃L[ℝ] X dim := (LinearEquiv.ofBijective D.toLinearMap hDbi).toContinuousLinearEquiv
  have hDeq : Deq.toContinuousLinearMap = D := by ext x; rfl
  have hdet : (coordinateMatrix D).det ≠ 0 := by
    rw [← hDeq]
    exact coordinateMatrix_det_ne_zero Deq
  have hFH (x : X dim) : F (H x) = x := by
    have h := frameVectorL_frameCoordinatesL γ y (e y) hframe x
    rw [frameVectorL_apply _ _ y] at h
    rw [frameVectorLinear_apply]
    exact h
  have hCf : J (G a) = C a := hJ.self_apply_inverse (C a)
  have hJF (x : X dim) : J x = fderiv ℝ E (y,v) (0,x) := rfl
  have hSplit : (a,b • w-s • connection γ y a w) = (a,-connection γ y a v)+b • ((0 : X dim),w) := by
    rw [show connection γ y a v = s • connection γ y a w from by
      rw [← connectionBilinear_apply,← connectionBilinear_apply]
      exact map_smul (connectionBilinear γ y a) s w]
    simp only [Prod.smul_mk,smul_zero,Prod.mk_add_mk,add_zero]
    abel
  apply hDbi.injective
  rw [normalizedBallDerivative_scaledNormalTraceVelocity γ E e y s b z a hdet,hD]
  change fderiv ℝ E (y,v) (a,b • w-s • connection γ y a w) = J (F (H (G a)+b • z))
  have hRF : F (H (G a)+b • z) = G a+b • w := by
    rw [map_add,map_smul,hFH,show F z = w from frameVectorLinear_apply e y z]
  rw [hRF,map_add,map_smul,hCf,hJF,hSplit,map_add,map_smul,
    ← normalParallelCenterJacobian_apply]

/-- The velocity error is measured on the full fixed ball so that the
same coefficient can be used by the native Sobolev multipliers. -/
theorem uniform_actual_scaled_moving_velocity_taylor
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y, ∀ a : X dim, ∀ b : ℝ,
      let r := d.radius y
      let V := fun z => scaledNormalTraceVelocity d.γ d.expMap d.frame y r b z a
      let H := frameCoordinatesL d.γ y (d.frame y)
      let F := fun z => V z-H a-b • z
      ∀ z ∈ closedBall (0 : X dim) 1,
        ‖F z‖ ≤ C*r^2*‖a‖ ∧ ‖fderiv ℝ F z‖ ≤ C*r^2*‖a‖ := by
  obtain ⟨η,C,hη,hC,hCenter⟩ := uniform_normal_parallel_center_angular_C1 (Y := Y)
    hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηN,hηN,hNear⟩ := uniform_normal_control_on_disk (Y := Y)
    hΩ (by omega : 2 ≤ m) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨min η ηN,K*C,lt_min hη hηN,by positivity,?_⟩
  intro floor hf ε hε hsmall d hd y hy a b
  dsimp only
  let r := d.radius y
  let V (z : X dim) := scaledNormalTraceVelocity d.γ d.expMap d.frame y r b z a
  let H := frameCoordinatesL d.γ y (d.frame y)
  let F (z : X dim) := V z-H a-b • z
  let G (z : X dim) := normalizedParallelCenterJacobian d.γ d.expMap y (r • frameVector d.frame y z)
  let T := (ContinuousLinearMap.apply ℝ (X dim) a : (X dim →L[ℝ] X dim) →L[ℝ] X dim)
  have hyΩ := hd.2.1.center_mem hy
  have hFr := hd.1.2.2.2.2.2.2.2 y hyΩ
  have hK₀ := zero_lt_one.trans_le hK
  have hH : ‖H‖ ≤ K := by
    apply ContinuousLinearMap.opNorm_le_bound H hK₀.le
    intro x
    have h := ((hd.1.1.2 y hyΩ).2 x).2
    rw [← norm_frameCoordinates_sq _ _ _ _ hFr,← frameCoordinatesL_apply] at h
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ K*‖x‖)).mp
    calc
      _ ≤ K*‖x‖^2 := h
      _ ≤ _ := by rw [mul_pow]; gcongr; nlinarith only [hK]
  have hT : ‖T‖ ≤ ‖a‖ := by
    apply ContinuousLinearMap.opNorm_le_bound T (norm_nonneg _)
    intro A
    exact (A.le_opNorm a).trans_eq (mul_comm _ _)
  let B := H.comp T
  have hB := (H.opNorm_comp_le T).trans (mul_le_mul hH hT (norm_nonneg _) hK₀.le)
  have hExpr : EqOn F (fun z => B (G z-ContinuousLinearMap.id ℝ (X dim))) (ball (0 : X dim) 2) := by
    intro z hz
    have hDisk := frameVector_mem_disk d.γ d.frame y z 2 hFr (ball_subset_closedBall hz)
    have hN := hNear floor hf ε hε (hsmall.trans (min_le_right _ _)) d hd y hy _ hDisk
    have he := scaledNormalTraceVelocity_eq_center_add_radius hd.2.1 d.frame hy hFr r b z a
      (interior_subset hN.1.1)
    change scaledNormalTraceVelocity d.γ d.expMap d.frame y r b z a-H a-b • z = _
    rw [he]
    change H (G z a)+b • z-H a-b • z = H ((G z-ContinuousLinearMap.id ℝ (X dim)) a)
    simp only [sub_apply,ContinuousLinearMap.id_apply,map_sub]
    abel
  intro z hz
  have hz2 := closedBall_subset_ball (by norm_num : (1 : ℝ) < 2) hz
  have hE := hCenter floor hf ε hε (hsmall.trans (min_le_left _ _)) d hd y hy z hz
  have hNz := hNear floor hf ε hε (hsmall.trans (min_le_right _ _)) d hd y hy _
    (frameVector_mem_disk d.γ d.frame y z 2 hFr (ball_subset_closedBall hz2))
  have hGs : ContDiffAt ℝ ∞ G z := by
    have hOut := hd.2.1.contDiffAt_normalizedParallelCenterJacobian hy
      (r • frameVector d.frame y z) (interior_subset hNz.1.1)
    have hIn : ContDiff ℝ ∞ (fun x => r • frameVector d.frame y x) := by
      have hh : (fun x => r • frameVector d.frame y x) = ⇑(r • frameVectorLinear d.frame y) :=
        funext fun x => by simp only [smul_apply,frameVectorLinear_apply]
      rw [hh]
      exact (r • frameVectorLinear d.frame y).contDiff
    exact hOut.comp z hIn.contDiffAt
  have hGerm : F =ᶠ[nhds z] fun x => B (G x-ContinuousLinearMap.id ℝ (X dim)) := by
    filter_upwards [isOpen_ball.mem_nhds hz2] with w hw using hExpr hw
  have hFD : fderiv ℝ F z = B.comp (fderiv ℝ G z) := by
    rw [hGerm.fderiv_eq]
    have h := B.hasFDerivAt.comp z (((hGs.differentiableAt (by simp)).hasFDerivAt).sub_const
      (ContinuousLinearMap.id ℝ (X dim)))
    exact h.fderiv
  change ‖F z‖ ≤ K*C*r^2*‖a‖ ∧ ‖fderiv ℝ F z‖ ≤ K*C*r^2*‖a‖
  rw [hExpr hz2,hFD]
  exact ⟨((B.le_opNorm _).trans (mul_le_mul hB hE.1 (norm_nonneg _) (by positivity))).trans_eq (by ring),
    ((B.opNorm_comp_le _).trans (mul_le_mul hB hE.2 (norm_nonneg _) (by positivity))).trans_eq (by ring)⟩

end CalderonN

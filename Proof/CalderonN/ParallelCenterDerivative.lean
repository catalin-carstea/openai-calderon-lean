module

public import Proof.CalderonN.NormalParallelMixedVariation
public import Proof.CalderonN.NormalCenterHorizontalVelocity
public import Proof.CalderonN.NormalSecondVariationTaylor

import Mathlib.Tactic

/-! Adapted from the checked Proposition 5.3 release, Proof/ParallelCenterDerivative.lean. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

lemma NormalCoordinates.parallel_variation_velocity_derivative {Y Ω : Set (X dim)} {g : (MetricField dim)}
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v a b : (X dim)) (t : ℝ) (hv : t • v ∈ disk g y (R y)) :
    fderiv ℝ (fun w => normalParallelVariation g expMap y w a t) v b =
      secondParameterVariation (normalJointPhase expMap) (a,-connection g y a v) (0,b) ((y,v),t)-
        normalJointVariation expMap y v 0 (connection g y a b) t := by
  have hPhase := hN.contDiffAt_jointPhase hy v t hv
  have hInput := ((hasFDerivAt_const (𝕜:=ℝ) y v).prodMk (hasFDerivAt_id v)).prodMk
    (hasFDerivAt_const t v)
  have hDir := ((hasFDerivAt_const (𝕜:=ℝ) a v).prodMk
    ((connectionBilinear g y a).hasFDerivAt.neg)).prodMk (hasFDerivAt_const (0:ℝ) v)
  have hD := ((hPhase.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp v hInput
  have hEval := congrArg (fun L : (X dim) →L[ℝ] (X dim) × (X dim) => L b) (hD.clm_apply hDir).fderiv
  have hSecond := fderiv_apply_const_of_contDiffAt (normalJointPhase expMap) ((y,v),t)
    ((a,-connection g y a v),0) ((0,b),0) hPhase
  change secondParameterVariation (normalJointPhase expMap) (a,-connection g y a v) (0,b) ((y,v),t) =
    fderiv ℝ (fderiv ℝ (normalJointPhase expMap)) ((y,v),t) ((0,b),0)
      ((a,-connection g y a v),0) at hSecond
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.zero_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.neg_apply,connectionBilinear_apply,Function.comp_def,Function.id_def,
    Pi.neg_apply] at hEval
  have hEval' : fderiv ℝ (fun w => normalParallelVariation g expMap y w a t) v b =
      fderiv ℝ (normalJointPhase expMap) ((y,v),t) ((0,-connection g y a b),0)+
      fderiv ℝ (fderiv ℝ (normalJointPhase expMap)) ((y,v),t) ((0,b),0)
        ((a,-connection g y a v),0) := by
    simpa only [normalParallelVariation,normalJointVariation] using hEval
  rw [← hSecond] at hEval'
  have hNeg : (((0:(X dim)),-connection g y a b),(0:ℝ)) =
      -(((0:(X dim)),connection g y a b),(0:ℝ)) := by simp
  rw [hNeg,map_neg] at hEval'
  exact hEval'.trans (by unfold normalJointVariation;abel)

lemma normalParallelCenterJacobian_split (g : (MetricField dim)) (expMap : (X dim) × (X dim) → (X dim)) (y v : (X dim)) :
    normalParallelCenterJacobian g expMap y v =
      (fderiv ℝ expMap (y,v)).comp (ContinuousLinearMap.inl ℝ (X dim) (X dim))-
        (normalVerticalJacobian expMap y v).comp ((connectionBilinear g y).flip v) := by
  apply ContinuousLinearMap.ext
  intro a
  rw [normalParallelCenterJacobian_apply]
  change fderiv ℝ expMap (y,v) (a,-connection g y a v) =
    fderiv ℝ expMap (y,v) (a,0)-fderiv ℝ expMap (y,v) (0,connectionBilinear g y a v)
  rw [← map_sub,connectionBilinear_apply]
  congr 1
  ext <;> simp

lemma NormalCoordinates.contDiffAt_parallelCenterJacobian {Y Ω : Set (X dim)} {g : (MetricField dim)}
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v : (X dim)) (hv : v ∈ disk g y (R y)) :
    ContDiffAt ℝ ∞ (normalParallelCenterJacobian g expMap y) v := by
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hE : ContDiffAt ℝ ∞ expMap (y,v) := hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,hv⟩))
  have hD := (hE.fderiv_right (m:=∞) (by simp)).comp v (contDiffAt_const.prodMk contDiffAt_id)
  have hBase := hD.clm_comp (show ContDiffAt ℝ ∞
    (fun _ : (X dim) => ContinuousLinearMap.inl ℝ (X dim) (X dim)) v from contDiffAt_const)
  have hJ := hN.contDiffAt_normalVerticalJacobian hy v hv
  have hGamma : ContDiffAt ℝ ∞ (fun w => (connectionBilinear g y).flip w) v :=
    (connectionBilinear g y).flip.contDiff.contDiffAt
  simpa only [Function.comp_def,← normalParallelCenterJacobian_split] using hBase.sub (hJ.clm_comp hGamma)

/-- The endpoint derivative includes the derivative of the parallel initial
    direction. Keeping this term explicit is essential for the cancellation. -/
lemma NormalCoordinates.parallelCenterJacobian_derivative_apply {Y Ω : Set (X dim)} {g : (MetricField dim)}
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v a b : (X dim)) (hv : v ∈ interior (disk g y (R y))) :
    fderiv ℝ (normalParallelCenterJacobian g expMap y) v b a =
      (secondParameterVariation (normalJointPhase expMap) (a,-connection g y a v) (0,b) ((y,v),1)).1-
        normalVerticalJacobian expMap y v (connection g y a b) := by
  have hvOne : (1:ℝ) • v ∈ disk g y (R y) := by simpa only [one_smul] using interior_subset hv
  have hPhase := hN.contDiffAt_jointPhase hy v 1 hvOne
  have hD := ((hPhase.fderiv_right (m:=∞) (by simp)).comp v
    ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).differentiableAt (by simp)
  have hDir : ContDiffAt ℝ ∞ (fun w : (X dim) => ((a,-connectionBilinear g y a w),(0:ℝ))) v :=
    (contDiffAt_const.prodMk ((connectionBilinear g y a).contDiff.contDiffAt.neg)).prodMk contDiffAt_const
  have hSlice : DifferentiableAt ℝ (fun w => normalParallelVariation g expMap y w a 1) v := by
    simpa only [normalParallelVariation,normalJointVariation,connectionBilinear_apply,
      Function.comp_def,Function.id_def] using hD.clm_apply (hDir.differentiableAt (by simp))
  have hNear : (fun w => (normalParallelVariation g expMap y w a 1).1) =ᶠ[𝓝 v]
      (fun w => normalParallelCenterJacobian g expMap y w a) := by
    filter_upwards [isOpen_interior.mem_nhds hv] with w hw
    exact (hN.joint_variation_position_eq hy w a (-connection g y a w) 1
      (by simpa only [one_smul] using interior_subset hw)).trans
        (by simpa only [one_smul] using (normalParallelCenterJacobian_apply g expMap y w a).symm)
  have hEval := ((hN.contDiffAt_parallelCenterJacobian hy v (interior_subset hv)).differentiableAt
    (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const a v)
  have hValue : fderiv ℝ (fun w => normalParallelCenterJacobian g expMap y w a) v b =
      fderiv ℝ (normalParallelCenterJacobian g expMap y) v b a := by
    rw [hEval.fderiv]
    simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      zero_apply,map_zero,zero_add]
  have hFst := congrArg (fun L : (X dim) →L[ℝ] (X dim) => L b) hSlice.hasFDerivAt.fst.fderiv
  change fderiv ℝ (fun w => (normalParallelVariation g expMap y w a 1).1) v b =
    (fderiv ℝ (fun w => normalParallelVariation g expMap y w a 1) v b).1 at hFst
  rw [hNear.fderiv_eq,hValue,hN.parallel_variation_velocity_derivative hy v a b 1 hvOne] at hFst
  have hVert := hN.joint_variation_position_eq hy v 0 (connection g y a b) 1 hvOne
  simp only [one_smul] at hVert
  change (normalJointVariation expMap y v 0 (connection g y a b) 1).1 =
    normalVerticalJacobian expMap y v (connection g y a b) at hVert
  exact hFst.trans (by change _ = _;rw [Prod.fst_sub,hVert])

@[expose] def parallelCenterDerivativeErrorBudget (K C D E : ℝ) : ℝ :=
  mixedParallelVariationBudget K C D E+normalVariationErrorBudget K C D*C

/-- The actual parallel-center Jacobian has first velocity jet minus Gamma,
    with a uniform speed-linear error. -/
theorem NormalCoordinates.parallelCenterJacobian_derivative_error {Y Ω : Set (X dim)}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K C D E : ℝ} {g : (MetricField dim)}
    (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    (hΓ2 : ∀ x ∈ Ω,‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) x‖ ≤ E)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (hR : ContinuousAt R y) (v : (X dim)) (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (normalParallelCenterJacobian g expMap y) v+connectionBilinear g y‖ ≤
      parallelCenterDerivativeErrorBudget K C D E*‖v‖ := by
  have hB : 0 ≤ normalVariationErrorBudget K C D := by unfold normalVariationErrorBudget;positivity
  have hMixed : 0 ≤ mixedParallelVariationBudget K C D E := by
    unfold mixedParallelVariationBudget mixedParallelForceBudget parallelVelocityBudget parallelVariationBudget
    dsimp only
    positivity
  have hBudget : 0 ≤ parallelCenterDerivativeErrorBudget K C D E := by
    unfold parallelCenterDerivativeErrorBudget;positivity
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (mul_nonneg hBudget (norm_nonneg v))
  intro b a
  have hvd := mem_interior_disk_of_metricPair_lt g y v (R y) hv
  have ht : (1:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hS := (norm_fst_le (secondParameterVariation (normalJointPhase expMap)
    (a,-connection g y a v) (0,b) ((y,v),1))).trans
      (hN.parallel_mixed_variation_bound hY hΩ hg hK hC hD hE hΓ0 hΓ1 hΓ2 hy hR v a b hv hv1 ht)
  have hJ := hN.normalVerticalJacobian_sub_id_bound hΩ hg hK hC hD hΓ0 hΓ1 hy v hvd hv1
  have hConn : ‖connection g y a b‖ ≤ C*‖a‖*‖b‖ := by
    rw [← connectionBilinear_apply]
    exact (norm_bilinear_apply_le _ _ _).trans (by gcongr;exact hΓ0 y (hN.center_mem hy))
  have hProduct : ‖(normalVerticalJacobian expMap y v-ContinuousLinearMap.id ℝ (X dim))
      (connection g y a b)‖ ≤ (normalVariationErrorBudget K C D*C)*‖v‖*‖a‖*‖b‖ := by
    calc
      _ ≤ ‖normalVerticalJacobian expMap y v-ContinuousLinearMap.id ℝ (X dim)‖*‖connection g y a b‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (normalVariationErrorBudget K C D*‖v‖)*(C*‖a‖*‖b‖) := by gcongr
      _ = _ := by ring
  have hSym : connectionBilinear g y b a = connection g y a b := by
    rw [connectionBilinear_apply]
    exact connection_symmetric hΩ hg (hN.center_mem hy) b a
  change ‖fderiv ℝ (normalParallelCenterJacobian g expMap y) v b a+connectionBilinear g y b a‖ ≤ _
  rw [hN.parallelCenterJacobian_derivative_apply hy v a b hvd,hSym]
  have hEq : (secondParameterVariation (normalJointPhase expMap)
      (a,-connection g y a v) (0,b) ((y,v),1)).1-
      normalVerticalJacobian expMap y v (connection g y a b)+connection g y a b =
      (secondParameterVariation (normalJointPhase expMap) (a,-connection g y a v) (0,b) ((y,v),1)).1-
      (normalVerticalJacobian expMap y v-ContinuousLinearMap.id ℝ (X dim)) (connection g y a b) := by
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply]
    abel
  rw [hEq]
  exact (norm_sub_le _ _).trans ((add_le_add hS hProduct).trans_eq (by
    dsimp only [parallelCenterDerivativeErrorBudget];ring))

/-- Torsion-freeness cancels the constant first jets of parallel-center and
    vertical Jacobians. Their actual derivative difference is speed-linear. -/
theorem NormalCoordinates.parallel_center_sub_vertical_derivative_bound {Y Ω : Set (X dim)}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K C D E : ℝ} {g : (MetricField dim)}
    (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    (hΓ2 : ∀ x ∈ Ω,‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) x‖ ≤ E)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (hR : ContinuousAt R y) (v : (X dim)) (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (fun w => normalParallelCenterJacobian g expMap y w-normalVerticalJacobian expMap y w) v‖ ≤
      (parallelCenterDerivativeErrorBudget K C D E+secondVelocityPrincipalErrorBudget K C D E)*‖v‖ := by
  have hvd := mem_interior_disk_of_metricPair_lt g y v (R y) hv
  have hCen := hN.parallelCenterJacobian_derivative_error hY hΩ hg hK hC hD hE hΓ0 hΓ1 hΓ2 hy hR v hv hv1
  have hVert := hN.normalVerticalJacobian_derivative_error hΩ hg hK hC hD hE hΓ0 hΓ1 hΓ2 hy v hvd hv1
  have hDiff : HasFDerivAt
      (fun w => normalParallelCenterJacobian g expMap y w-normalVerticalJacobian expMap y w)
      (fderiv ℝ (normalParallelCenterJacobian g expMap y) v-
        fderiv ℝ (normalVerticalJacobian expMap y) v) v :=
    ((hN.contDiffAt_parallelCenterJacobian hy v hv.le).differentiableAt (by simp)).hasFDerivAt.sub
      ((hN.contDiffAt_normalVerticalJacobian hy v hv.le).differentiableAt (by simp)).hasFDerivAt
  have hDf : fderiv ℝ (normalParallelCenterJacobian g expMap y-normalVerticalJacobian expMap y) v =
      fderiv ℝ (normalParallelCenterJacobian g expMap y) v-fderiv ℝ (normalVerticalJacobian expMap y) v :=
    hDiff.fderiv
  change ‖fderiv ℝ (normalParallelCenterJacobian g expMap y-normalVerticalJacobian expMap y) v‖ ≤ _
  rw [hDf]
  have hEq : fderiv ℝ (normalParallelCenterJacobian g expMap y) v-
      fderiv ℝ (normalVerticalJacobian expMap y) v =
      (fderiv ℝ (normalParallelCenterJacobian g expMap y) v+connectionBilinear g y)-
      (fderiv ℝ (normalVerticalJacobian expMap y) v+connectionBilinear g y) := by abel
  rw [hEq]
  exact (norm_sub_le _ _).trans ((add_le_add hCen hVert).trans_eq (by ring))

end CalderonN

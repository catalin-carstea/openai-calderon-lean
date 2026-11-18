import Proof.NormalizedDensityAffineTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def firstDensityLogCovariantDerivative (g g₁ : MetricField) (y a : X) : X →L[ℝ] ℝ :=
  fderiv ℝ (firstDensityLogDifferential g g₁) y a-
    (firstDensityLogDifferential g g₁ y).comp (connectionBilinear g y a)

def normalizedDensityCovariantCenterRemainder (g g₁ : MetricField) (E : X × X → X) (y v a : X) : ℝ :=
  fderiv ℝ (normalizedJointFirstDensityFactor g g₁ E) (y,v) (a,-connection g y a v)-
    firstDensityLogCovariantDerivative g g₁ y a v

theorem Background.normalized_density_covariant_center_bound {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 5 ≤ m)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R)
    (hR : ContinuousOn R Y) {y : X} (hy : y ∈ Y) (v a : X)
    (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1) :
    ‖normalizedDensityCovariantCenterRemainder g g₁ E y v a‖ ≤
      (1+243*K*|M ⟨1,by omega⟩|)*backgroundNormalizedDensityJetBudget hm K M*‖v‖^2*‖a‖ := by
  let F := normalizedJointFirstDensityFactor g g₁ E
  let ell := firstDensityLogDifferential g g₁
  let Q := backgroundNormalizedDensityJetBudget hm K M
  let C := 243*K*|M ⟨1,by omega⟩|
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hV := backgroundExpJetEnvelope_ge_one hm hK.le M
  have hQ : 0 ≤ Q := by dsimp [Q,backgroundNormalizedDensityJetBudget];positivity
  have hΓ (z : X) : ‖connection g y a z‖ ≤ C*‖a‖*‖z‖ := by
    rw [← connectionBilinear_apply]
    exact (norm_bilinear_apply_le _ _ _).trans (by gcongr;exact h.connection_budget hK (by omega) (hN.center_mem hy))
  have hTaylor := h.normalized_joint_density_affine_taylor hY hΩ hK hm hN hR hy v hv hv1
  have hCenter := hTaylor.2.2.1 a
  have hVertical := hTaylor.2.1 (-connection g y a v)
  have hVertBound : ‖fderiv ℝ F (y,v) (0,-connection g y a v)-ell y (-connection g y a v)‖ ≤ Q*C*‖v‖^2*‖a‖ := by
    rw [norm_neg] at hVertical
    exact hVertical.trans ((show Q*‖v‖*‖connection g y a v‖ ≤ Q*‖v‖*(C*‖a‖*‖v‖) by
      gcongr;exact hΓ v).trans_eq (by ring))
  have hEq : normalizedDensityCovariantCenterRemainder g g₁ E y v a =
      (fderiv ℝ F (y,v) (a,0)-fderiv ℝ ell y a v)+
      (fderiv ℝ F (y,v) (0,-connection g y a v)-ell y (-connection g y a v)) := by
    have hDir : (a,-connection g y a v) = ((a,0):X × X)+(0,-connection g y a v) := by simp
    dsimp only [normalizedDensityCovariantCenterRemainder,firstDensityLogCovariantDerivative]
    rw [hDir,map_add]
    simp only [_root_.sub_apply,ContinuousLinearMap.comp_apply,connectionBilinear_apply,map_neg]
    change _ = _
    ring
  rw [hEq]
  exact ((norm_add_le _ _).trans (add_le_add hCenter hVertBound)).trans_eq (by dsimp only [C,Q];ring)

lemma fderiv_normalizedDensityCovariantCenterRemainder (g g₁ : MetricField) (E : X × X → X) (y v a b : X)
    (hF : ContDiffAt ℝ ∞ (normalizedJointFirstDensityFactor g g₁ E) (y,v)) :
    fderiv ℝ (fun z => normalizedDensityCovariantCenterRemainder g g₁ E y z a) v b =
      fderiv ℝ (fderiv ℝ (normalizedJointFirstDensityFactor g g₁ E)) (y,v) (0,b) (a,-connection g y a v)+
      fderiv ℝ (normalizedJointFirstDensityFactor g g₁ E) (y,v) (0,-connection g y a b)-
      firstDensityLogCovariantDerivative g g₁ y a b := by
  have hInput : HasFDerivAt (fun z : X => (y,z)) (ContinuousLinearMap.inr ℝ X X) v :=
    (hasFDerivAt_const y v).prodMk (hasFDerivAt_id v)
  have hDF := ((hF.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp v hInput
  have hDirection : HasFDerivAt (fun z : X => (a,-connection g y a z))
      ((0 : X →L[ℝ] X).prod (-(connectionBilinear g y a))) v := by
    convert (hasFDerivAt_const a v).prodMk ((connectionBilinear g y a).hasFDerivAt.neg) using 1
    funext z
    simp only [Pi.neg_apply,connectionBilinear_apply]
  have hAll := (hDF.clm_apply hDirection).sub (firstDensityLogCovariantDerivative g g₁ y a).hasFDerivAt
  have hh := congrArg (fun L : X →L[ℝ] ℝ => L b) hAll.fderiv
  simp only [Function.comp_def,_root_.sub_apply,_root_.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.prod_apply,ContinuousLinearMap.inr_apply,
    _root_.neg_apply,connectionBilinear_apply,zero_apply] at hh
  change fderiv ℝ (fun z => normalizedDensityCovariantCenterRemainder g g₁ E y z a) v b = _ at hh
  exact hh.trans (by ring)

theorem Background.normalized_density_covariant_center_vertical_derivative_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (h : Background Ω K M g g₁ g₂ e)
    (hK : 0 < K) (hm : 5 ≤ m) {E : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g E R) (hR : ContinuousOn R Y)
    {y : X} (hy : y ∈ Y) (v a b : X)
    (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (fun z => normalizedDensityCovariantCenterRemainder g g₁ E y z a) v b‖ ≤
      (1+2*(243*K*|M ⟨1,by omega⟩|))*backgroundNormalizedDensityJetBudget hm K M*
        ‖v‖*‖b‖*‖a‖ := by
  let F := normalizedJointFirstDensityFactor g g₁ E
  let ell := firstDensityLogDifferential g g₁
  let Q := backgroundNormalizedDensityJetBudget hm K M
  let C := 243*K*|M ⟨1,by omega⟩|
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hV := backgroundExpJetEnvelope_ge_one hm hK.le M
  have hQ : 0 ≤ Q := by dsimp [Q,backgroundNormalizedDensityJetBudget];positivity
  have hΓ (z : X) : ‖connection g y a z‖ ≤ C*‖a‖*‖z‖ := by
    rw [← connectionBilinear_apply]
    exact (norm_bilinear_apply_le _ _ _).trans (by gcongr;exact h.connection_budget hK (by omega) (hN.center_mem hy))
  obtain ⟨hSmooth,hJets⟩ := h.normalized_joint_first_density_jets hY hΩ hK hm hN hR hy v hv hv1
  have hD2 : ‖fderiv ℝ (fderiv ℝ F) (y,v)‖ ≤ Q := by
    have hb := hJets 2 (by omega)
    rwa [← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one] at hb
  have hTaylor := h.normalized_joint_density_affine_taylor hY hΩ hK hm hN hR hy v hv hv1
  have hMixed := hTaylor.2.2.2 a b
  have hVertical := hTaylor.2.1 (-connection g y a b)
  have hTwo : ‖fderiv ℝ (fderiv ℝ F) (y,v) (0,b) (0,-connection g y a v)‖ ≤ Q*C*‖v‖*‖b‖*‖a‖ := by
    have hb := (ContinuousLinearMap.le_opNorm₂ (fderiv ℝ (fderiv ℝ F) (y,v)) ((0:X),b) ((0:X),-connection g y a v)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD2 (norm_nonneg _)) (norm_nonneg _))
    simp only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg b),norm_neg,
      max_eq_right (norm_nonneg (connection g y a v))] at hb
    exact hb.trans ((show Q*‖b‖*‖connection g y a v‖ ≤ Q*‖b‖*(C*‖a‖*‖v‖) by
      gcongr;exact hΓ v).trans_eq (by ring))
  have hThree : ‖fderiv ℝ F (y,v) (0,-connection g y a b)-ell y (-connection g y a b)‖ ≤ Q*C*‖v‖*‖b‖*‖a‖ := by
    rw [norm_neg] at hVertical
    exact hVertical.trans ((show Q*‖v‖*‖connection g y a b‖ ≤ Q*‖v‖*(C*‖a‖*‖b‖) by
      gcongr;exact hΓ b).trans_eq (by ring))
  have hEq : fderiv ℝ (fun z => normalizedDensityCovariantCenterRemainder g g₁ E y z a) v b =
      (fderiv ℝ (fderiv ℝ F) (y,v) (0,b) (a,0)-fderiv ℝ ell y a b)+
      fderiv ℝ (fderiv ℝ F) (y,v) (0,b) (0,-connection g y a v)+
      (fderiv ℝ F (y,v) (0,-connection g y a b)-ell y (-connection g y a b)) := by
    rw [fderiv_normalizedDensityCovariantCenterRemainder g g₁ E y v a b hSmooth]
    have hDir : (a,-connection g y a v) = ((a,0):X × X)+(0,-connection g y a v) := by simp
    rw [hDir,map_add]
    simp only [firstDensityLogCovariantDerivative,_root_.sub_apply,ContinuousLinearMap.comp_apply,
      connectionBilinear_apply,map_neg]
    change _ = _
    ring
  rw [hEq]
  exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hMixed hTwo)) hThree)).trans_eq
    (by dsimp only [C,Q];ring)

end ShrinkingSpheres

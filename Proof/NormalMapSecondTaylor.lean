import Proof.NormalMapTransport
import Proof.CurveAffineError

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- A second-jet budget controls the genuine second Taylor error of a background
    map along the normal geodesic, with one common explicit quadratic constant. -/
theorem NormalCoordinates.map_second_taylor_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Y Ω : Set X} (hΩ : IsOpen Ω) {K C M1 M2 : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 0 < K) (hC : 0 ≤ C) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hΓ : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (F : X → E) (hSmooth : ContDiffOn ℝ ∞ F Ω)
    (hDF : ∀ x ∈ Ω,‖fderiv ℝ F x‖ ≤ M1)
    (hDDF : ∀ x ∈ Ω,‖fderiv ℝ (fderiv ℝ F) x‖ ≤ M2)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v : X) (hv : v ∈ disk g y (R y)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖F (expMap (y,t • v))-F y-t • fderiv ℝ F y v‖ ≤
      ((M2+M1*C)*K^2)*‖v‖^2*t^2 := by
  let P : ℝ → X × X := fun s => normalGeodesicPhase expMap y (v,s)
  let G : ℝ → E := fun s => F (P s).1
  let V : ℝ → E := fun s => fderiv ℝ F (P s).1 (P s).2
  let B := ((M2+M1*C)*K^2)*‖v‖^2
  have hB : 0 ≤ B := by dsimp [B];positivity
  have hPosition (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : HasDerivAt (fun q => (P q).1) (P s).2 s :=
    hasDerivAt_prod_fst (hN.hasDerivAt_phase hy v hv hs)
  have hVelocity (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun q => (P q).2) (-connection g (P s).1 (P s).2 (P s).2) s :=
    hasDerivAt_prod_snd (hN.hasDerivAt_phase hy v hv hs)
  have hGD (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : HasDerivAt G (V s) s :=
    ((hSmooth.contDiffAt (hΩ.mem_nhds (hN.path_image hy v hv hs))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s
      (hPosition s hs)
  have hVD (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivAt V (fderiv ℝ F (P s).1 (-connection g (P s).1 (P s).2 (P s).2)+
        fderiv ℝ (fderiv ℝ F) (P s).1 (P s).2 (P s).2) s := by
    have hPos : (P s).1 ∈ Ω := hN.path_image hy v hv hs
    have hF := hSmooth.contDiffAt (hΩ.mem_nhds hPos)
    have hD := ((hF.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s
      (hPosition s hs)
    exact (hD.clm_apply (hVelocity s hs)).congr_deriv (add_comm _ _)
  have hBound (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖deriv V s‖ ≤ B := by
    have hPos : (P s).1 ∈ Ω := hN.path_image hy v hv hs
    have hSpeed : ‖(P s).2‖ ≤ K*‖v‖ := by
      rw [show P s = (expMap (y,s • v),deriv (fun q : ℝ => expMap (y,q • v)) s) from hN.phase_eq hy v hv hs]
      exact hN.geodesic_speed_le hΩ hg hK hy v hv hs
    have hAcc : ‖-connection g (P s).1 (P s).2 (P s).2‖ ≤ C*K^2*‖v‖^2 := by
      rw [norm_neg,← connectionBilinear_apply]
      exact (norm_bilinear_apply_le _ _ _).trans ((show
        ‖connectionBilinear g (P s).1‖*‖(P s).2‖*‖(P s).2‖ ≤ C*(K*‖v‖)*(K*‖v‖) by
          gcongr;exact hΓ _ hPos).trans_eq (by ring))
    have h1 : ‖fderiv ℝ F (P s).1 (-connection g (P s).1 (P s).2 (P s).2)‖ ≤ M1*(C*K^2*‖v‖^2) :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hDF _ hPos) hAcc (norm_nonneg _) hM1)
    have h2 : ‖fderiv ℝ (fderiv ℝ F) (P s).1 (P s).2 (P s).2‖ ≤ M2*(K*‖v‖)*(K*‖v‖) := by
      calc
        _ ≤ ‖fderiv ℝ (fderiv ℝ F) (P s).1‖*‖(P s).2‖*‖(P s).2‖ :=
          ((fderiv ℝ (fderiv ℝ F) (P s).1 (P s).2).le_opNorm (P s).2).trans
            (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ F) (P s).1).le_opNorm (P s).2) (norm_nonneg _))
        _ ≤ _ := by gcongr;exact hDDF _ hPos
    rw [(hVD s hs).deriv]
    exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by dsimp [B];ring))
  have hZero : P 0 = (y,v) := hN.phase_zero hy v hv
  have hVZero : V 0 = fderiv ℝ F y v := by dsimp [V];rw [hZero]
  have hGZero : G 0 = F y := by dsimp [G];rw [hZero]
  have hz : (0:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hError (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖V s-fderiv ℝ F y v‖ ≤ B*s := by
    have hb := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun q hq => (hVD q hq).differentiableAt) hBound hz hs
    rw [hVZero] at hb
    simpa only [sub_zero,Real.norm_eq_abs,abs_of_nonneg hs.1] using hb
  exact norm_curve_affine_error_le G V (F y) (fderiv ℝ F y v) B t hB ht hGD hGZero hError

end ShrinkingSpheres

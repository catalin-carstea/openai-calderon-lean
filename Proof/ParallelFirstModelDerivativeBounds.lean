import Proof.ParallelFirstCoefficientModel
import Proof.CanonicalFirstRadialCovariantJet
import Proof.CommonSupportDirectionalGenerators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.EnergyBridge

theorem Background.firstDensityLogCovariantDerivative_eq_hessian {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) {y : X} (hy : y ∈ Ω) (a : X) :
    firstDensityLogCovariantDerivative g g₁ y a =
      -hessianBilinear g (firstMetricConformalDepth g g₁) y a := by
  let t := firstMetricConformalDepth g g₁
  have hNear : firstDensityLogDifferential g g₁ =ᶠ[𝓝 y] -fderiv ℝ t := by
    filter_upwards [hΩ.mem_nhds hy] with x hx
    exact h.firstDensityLogDifferential_eq_depth hK hΩ hx
  have hDEll : fderiv ℝ (firstDensityLogDifferential g g₁) y = -fderiv ℝ (fderiv ℝ t) y :=
    hNear.fderiv_eq.trans fderiv_neg
  ext v
  simp only [firstDensityLogCovariantDerivative,hDEll,h.firstDensityLogDifferential_eq_depth hK hΩ hy,
    _root_.sub_apply,_root_.neg_apply,ContinuousLinearMap.comp_apply,connectionBilinear_apply,hessianBilinear_apply]
  ring

theorem Background.firstDensityLogCovariantDerivative_frame_eq {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) {y : X} (hy : y ∈ Ω) (a : X) :
    (firstDensityLogCovariantDerivative d.γ d.g₁ y a).comp (frameVectorLinear d.frame y) =
      firstDensityCovariantLinearL d y a := by
  rw [h.firstDensityLogCovariantDerivative_eq_hessian hΩ hK hy]
  rfl

lemma fderiv_parallelFirstCoefficientModel_center (g g₁ : MetricField) (y a : X) (L : X →L[ℝ] X)
    (z : X) (i j : I) (hEll : ContDiffAt ℝ ∞ (firstDensityLogDifferential g g₁) y) :
    fderiv ℝ (fun p => parallelFirstCoefficientModel g g₁ y a L p i j) (0,z) (1,0) =
      firstDensityLogCovariantDerivative g g₁ y a (L z)*(1:Mat) i j := by
  have hEllAt : ContDiffAt ℝ ∞ (firstDensityLogDifferential g g₁) (y+(0:ℝ) • a) := by simpa using hEll
  have hM := contDiffAt_parallelFirstCoefficientModel g g₁ y a L (0,z) hEllAt
  have hEntry := (contDiffAt_pi.mp (contDiffAt_pi.mp hM i) j)
  have hTime := (hEntry.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (0:ℝ)
    ((hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) z))
  have hOther := ((hasDerivAt_parallelFirstCoefficientCovector g g₁ y a L hEll).clm_apply
    (hasDerivAt_const (0:ℝ) z)).mul_const ((1:Mat) i j)
  simp only [map_zero,add_zero,ContinuousLinearMap.comp_apply] at hOther
  change HasDerivAt (fun t => parallelFirstCoefficientModel g g₁ y a L (t,z) i j) _ 0 at hOther
  exact hTime.unique hOther

lemma fderiv_parallelFirstCoefficientModel_mixed (g g₁ : MetricField) (y a : X) (L : X →L[ℝ] X)
    (z b : X) (i j : I) (hEll : ContDiffAt ℝ ∞ (firstDensityLogDifferential g g₁) y) :
    fderiv ℝ (fderiv ℝ (fun p => parallelFirstCoefficientModel g g₁ y a L p i j)) (0,z) (0,b) (1,0) =
      firstDensityLogCovariantDerivative g g₁ y a (L b)*(1:Mat) i j := by
  have hEllAt : ContDiffAt ℝ ∞ (firstDensityLogDifferential g g₁) (y+(0:ℝ) • a) := by simpa using hEll
  have hM := contDiffAt_parallelFirstCoefficientModel g g₁ y a L (0,z) hEllAt
  let T := (firstDensityLogCovariantDerivative g g₁ y a).comp L
  have hNear : (fun w => fderiv ℝ (fun p => parallelFirstCoefficientModel g g₁ y a L p i j) (0,w) (1,0)) =ᶠ[𝓝 z]
      (fun w => T w*(1:Mat) i j) := Filter.Eventually.of_forall
        (fun w => fderiv_parallelFirstCoefficientModel_center g g₁ y a L w i j hEll)
  have hMixed := mixed_first_coordinate_fderiv_of_germ (fun p => parallelFirstCoefficientModel g g₁ y a L p i j)
    z b (fun w => T w*(1:Mat) i j) (contDiffAt_pi.mp (contDiffAt_pi.mp hM i) j) hNear
  have hT : HasFDerivAt (fun w => T w*(1:Mat) i j) ((1:Mat) i j • T) z :=
    T.hasFDerivAt.mul_const ((1:Mat) i j)
  have hD := congrArg (fun D : X →L[ℝ] ℝ => D b) hT.fderiv
  simp only [_root_.smul_apply,smul_eq_mul] at hD
  exact hMixed.trans (by simpa only [T,ContinuousLinearMap.comp_apply,mul_comm] using hD)

def parallelFirstModelDerivativeBudget {m : ℕ} (hm : 2 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) : ℝ :=
  2*K*((K*|M ⟨2,by omega⟩|+K^2*|M ⟨1,by omega⟩|^2)+
    (K*|M ⟨1,by omega⟩|)*(243*K*|M ⟨1,by omega⟩|))

/-- Every genuine compact representative of the same parallel first model
    inherits the existing covariant Hessian bound at the native operator level. -/
theorem Background.parallel_first_model_joint_bounds {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 1 ≤ K) (hm : 2 ≤ m)
    {y : X} (hy : y ∈ Ω) (a : X)
    (A1 : ℝ × X → Mat) (hA1 : ContDiff ℝ ∞ A1) (S : Set X) (hS : IsCompact S)
    (hz1 : ∀ t z,z ∉ S → A1 (t,z) = 0)
    (hRep : ∀ z ∈ Metric.closedBall (0:X) 2,A1 =ᶠ[𝓝 (0,z)]
      parallelFirstCoefficientModel d.γ d.g₁ y a (frameVectorLinear d.frame y)) :
    (∀ z ∈ (ballOpens:Set X),∀ i j,
      |fderiv ℝ (fun p => A1 p i j) (0,z) (1,0)| ≤ parallelFirstModelDerivativeBudget hm K M*‖a‖) ∧
    (∀ z ∈ (ballOpens:Set X),∀ v : X,∀ i j,
      |fderiv ℝ (fderiv ℝ (fun p => A1 p i j)) (0,z) (0,v) (1,0)| ≤ (parallelFirstModelDerivativeBudget hm K M*‖a‖)*‖v‖) := by
  let T := firstDensityCovariantLinearL d y a
  let C := K*((K*|M ⟨2,by omega⟩|+K^2*|M ⟨1,by omega⟩|^2)+
    (K*|M ⟨1,by omega⟩|)*(243*K*|M ⟨1,by omega⟩|))
  let q := parallelFirstModelDerivativeBudget hm K M*‖a‖
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hq : 0 ≤ q := by dsimp [q,parallelFirstModelDerivativeBudget];positivity
  have hNorm : ‖T‖ ≤ C*‖a‖ := h.norm_firstDensityCovariantLinearL_le hΩ hK hm hy a
  have hEll := (h.firstDensityLogDifferential_smooth hKpos hΩ).contDiffAt (hΩ.mem_nhds hy)
  have hValue (w : X) (i j : I) : |T w*(1:Mat) i j| ≤ C*‖a‖*‖w‖ := by
    have hδ : |(1:Mat) i j| ≤ 1 := by by_cases hij : i=j <;> simp [Matrix.one_apply,hij]
    have hEval : |T w| ≤ C*‖a‖*‖w‖ := by
      simpa only [Real.norm_eq_abs] using (T.le_opNorm w).trans (mul_le_mul_of_nonneg_right hNorm (norm_nonneg w))
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul hEval hδ (abs_nonneg _) (by positivity : 0 ≤ C*‖a‖*‖w‖)
  have hEntryNear (z : X) (hz : z ∈ Metric.closedBall (0:X) 2) (i j : I) :
      (fun p => A1 p i j) =ᶠ[𝓝 (0,z)]
        (fun p => parallelFirstCoefficientModel d.γ d.g₁ y a (frameVectorLinear d.frame y) p i j) := by
    filter_upwards [hRep z hz] with p hp;exact congrArg (fun A : Mat => A i j) hp
  constructor
  · intro z hzB i j
    have hz2 := unitBall_subset_closedBall_two hzB
    have hzNorm : ‖z‖ ≤ 2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz2
    rw [(hEntryNear z hz2 i j).fderiv_eq,fderiv_parallelFirstCoefficientModel_center _ _ _ _ _ _ _ _ hEll]
    have hEq := congrArg (fun D : X →L[ℝ] ℝ => D z) (h.firstDensityLogCovariantDerivative_frame_eq hΩ hKpos hy a)
    change firstDensityLogCovariantDerivative d.γ d.g₁ y a (frameVectorLinear d.frame y z) = T z at hEq
    rw [hEq]
    exact (hValue z i j).trans ((mul_le_mul_of_nonneg_left hzNorm (mul_nonneg hC (norm_nonneg a))).trans_eq
      (by dsimp only [q,parallelFirstModelDerivativeBudget,C];ring))
  · intro z hzB v i j
    have hz2 := unitBall_subset_closedBall_two hzB
    rw [(hEntryNear z hz2 i j).fderiv.fderiv_eq,fderiv_parallelFirstCoefficientModel_mixed _ _ _ _ _ _ _ _ _ hEll]
    have hEq := congrArg (fun D : X →L[ℝ] ℝ => D v) (h.firstDensityLogCovariantDerivative_frame_eq hΩ hKpos hy a)
    change firstDensityLogCovariantDerivative d.γ d.g₁ y a (frameVectorLinear d.frame y v) = T v at hEq
    rw [hEq]
    exact (hValue v i j).trans ((show C*‖a‖*‖v‖ ≤ 2*C*‖a‖*‖v‖ by
      nlinarith only [mul_nonneg (mul_nonneg hC (norm_nonneg a)) (norm_nonneg v)]).trans_eq
      (by dsimp only [q,parallelFirstModelDerivativeBudget,C];ring))

/-- Every genuine compact representative of the same parallel first model
    inherits the existing covariant Hessian bound at the native operator level. -/
theorem Background.parallel_first_model_native_bounds {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 1 ≤ K) (hm : 2 ≤ m)
    {y : X} (hy : y ∈ Ω) (a : X)
    (A1 : ℝ × X → Mat) (hA1 : ContDiff ℝ ∞ A1) (S : Set X) (hS : IsCompact S)
    (hz1 : ∀ t z,z ∉ S → A1 (t,z) = 0)
    (hRep : ∀ z ∈ Metric.closedBall (0:X) 2,A1 =ᶠ[𝓝 (0,z)]
      parallelFirstCoefficientModel d.γ d.g₁ y a (frameVectorLinear d.frame y)) :
    CommonSupportNativeDerivativeBounds A1 hA1 S hS hz1 (parallelFirstModelDerivativeBudget hm K M*‖a‖) := by
  have hBounds := h.parallel_first_model_joint_bounds hΩ hK hm hy a A1 hA1 S hS hz1 hRep
  exact commonSupport_native_derivatives_of_joint_bounds A1 hA1 S hS hz1
    (parallelFirstModelDerivativeBudget hm K M*‖a‖) (by unfold parallelFirstModelDerivativeBudget;positivity)
    hBounds.1 hBounds.2

end ShrinkingSpheres

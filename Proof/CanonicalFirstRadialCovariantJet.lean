import Proof.CanonicalFirstRadialCorrection
import Proof.HessianDifferential
import Proof.UniformNormalGeodesicBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Covariant derivative of the normalized first-correction coefficient.
    It is expressed by the genuine Hessian of the conformal depth. -/
def firstDensityCovariantLinearL (d : Data) (y a : X) : X →L[ℝ] ℝ :=
  -(hessianBilinear d.γ (firstMetricConformalDepth d.γ d.g₁) y a).comp (frameVectorLinear d.frame y)

/-- The arbitrary frame derivative cancels against its connection action. -/
theorem Background.firstDensityLogCovector_covariant_component {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K)
    {y : X} (hy : y ∈ Ω) (a : X) (i : I) :
    fderiv ℝ (fun x => firstDensityLogCovector d x (axis i)) y a+
      firstDensityLogCovector d y
        (frameAngularVector (frameConnectionCoefficient d.γ d.frame y a) (axis i)) =
      firstDensityCovariantLinearL d y a (axis i) := by
  let t := firstMetricConformalDepth d.γ d.g₁
  have ht := (hB.firstMetricConformalDepth_smooth hK).contDiffAt (hΩ.mem_nhds hy)
  have hdt := (ht.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have he := ((hB.2.2.2.2.2.2.1 i).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  have hEq : (fun x => firstDensityLogCovector d x (axis i)) =ᶠ[𝓝 y]
      (fun x => -(fderiv ℝ t x (d.frame x i))) := by
    filter_upwards [hΩ.mem_nhds hy] with x hx
    rw [hB.firstDensityLogCovector_eq_depth hΩ hK hx,_root_.neg_apply,ContinuousLinearMap.comp_apply,
      frameVectorLinear_apply,frameVector_axis]
  have hD := congrArg (fun T : X →L[ℝ] ℝ => T a)
    (hdt.hasFDerivAt.clm_apply he.hasFDerivAt).fderiv
  have hActual : fderiv ℝ (fun x => firstDensityLogCovector d x (axis i)) y a =
      -(fderiv ℝ (fderiv ℝ t) y a (d.frame y i)+
        fderiv ℝ t y (fderiv ℝ (fun x => d.frame x i) y a)) := by
    rw [hEq.fderiv_eq]
    have hNeg : (fun x => -(fderiv ℝ t x (d.frame x i))) =
        -(fun x => fderiv ℝ t x (d.frame x i)) := rfl
    rw [hNeg,fderiv_neg,_root_.neg_apply]
    apply congrArg Neg.neg
    simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,add_comm] using hD
  have hAngular := frameVector_frameAngularVector d.γ d.frame y a (axis i) (hB.2.2.2.2.2.2.2 y hy)
  have hSum : (∑ j : I,(axis i) j • covariantFrameVector d.γ d.frame y a j) =
      covariantFrameVector d.γ d.frame y a i := by simp [axis,PiLp.single_apply]
  rw [hSum] at hAngular
  rw [hActual,hB.firstDensityLogCovector_eq_depth hΩ hK hy,_root_.neg_apply,
    ContinuousLinearMap.comp_apply,frameVectorLinear_apply,hAngular,map_neg,neg_neg]
  change -(fderiv ℝ (fderiv ℝ t) y a (d.frame y i)+
      fderiv ℝ t y (fderiv ℝ (fun x => d.frame x i) y a))+
        fderiv ℝ t y (covariantFrameVector d.γ d.frame y a i) =
    -(hessianBilinear d.γ t y a (frameVectorLinear d.frame y (axis i)))
  rw [frameVectorLinear_apply,frameVector_axis,hessianBilinear_apply,covariantFrameVector,map_add]
  ring

theorem Background.norm_firstDensityCovariantLinearL_le {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 1 ≤ K) (hm : 2 ≤ m)
    {y : X} (hy : y ∈ Ω) (a : X) :
    ‖firstDensityCovariantLinearL d y a‖ ≤
      K*((K*|M ⟨2,by omega⟩|+K^2*|M ⟨1,by omega⟩|^2)+
        (K*|M ⟨1,by omega⟩|)*(243*K*|M ⟨1,by omega⟩|))*‖a‖ := by
  let t := firstMetricConformalDepth d.γ d.g₁
  let T1 := K*|M ⟨1,by omega⟩|
  let T2 := K*|M ⟨2,by omega⟩|+K^2*|M ⟨1,by omega⟩|^2
  let CG := 243*K*|M ⟨1,by omega⟩|
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hT := hB.firstMetricConformalDepth_jet_bounds hΩ hKpos hm hy
  have hG := hB.connection_budget hKpos (by omega) hy
  have hE := hB.1.norm_frameVectorLinear_le hK hy d.frame (hB.2.2.2.2.2.2.2 y hy)
  have hH : ‖hessianBilinear d.γ t y‖ ≤ T2+T1*CG := by
    apply (norm_sub_le _ _).trans
    apply add_le_add hT.2
    have hComp : ‖((ContinuousLinearMap.compL ℝ X X ℝ) (fderiv ℝ t y)).comp (connectionBilinear d.γ y)‖ ≤
        ‖fderiv ℝ t y‖*‖connectionBilinear d.γ y‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro v
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left ((connectionBilinear d.γ y).le_opNorm v) (norm_nonneg _)) |>.trans_eq (by ring)
    exact hComp.trans (mul_le_mul hT.1 hG (norm_nonneg _) (by dsimp only [T1];positivity))
  rw [firstDensityCovariantLinearL,norm_neg]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (((hessianBilinear d.γ t y).le_opNorm a).trans
      (mul_le_mul_of_nonneg_right hH (norm_nonneg _))) hE (norm_nonneg _)
        (by dsimp only [T1,T2,CG];positivity)).trans_eq (by ring))

/-- The coefficient derivative computed from the actual center family and
    its actual frame connection, with no chosen gauge or frame jet estimate. -/
def firstDensityCovariantDerivativeL (d : Data) (y a : X) : X →L[ℝ] ℝ :=
  ∑ i : I,(fderiv ℝ (fun x => firstDensityLogCovector d x (axis i)) y a+
    firstDensityLogCovector d y
      (frameAngularVector (frameConnectionCoefficient d.γ d.frame y a) (axis i))) •
        EuclideanSpace.proj (𝕜:=ℝ) i

theorem Background.firstDensityCovariantDerivativeL_eq {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K)
    {y : X} (hy : y ∈ Ω) (a : X) :
    firstDensityCovariantDerivativeL d y a = firstDensityCovariantLinearL d y a := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [firstDensityCovariantDerivativeL,hB.firstDensityLogCovector_covariant_component hΩ hK hy,
    _root_.sum_apply,_root_.smul_apply,smul_eq_mul,PiLp.proj_apply]
  rw [linear_axis_expansion (firstDensityCovariantLinearL d y a) z]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Covariant coefficient jet of the canonical bounded radial correction.
    Its use as an operator commutator still requires rotation covariance. -/
def firstRadialCoefficientCovariantJetL (d : Data) (y a : X) :
    SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
  radialCorrectionCovectorL (firstDensityCovariantDerivativeL d y a)

theorem Background.norm_firstRadialCoefficientCovariantJetL_le {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 1 ≤ K) (hm : 2 ≤ m)
    {y : X} (hy : y ∈ Ω) (a : X) :
    ‖firstRadialCoefficientCovariantJetL d y a‖ ≤
      6*K*((K*|M ⟨2,by omega⟩|+K^2*|M ⟨1,by omega⟩|^2)+
        (K*|M ⟨1,by omega⟩|)*(243*K*|M ⟨1,by omega⟩|))*‖a‖ := by
  change ‖radialCorrectionCovectorL (firstDensityCovariantDerivativeL d y a)‖ ≤ _
  rw [hB.firstDensityCovariantDerivativeL_eq hΩ (zero_lt_one.trans_le hK) hy]
  exact (norm_radialCorrectionCovectorL_apply_le _).trans
    ((mul_le_mul_of_nonneg_left (hB.norm_firstDensityCovariantLinearL_le hΩ hK hm hy a)
      (by norm_num : (0:ℝ) ≤ 6)).trans_eq (by ring))

end ShrinkingSpheres

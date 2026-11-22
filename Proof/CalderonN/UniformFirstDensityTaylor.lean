module

public import Proof.CalderonN.FirstDensityJetBounds
public import Proof.CalderonN.EnlargedNormalInverse

import Proof.CalderonN.NormalMapDerivativeTaylor
import Proof.CalderonN.NormalJacobianInverse
import Proof.CalderonN.ConnectionOperatorBounds
import Proof.CalderonN.BackgroundBudgets
import Mathlib.Tactic

/-! Adapted from `UniformFirstDensityTaylor` in the checked Proposition 5.3 release. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The actual scalar density has one uniform affine first radial model and
    quadratic value/first angular derivative errors on every fixed normal ball. -/
theorem uniform_first_density_taylor {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η Q : ℝ,0 < η ∧ 0 ≤ Q ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      0 < firstMetricDensityFactor d.γ d.g₁ y ∧ firstMetricDensityFactor d.γ d.g₁ y ≤ K^(dim-2) ∧
      ‖firstDensityCenterDerivative d y‖ ≤ K^(dim-2)*((dim-2 : ℕ):ℝ)*K^2*|M ⟨1,by omega⟩| ∧
      ∀ z ∈ Metric.closedBall (0:(X dim)) L,
        |framedFirstDensityFactor d y (d.radius y) z-firstMetricDensityFactor d.γ d.g₁ y-
          d.radius y*firstDensityCenterDerivative d y z| ≤ Q*(d.radius y)^2 ∧
        ‖fderiv ℝ (framedFirstDensityFactor d y (d.radius y)) z-d.radius y • firstDensityCenterDerivative d y‖ ≤ Q*(d.radius y)^2 := by
  let a : ℝ := (dim-2 : ℕ)
  let M₁ := |M ⟨1,by omega⟩|
  let M₂ := |M ⟨2,by omega⟩|
  let P1 := K^(dim-2)*(a*(K*M₁))
  let P2 := K^(dim-2)*(a*(K*M₂+K^2*M₁^2)+(a*(K*M₁))^2)
  let C := (dim:ℝ)^3*(3*(dim:ℝ)*K*M₁)
  let D := (dim:ℝ)^3*(3*(dim:ℝ)^3*K^2*M₁^2+3*(dim:ℝ)*K*M₂)
  let B := normalVariationErrorBudget K C D
  let Q0 := ((P2+P1*C)*K^2)*(K*L)^2
  let Q1 := (P2*K*2+P1*B)*K^2*L
  let Q := |Q0|+|Q1|
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hP1 : 0 ≤ P1 := by dsimp [P1,a,M₁];positivity
  have hP2 : 0 ≤ P2 := by dsimp [P2,a,M₁,M₂];positivity
  have hC : 0 ≤ C := by dsimp [C,M₁];positivity
  have hD : 0 ≤ D := by dsimp [D,M₁,M₂];positivity
  have hB : 0 ≤ B := by dsimp [B,normalVariationErrorBudget];positivity
  have hQ : 0 ≤ Q := by dsimp [Q];positivity
  obtain ⟨η,hη,hControl⟩ := uniform_normal_control_on_disk (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ L hL
  refine ⟨η,Q,hη,hQ,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  let F := firstMetricDensityFactor d.γ d.g₁
  let E := frameVectorLinear d.frame y
  have hCenter := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hCenter
  have hEn : ‖E‖ ≤ K := hd.1.1.norm_frameVectorLinear_le hK hCenter d.frame hFrame
  have hSmooth : ContDiffOn ℝ ∞ F Ω := hd.1.firstMetricDensityFactor_smooth hKpos
  have hDF (x : (X dim)) (hx : x ∈ Ω) : ‖fderiv ℝ F x‖ ≤ P1 :=
    (hd.1.firstMetricDensityFactor_jet_bounds hΩ hKpos hm hx).1
  have hDDF (x : (X dim)) (hx : x ∈ Ω) : ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ P2 :=
    (hd.1.firstMetricDensityFactor_jet_bounds hΩ hKpos hm hx).2
  have hLn : ‖firstDensityCenterDerivative d y‖ ≤ K^(dim-2)*a*K^2*M₁ := by
    change ‖(fderiv ℝ F y).comp E‖ ≤ _
    calc
      _ ≤ ‖fderiv ℝ F y‖ * ‖E‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ P1*K := mul_le_mul (hDF y hCenter) hEn (norm_nonneg _) hP1
      _ = K^(dim-2)*a*K^2*M₁ := by dsimp only [P1]; ring
  refine ⟨firstMetricDensityFactor_pos _ _ _,hd.1.firstMetricDensityFactor_le hKpos hCenter,hLn,?_⟩
  intro z hz
  have hw := frameVector_mem_disk d.γ d.frame y z L hFrame hz
  have hPack := hControl floor hf ε hε hSmall d hd y hy (frameVector d.frame y z) hw
  let r := d.radius y
  let v := r • frameVector d.frame y z
  let J := normalVerticalJacobian d.expMap y v
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hzNorm : ‖z‖ ≤ L := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
  have hFrameZ : ‖frameVector d.frame y z‖ ≤ K*L := by
    have hb := E.le_opNorm z
    rw [frameVectorLinear_apply] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_right hEn (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hzNorm hKpos.le))
  have hvNorm : ‖v‖ ≤ r*(K*L) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left hFrameZ hr.le
  have hConn (x : X dim) (hx : x ∈ Ω) :=
    hd.1.1.connection_operator_bounds hΩ hKpos hx M₁ M₂ (abs_nonneg _) (abs_nonneg _)
      (fun i j => (hd.1.reference_fderiv_bound (by omega) hx i j).trans (le_abs_self _))
      (fun i j => (hd.1.reference_second_fderiv_bound hm hx i j).trans (le_abs_self _))
  have hΓ0 (x : X dim) (hx : x ∈ Ω) : ‖connectionBilinear d.γ x‖ ≤ C := (hConn x hx).1
  have hΓ1 (x : X dim) (hx : x ∈ Ω) : ‖fderiv ℝ (connectionBilinear d.γ) x‖ ≤ D := (hConn x hx).2
  have hJn : ‖J‖ ≤ 2 := by
    calc
      _ = ‖(J-ContinuousLinearMap.id ℝ (X dim))+ContinuousLinearMap.id ℝ (X dim)‖ := by rw [sub_add_cancel]
      _ ≤ ‖J-ContinuousLinearMap.id ℝ (X dim)‖+‖ContinuousLinearMap.id ℝ (X dim)‖ := norm_add_le _ _
      _ ≤ (1/2:ℝ)+1 := add_le_add hPack.2.2.2.1 ContinuousLinearMap.norm_id_le
      _ ≤ 2 := by norm_num
  have hJerr : ‖J-ContinuousLinearMap.id ℝ (X dim)‖ ≤ B*‖v‖ :=
    hd.2.1.normalVerticalJacobian_sub_id_bound hΩ hd.1.1 hKpos hC hD hΓ0 hΓ1 hy v hPack.1.1 hPack.1.2
  constructor
  · have hb := hd.2.1.map_second_taylor_bound hΩ hd.1.1 hKpos hC hP1 hP2 hΓ0 F hSmooth hDF hDDF
      hy v (interior_subset hPack.1.1) (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
    simp only [one_smul,one_pow,mul_one,v,map_smul,smul_eq_mul,Real.norm_eq_abs,one_mul] at hb
    have hb' : |framedFirstDensityFactor d y (d.radius y) z-F y-r*firstDensityCenterDerivative d y z|
        ≤ ((P2+P1*C)*K^2)*‖v‖^2 := by
      simpa only [framedFirstDensityFactor,firstDensityCenterDerivative,F,v,r,
        ContinuousLinearMap.comp_apply,frameVectorLinear_apply] using hb
    have hq0 : Q0 ≤ Q := (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
    exact hb'.trans ((show ((P2+P1*C)*K^2)*‖v‖^2 ≤ Q0*r^2 by
      calc
        _ ≤ ((P2+P1*C)*K^2)*(r*(K*L))^2 := by gcongr
        _ = _ := by dsimp [Q0];ring).trans (mul_le_mul_of_nonneg_right hq0 (sq_nonneg _)))
  · let G := fun w : (X dim) => F (d.expMap (y,w))
    have hG := ((hSmooth.contDiffAt (hΩ.mem_nhds hPack.2.1)).differentiableAt (by simp)).hasFDerivAt.comp v
      (hd.2.1.hasFDerivAt_velocity_slice hy v (interior_subset hPack.1.1))
    have hScale : HasFDerivAt (fun w => r • frameVector d.frame y w) (r • E) z := by
      convert (r • E).hasFDerivAt using 1
      funext w
      simp only [ContinuousLinearMap.smul_apply,E,frameVectorLinear_apply]
    have hComp := hG.comp z hScale
    change HasFDerivAt (framedFirstDensityFactor d y (d.radius y))
      (((fderiv ℝ F (d.expMap (y,v))).comp J).comp (r • E)) z at hComp
    have hGderiv : fderiv ℝ G v = (fderiv ℝ F (d.expMap (y,v))).comp J := hG.fderiv
    have hEq : fderiv ℝ (framedFirstDensityFactor d y (d.radius y)) z-r • firstDensityCenterDerivative d y =
        (fderiv ℝ G v-fderiv ℝ F y).comp (r • E) := by
      ext a
      simp only [hComp.fderiv,hGderiv,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,map_smul]
      rw [smul_sub]
      rfl
    rw [hEq]
    have hb := hd.2.1.map_derivative_taylor_bound hΩ hd.1.1 hKpos hP1 hP2 (by norm_num) hB
      F hSmooth hDF hDDF hy v (interior_subset hPack.1.1) hJn hJerr
    have hScaleNorm : ‖r • E‖ ≤ r*K := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left hEn hr.le
    have hq1 : Q1 ≤ Q := (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hb hScaleNorm (norm_nonneg _) (by positivity)).trans
        ((show ((P2*K*2+P1*B)*‖v‖)*(r*K) ≤ Q1*r^2 by
          calc
            _ ≤ ((P2*K*2+P1*B)*(r*(K*L)))*(r*K) := by gcongr
            _ = _ := by dsimp [Q1];ring).trans (mul_le_mul_of_nonneg_right hq1 (sq_nonneg _))))

end CalderonN

import Proof.ComponentDerivativeBounds
import Proof.SecondDerivativeCompositionBounds
import Proof.MetricSmooth
import Proof.MetricDensityBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

lemma norm_first_fderiv_mul_at {S : Set X} (hS : IsOpen S) {f g : X → ℝ}
    (hf : ContDiffOn ℝ ∞ f S) (hg : ContDiffOn ℝ ∞ g S) {y : X} (hy : y ∈ S) :
    ‖fderiv ℝ (fun x => f x*g x) y‖ ≤ |f y| * ‖fderiv ℝ g y‖+‖fderiv ℝ f y‖*|g y| := by
  have hb := norm_iteratedFDeriv_mul_at hS hf hg hy 1
  simpa only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
    Nat.choose_self,Nat.cast_one,norm_iteratedFDeriv_zero,norm_iteratedFDeriv_one,
    Real.norm_eq_abs,Nat.sub_zero,Nat.reduceSub,one_mul,zero_add] using hb

/-- A local C2 pullback metric estimate from genuine map and Jacobian jets.
    The two tangent witnesses are shared in every differentiated term. -/
theorem norm_second_fderiv_metric_pullback_le {S Ω : Set X} (hS : IsOpen S) (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    (E : X → X) (J : X → X →L[ℝ] X) (hE : ContDiffOn ℝ ∞ E S) (hJ : ContDiffOn ℝ ∞ J S)
    (hImage : ∀ x ∈ S,E x ∈ Ω) {y : X} (hy : y ∈ S) (u w : X)
    (M1 M2 V0 V1 J0 J1 J2 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hV0 : 0 ≤ V0) (hV1 : 0 ≤ V1) (hJ0 : 0 ≤ J0) (hJ1 : 0 ≤ J1) (hJ2 : 0 ≤ J2)
    (hMetric1 : ∀ i j,‖fderiv ℝ (fun x => g x i j) (E y)‖ ≤ M1)
    (hMetric2 : ∀ i j,‖fderiv ℝ (fderiv ℝ (fun x => g x i j)) (E y)‖ ≤ M2)
    (hDE : ‖fderiv ℝ E y‖ ≤ V0) (hDDE : ‖fderiv ℝ (fderiv ℝ E) y‖ ≤ V1)
    (hJValue : ‖J y‖ ≤ J0) (hDJ : ‖fderiv ℝ J y‖ ≤ J1) (hDDJ : ‖fderiv ℝ (fderiv ℝ J) y‖ ≤ J2) :
    ‖fderiv ℝ (fderiv ℝ (fun x => metricPair g (E x) (J x u) (J x w))) y‖ ≤
      9*(K*(2*J0*J2+2*J1^2)+4*M1*V0*J0*J1+(M1*V1+M2*V0^2)*J0^2)*‖u‖*‖w‖ := by
  let A (i j : I) (x : X) := g (E x) i j
  let U (z : X) (i : I) (x : X) := J x z i
  let B (i j : I) (x : X) := U u i x*U w j x
  let P := K*(2*J0*J2+2*J1^2)+4*M1*V0*J0*J1+(M1*V1+M2*V0^2)*J0^2
  have hA (i j : I) : ContDiffOn ℝ ∞ (A i j) S := (hg.1 i j).comp hE hImage
  have hU (z : X) (i : I) : ContDiffOn ℝ ∞ (U z i) S :=
    (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.contDiffOn.comp (hJ.clm_apply contDiffOn_const) (fun _ _ => mem_univ _)
  have hB (i j : I) : ContDiffOn ℝ ∞ (B i j) S := (hU u i).mul (hU w j)
  have hJy := hJ.contDiffAt (hS.mem_nhds hy)
  have hEy := hE.contDiffAt (hS.mem_nhds hy)
  have hU0 (z : X) (i : I) : |U z i y| ≤ J0*‖z‖ := by
    have hb := norm_iteratedFDeriv_clm_component_le J y z i hJy 0
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hJValue (norm_nonneg z)).trans_eq (by ring))
  have hU1 (z : X) (i : I) : ‖fderiv ℝ (U z i) y‖ ≤ J1*‖z‖ := by
    have hb := norm_iteratedFDeriv_clm_component_le J y z i hJy 1
    simp only [norm_iteratedFDeriv_one] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hDJ (norm_nonneg z)).trans_eq (by ring))
  have hU2 (z : X) (i : I) : ‖fderiv ℝ (fderiv ℝ (U z i)) y‖ ≤ J2*‖z‖ := by
    have hb := norm_iteratedFDeriv_clm_component_le J y z i hJy 2
    simp only [norm_iteratedFDeriv_two_eq_nested] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hDDJ (norm_nonneg z)).trans_eq (by ring))
  have hA0 (i j : I) : |A i j y| ≤ K := hg.entry_abs_bound hK (hImage y hy) i j
  have hA1 (i j : I) : ‖fderiv ℝ (A i j) y‖ ≤ M1*V0 := by
    have hgi := (hg.1 i j).contDiffAt (hΩ.mem_nhds (hImage y hy))
    have hComp := (hgi.differentiableAt (by simp)).hasFDerivAt.comp y (hEy.differentiableAt (by simp)).hasFDerivAt
    change HasFDerivAt (A i j) _ y at hComp
    rw [hComp.fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr;exact hMetric1 i j)
  have hA2 (i j : I) : ‖fderiv ℝ (fderiv ℝ (A i j)) y‖ ≤ M1*V1+M2*V0^2 := by
    have hb := norm_second_fderiv_comp_at E (fun x => g x i j) y hEy
      ((hg.1 i j).contDiffAt (hΩ.mem_nhds (hImage y hy)))
    exact hb.trans (by gcongr;exact hMetric1 i j;exact hMetric2 i j)
  have hB0 (i j : I) : |B i j y| ≤ J0^2*‖u‖*‖w‖ := by
    dsimp only [B]
    rw [abs_mul]
    exact (mul_le_mul (hU0 u i) (hU0 w j) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hB1 (i j : I) : ‖fderiv ℝ (B i j) y‖ ≤ 2*J0*J1*‖u‖*‖w‖ := by
    exact (norm_first_fderiv_mul_at hS (hU u i) (hU w j) hy).trans (by
      calc
        _ ≤ (J0*‖u‖)*(J1*‖w‖)+(J1*‖u‖)*(J0*‖w‖) := by
          gcongr <;> first | exact hU0 _ _ | exact hU1 _ _
        _ = _ := by ring)
  have hB2 (i j : I) : ‖fderiv ℝ (fderiv ℝ (B i j)) y‖ ≤ (2*J0*J2+2*J1^2)*‖u‖*‖w‖ := by
    exact (norm_second_fderiv_mul_at hS (hU u i) (hU w j) hy).trans (by
      calc
        _ ≤ (J0*‖u‖)*(J2*‖w‖)+2*(J1*‖u‖)*(J1*‖w‖)+(J2*‖u‖)*(J0*‖w‖) := by
          gcongr <;> first | exact hU0 _ _ | exact hU1 _ _ | exact hU2 _ _
        _ = _ := by ring)
  have hTerm (i j : I) : ‖iteratedFDeriv ℝ 2 (fun x => A i j x*B i j x) y‖ ≤ P*‖u‖*‖w‖ := by
    rw [norm_iteratedFDeriv_two_eq_nested]
    exact (norm_second_fderiv_mul_at hS (hA i j) (hB i j) hy).trans (by
      calc
        _ ≤ K*((2*J0*J2+2*J1^2)*‖u‖*‖w‖)+2*(M1*V0)*(2*J0*J1*‖u‖*‖w‖)+
            (M1*V1+M2*V0^2)*(J0^2*‖u‖*‖w‖) := by
          gcongr
          · exact hA0 i j
          · exact hB2 i j
          · exact hA1 i j
          · exact hB1 i j
          · exact hA2 i j
          · exact hB0 i j
        _ = _ := by dsimp only [P];ring)
  have hFun : (fun x => metricPair g (E x) (J x u) (J x w)) =
      (fun x => ∑ i,∑ j,A i j x*B i j x) := by
    funext x
    simp only [metricPair,A,B,U]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [← norm_iteratedFDeriv_two_eq_nested,hFun]
  calc
    _ ≤ ∑ i : I,‖iteratedFDeriv ℝ 2 (fun x => ∑ j,A i j x*B i j x) y‖ :=
      norm_iteratedFDeriv_finite_sum_le _ _ y 2 (fun i _ =>
        (ContDiffOn.sum (fun j _ => (hA i j).mul (hB i j))).contDiffAt (hS.mem_nhds hy))
    _ ≤ ∑ i : I,∑ j : I,‖iteratedFDeriv ℝ 2 (fun x => A i j x*B i j x) y‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_iteratedFDeriv_finite_sum_le _ _ y 2
        (fun j _ => ((hA i j).mul (hB i j)).contDiffAt (hS.mem_nhds hy))
    _ ≤ ∑ _i : I,∑ _j : I,P*‖u‖*‖w‖ :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hTerm i j))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];dsimp [P];ring

end ShrinkingSpheres

import Proof.LocalJetEnvelopeBounds
import Proof.NormalVerticalThirdDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- The coordinate normal pullback tensor before choosing or differentiating a frame. -/
def jointNormalMetricPair (g : MetricField) (expMap : X × X → X) (u w : X) (p : X × X) : ℝ :=
  metricPair g (expMap p) (normalVerticalJacobian expMap p.1 p.2 u)
    (normalVerticalJacobian expMap p.1 p.2 w)

/-- Full third joint jets of the actual pullback tensor use four jets of the
    exponential map. The same fixed tangent witnesses occur in every term. -/
theorem norm_jointNormalMetricPair_third_jet_envelope (g : MetricField) (E : X × X → X)
    (p : X × X) (u w : X) (hE : ContDiffAt ℝ ∞ E p)
    (hMetric : ∀ i j,ContDiffAt ℝ ∞ (fun x => g x i j) (E p))
    (C V : ℝ) (hC : 0 ≤ C) (hV : 1 ≤ V)
    (hG : ∀ i j n,n ≤ 3 → ‖iteratedFDeriv ℝ n (fun x => g x i j) (E p)‖ ≤ C)
    (hJets : ∀ n,1 ≤ n → n ≤ 4 → ‖iteratedFDeriv ℝ n E p‖ ≤ V) :
    ∀ n,n ≤ 3 → ‖iteratedFDeriv ℝ n (jointNormalMetricPair g E u w) p‖ ≤
      3456*C*V^5*‖u‖*‖w‖ := by
  let A (i j : I) (q : X × X) := g (E q) i j
  let U (z : X) (i : I) (q : X × X) := fderiv ℝ E q ((0:X),z) i
  let B (i j : I) (q : X × X) := U u i q*U w j q
  let CA := 6*C*V^3
  let CB := 8*V^2*‖u‖*‖w‖
  have hV0 : 0 ≤ V := zero_le_one.trans hV
  have hCA : 0 ≤ CA := by dsimp [CA];positivity
  have hCB : 0 ≤ CB := by dsimp [CB];positivity
  have hA (i j : I) : ContDiffAt ℝ ∞ (A i j) p := (hMetric i j).comp p hE
  have hDE := hE.fderiv_right (m:=∞) (by simp)
  have hU (z : X) (i : I) : ContDiffAt ℝ ∞ (U z i) p :=
    (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.contDiffAt.comp p (hDE.clm_apply contDiffAt_const)
  have hB (i j : I) : ContDiffAt ℝ ∞ (B i j) p := (hU u i).mul (hU w j)
  have hAJet (i j : I) (n : ℕ) (hn : n ≤ 3) : ‖iteratedFDeriv ℝ n (A i j) p‖ ≤ CA :=
    norm_iteratedFDeriv_comp_three_envelope E (fun x => g x i j) p hE (hMetric i j) C V hC hV
      (hG i j) (fun k hk hk3 => hJets k hk (by omega)) n hn
  have hUJet (z : X) (i : I) (n : ℕ) (hn : n ≤ 3) :
      ‖iteratedFDeriv ℝ n (U z i) p‖ ≤ V*‖z‖ := by
    have hEval := norm_iteratedFDeriv_clm_apply_const (c:=((0:X),z)) hDE (n:=n) (by simp)
    have hProj := (EuclideanSpace.proj (𝕜:=ℝ) i).norm_iteratedFDeriv_comp_left
      (hDE.clm_apply (contDiffAt_const (c:=((0:X),z)))) (n:=n) (by simp)
    have hb : ‖iteratedFDeriv ℝ n (U z i) p‖ ≤ ‖iteratedFDeriv ℝ n (fun q => fderiv ℝ E q ((0:X),z)) p‖ :=
      hProj.trans ((mul_le_mul_of_nonneg_right (norm_euclidean_proj_le_one i) (norm_nonneg _)).trans_eq (one_mul _))
    have hJet := hJets (n+1) (by omega) (by omega)
    rw [norm_iteratedFDeriv_fderiv] at hEval
    exact (hb.trans hEval).trans ((mul_le_mul_of_nonneg_left hJet (norm_nonneg _)).trans_eq (by
      simp only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg z)];ring))
  have hBJet (i j : I) (n : ℕ) (hn : n ≤ 3) : ‖iteratedFDeriv ℝ n (B i j) p‖ ≤ CB := by
    have hb := norm_iteratedFDeriv_mul_envelope_at (U u i) (U w j) p n (hU u i) (hU w j)
      (V*‖u‖) (V*‖w‖) (by positivity) (by positivity)
      (fun k hk => hUJet u i k (hk.trans hn)) (fun k hk => hUJet w j k (hk.trans hn))
    have hPow : (2:ℝ)^n ≤ 8 := (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn).trans_eq (by norm_num)
    exact hb.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPow (by positivity))
      (by positivity)).trans_eq (by dsimp only [CB];ring))
  intro n hn
  have hTerm (i j : I) : ‖iteratedFDeriv ℝ n (fun q => A i j q*B i j q) p‖ ≤
      384*C*V^5*‖u‖*‖w‖ := by
    have hb := norm_iteratedFDeriv_mul_envelope_at (A i j) (B i j) p n (hA i j) (hB i j)
      CA CB hCA hCB (fun k hk => hAJet i j k (hk.trans hn)) (fun k hk => hBJet i j k (hk.trans hn))
    have hPow : (2:ℝ)^n ≤ 8 := (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn).trans_eq (by norm_num)
    exact hb.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPow hCA) hCB).trans_eq
      (by dsimp only [CA,CB];ring))
  have hFun : jointNormalMetricPair g E u w = (fun q => ∑ i,∑ j,A i j q*B i j q) := by
    funext q
    simp only [jointNormalMetricPair,normalVerticalJacobian,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply,metricPair,A,B,U]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hFun,iteratedFDeriv_fun_sum_apply (fun i _ =>
    (ContDiffAt.sum (fun j _ => (hA i j).mul (hB i j))).of_le (by simp))]
  calc
    _ ≤ ∑ i : I,‖iteratedFDeriv ℝ n (fun q => ∑ j,A i j q*B i j q) p‖ := norm_sum_le _ _
    _ ≤ ∑ i : I,∑ j : I,‖iteratedFDeriv ℝ n (fun q => A i j q*B i j q) p‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [iteratedFDeriv_fun_sum_apply (fun j _ => ((hA i j).mul (hB i j)).of_le (by simp))]
      exact norm_sum_le _ _
    _ ≤ ∑ _i : I,∑ _j : I,384*C*V^5*‖u‖*‖w‖ :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hTerm i j))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

end ShrinkingSpheres

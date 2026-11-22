module

public import Proof.CalderonN.AffinePullbackJetBounds
public import Proof.CalderonN.CenterDerivativeSlice

import Proof.CalderonN.FirstDensityJetBounds
import Proof.CalderonN.EnlargedNormalInverse
import Mathlib.Tactic

/-! The affine center path supplies the same first parameter jet as the
actual parallel frame and normalized density along the center curve. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option maxSynthPendingDepth 32
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

@[expose] def centerInverseDensity (d : Data dim) (y : X dim) : ℝ :=
  (firstMetricDensityFactor d.γ d.g₁ y)⁻¹

@[expose] def parallelFrameFirstJet (d : Data dim) (y a : X dim) : FrameOperator dim :=
  -(connectionBilinear d.γ y a).comp (frameVectorLinear d.frame y)

@[expose] def actualCenterCoefficientFamilyJet (d : Data dim) (y a : X dim) :
    CenterParameters dim → Mat dim :=
  affineNormalCoefficient d y a (frameVectorLinear d.frame y) (parallelFrameFirstJet d y a)
    (centerInverseDensity d y) (fderiv ℝ (centerInverseDensity d) y a)

@[expose] def actualCenterNormalCoefficientDerivative (d : Data dim) (y a : X dim) :
    X dim → Mat dim :=
  centerDerivativeSlice (actualCenterCoefficientFamilyJet d y a)

theorem Background.contDiffOn_centerInverseDensity {Ω : Set (X dim)} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {d : Data dim}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) :
    ContDiffOn ℝ ∞ (centerInverseDensity d) Ω :=
  (hB.firstMetricDensityFactor_smooth hK).inv (fun y _ => (firstMetricDensityFactor_pos _ _ y).ne')

theorem exists_actualCenterCoefficientFamily_jet_bound (dim : ℕ) [NeZero dim]
    {m : ℕ} (hm : 5 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (hK : 1 ≤ K) :
    ∃ B ≥ (0 : ℝ), ∀ {Y Ω : Set (X dim)}, IsOpen Y → IsOpen Ω →
      ∀ {ρ c₀ floor ε : ℝ} {Cj : Fin 9 → ℝ} {d : Data dim},
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y, ∀ a v : X dim,
        ‖a‖ ≤ K → ‖v‖ ≤ 1 → ‖frameVectorLinear d.frame y v‖ ≤ 1 →
        metricPair d.γ y (frameVectorLinear d.frame y v) (frameVectorLinear d.frame y v) <
          (max ρ (d.radius y))^2 →
        ‖normalVerticalJacobian d.expMap y (frameVectorLinear d.frame y v)
          -ContinuousLinearMap.id ℝ (X dim)‖ ≤ (1/2 : ℝ) →
        ContDiffAt ℝ ∞ (actualCenterCoefficientFamilyJet d y a) ((0 : ℝ),v) ∧
          ∀ j, j ≤ 3 →
            ‖iteratedFDeriv ℝ j (actualCenterCoefficientFamilyJet d y a) ((0 : ℝ),v)‖ ≤ B := by
  have hK' : 0 < K := zero_lt_one.trans_le hK
  let G : ℝ := ∑ i : Fin (m+1), |M i|
  have hG : 0 ≤ G := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let A := 1+K+3*(dim : ℝ)^4*K*G*K*K
  let D := K^(dim-2)
  let CD := D+D^3*(dim-2 : ℕ)*K*G*K
  let L := max G (2*K)
  have hA : 1 ≤ A := by
    dsimp [A]
    exact (le_add_of_nonneg_right hK'.le).trans (le_add_of_nonneg_right (by positivity))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hCD : 0 ≤ CD := by dsimp [CD]; positivity
  obtain ⟨V,hV,hExp⟩ := Background.exists_normal_exp_joint_jet_envelope dim M hK' hm
  obtain ⟨S,hS,hData⟩ := exists_affineNormalPullbackData_jet_envelope dim A V G hA hV hG
  obtain ⟨T,hT,hMap⟩ := exists_pullbackDivergenceMatrix_third_jet_bound dim K L hK'
  let Q : ℝ →L[ℝ] Mat dim →L[ℝ] Mat dim := ContinuousLinearMap.lsmul ℝ ℝ
  refine ⟨8*‖Q‖*CD*(6*T*S^3),by positivity,?_⟩
  intro Y Ω hY hΩ ρ c₀ floor ε Cj d hd y hy a v ha hv hvel hDisk hNear
  let U := frameVectorLinear d.frame y
  let P := parallelFrameFirstJet d y a
  let J := normalVerticalJacobian d.expMap y (U v)
  let x := d.expMap (y,U v)
  let p : CenterParameters dim := (0,v)
  let N := affineNormalPullbackData d y a U P
  let C := pullbackDivergenceMatrix ∘ N
  let b := centerInverseDensity d y
  let b' := fderiv ℝ (centerInverseDensity d) y a
  let bF (w : CenterParameters dim) := b+w.1*b'
  have hyΩ := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hyΩ
  have hUn := hd.1.1.norm_frameVectorLinear_le hK hyΩ d.frame hFrame
  have hx : x ∈ Ω := ((hd.2.1.2 y hy).2.2 (U v) hDisk.le).1
  have hE : ContDiffAt ℝ ∞ d.expMap (y,U v) := by
    obtain ⟨O,hO,hTube,hSmooth⟩ := hd.2.1.1
    exact hSmooth.contDiffAt (hO.mem_nhds (hTube ⟨hy,hDisk.le⟩))
  have hM (j : Fin (m+1)) : |M j| ≤ G :=
    Finset.single_le_sum (fun i _ => abs_nonneg (M i)) (Finset.mem_univ j)
  have hΓ := (hd.1.1.connection_operator_bounds hΩ hK' hyΩ |M ⟨1,by omega⟩| |M ⟨2,by omega⟩|
      (abs_nonneg _) (abs_nonneg _)
      (fun i j => (hd.1.reference_fderiv_bound (by omega) hyΩ i j).trans (le_abs_self _))
      (fun i j => (hd.1.reference_second_fderiv_bound (by omega) hyΩ i j).trans (le_abs_self _))).1
  have hCΓ : ‖connectionBilinear d.γ y‖ ≤ 3*(dim : ℝ)^4*K*G := by
    refine hΓ.trans ?_
    calc
      _ = 3*(dim : ℝ)^4*K*|M ⟨1,by omega⟩| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hM _) (by positivity)
  have hPnorm : ‖P‖ ≤ A := by
    dsimp only [P,parallelFrameFirstJet]
    rw [norm_neg]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine (mul_le_mul ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul hCΓ ha (norm_nonneg _) (by positivity))) hUn (norm_nonneg _) (by positivity)).trans ?_
    dsimp [A]
    linarith only [hK]
  have hKA : K ≤ A := by
    dsimp [A]
    exact (le_add_of_nonneg_left zero_le_one).trans (le_add_of_nonneg_right (by positivity))
  have hR : ContinuousOn (fun y => max ρ (d.radius y)) Y :=
    fun z hz => by
      have hr : ContinuousAt (fun x => max ρ (d.radius x)) z :=
        continuousAt_const.max ((hd.2.2.2.2.1.1.contDiffAt (hY.mem_nhds hz)).continuousAt)
      exact hr.continuousWithinAt
  have hg : ContDiffAt ℝ ∞ d.g₁ x := by
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    exact (hd.1.2.1.1 i j).contDiffAt (hΩ.mem_nhds hx)
  have hgj (j : ℕ) (hj : j ≤ 3) : ‖iteratedFDeriv ℝ j d.g₁ x‖ ≤ G := by
    apply norm_iteratedFDeriv_matrix_le_of_entries d.g₁ x j hg hG
    intro i k
    let l : Fin (m+1) := ⟨j,by omega⟩
    exact ((hd.1.2.2.2.2.1 d.g₁ (by simp) l i k x hx).trans (le_abs_self _)).trans (hM l)
  obtain ⟨hN,hNj⟩ := hData d y a v U P (ha.trans hKA) hv (hUn.trans hKA) hPnorm
    ⟨hE,hg,hExp hY hΩ hd.1 hd.2.1 hR hy (U v) hDisk hvel,hgj⟩
  have hJnorm : ‖J‖ ≤ 2 := by
    calc
      _ = ‖(J-ContinuousLinearMap.id ℝ (X dim))+ContinuousLinearMap.id ℝ (X dim)‖ := by rw [sub_add_cancel]
      _ ≤ ‖J-ContinuousLinearMap.id ℝ (X dim)‖+‖ContinuousLinearMap.id ℝ (X dim)‖ := norm_add_le _ _
      _ ≤ (1/2:ℝ)+1 := add_le_add hNear ContinuousLinearMap.norm_id_le
      _ ≤ 2 := by norm_num
  have hNval : N p = (d.g₁ x,J.comp U) := by
    simp [N,p,affineNormalPullbackData,affineNormalInput,affineCenterFrame,x,J]
  have hNnorm : ‖N p‖ ≤ L := by
    rw [hNval,Prod.norm_mk]
    exact max_le_max (by simpa only [norm_iteratedFDeriv_zero] using hgj 0 (by omega))
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hJnorm hUn (norm_nonneg _) (by norm_num)))
  have hTLo (u : X dim) : ‖u‖ ≤ 2*K*‖(J.comp U) u‖ := by
    have he := (hd.1.1.frameVector_norm_sq_bounds hK' hyΩ d.frame hFrame u).1
    rw [← frameVectorLinear_apply] at he
    have hULo : ‖u‖ ≤ K*‖U u‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      have hKK : K ≤ K^2 := by nlinarith
      exact he.trans ((mul_le_mul_of_nonneg_right hKK (sq_nonneg ‖U u‖)).trans_eq (by ring))
    have hErr := ((J-ContinuousLinearMap.id ℝ (X dim)).le_opNorm (U u)).trans
      (mul_le_mul_of_nonneg_right hNear (norm_nonneg _))
    change ‖J (U u)-U u‖ ≤ _ at hErr
    have hTri := norm_sub_le (J (U u)) (J (U u)-U u)
    rw [sub_sub_cancel] at hTri
    have hf := mul_le_mul_of_nonneg_left (show ‖U u‖ ≤ 2*‖J (U u)‖ by linarith) hK'.le
    exact hULo.trans (hf.trans_eq (by rw [ContinuousLinearMap.comp_apply]; ring))
  obtain ⟨hθ,hθ₁,hθ₂,hθ₃,hθ₀⟩ := hMap (N p) hNnorm
    (by rw [hNval]; exact (hd.1.2.1.2 _ hx).1)
    (fun u => by rw [hNval]; exact ((hd.1.2.1.2 _ hx).2 u).1)
    (fun u => by rw [hNval]; exact hTLo u)
  have hC : ContDiffAt ℝ ∞ C p := hθ.comp p hN
  have hCj (j : ℕ) (hj : j ≤ 3) : ‖iteratedFDeriv ℝ j C p‖ ≤ 6*T*S^3 := by
    refine norm_iteratedFDeriv_comp_three_envelope N pullbackDivergenceMatrix p hN hθ T S hT hS
      (fun i hi => ?_) (fun i _ hi => hNj i hi) j hj
    interval_cases i
    · simpa only [norm_iteratedFDeriv_zero] using hθ₀
    · simpa only [norm_iteratedFDeriv_one] using hθ₁
    · rw [← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one]
      exact hθ₂
    · rw [← norm_iteratedFDeriv_fderiv (n:=2),← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one]
      exact hθ₃
  have hb : ‖b‖ ≤ D := by
    rw [Real.norm_eq_abs,show b = (firstMetricDensityFactor d.γ d.g₁ y)⁻¹ from rfl,
      abs_of_pos (inv_pos.mpr (firstMetricDensityFactor_pos _ _ _))]
    exact hd.1.firstMetricDensityFactor_inverse_le hK' hyΩ
  have hb' : ‖b'‖ ≤ D^3*(dim-2 : ℕ)*K*G*K := by
    let f := firstMetricDensityFactor d.γ d.g₁
    have h := (hd.1.firstMetricDensityFactor_jet_bounds hΩ hK' (by omega : 2 ≤ m) hyΩ).1
    have hf := ((hd.1.firstMetricDensityFactor_smooth hK').contDiffAt
      (hΩ.mem_nhds hyΩ)).differentiableAt (by simp)
    have hBder := (hasFDerivAt_inv (firstMetricDensityFactor_pos d.γ d.g₁ y).ne').comp y hf.hasFDerivAt
    have hEq : b' = -(b^2)*(fderiv ℝ f y a) := by
      change fderiv ℝ ((fun x : ℝ => x⁻¹) ∘ f) y a = _
      rw [hBder.fderiv,ContinuousLinearMap.comp_apply]
      change (fderiv ℝ f y a) * (-(f y ^ 2)⁻¹) = -(b^2) * fderiv ℝ f y a
      rw [← inv_pow, mul_comm]
      rfl
    rw [hEq,norm_mul,norm_neg,norm_pow]
    have hh := (fderiv ℝ f y).le_opNorm a
    exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hb 2)
      (hh.trans (mul_le_mul h ha (norm_nonneg _) (by positivity))) (norm_nonneg _) (by positivity)).trans
      (by have hn := hM ⟨1,by omega⟩
          calc
            _ = D^3*(dim-2 : ℕ)*K*|M ⟨1,by omega⟩| * K := by ring
            _ ≤ _ := by gcongr)
  let Lb := (ContinuousLinearMap.fst ℝ ℝ (X dim)).smulRight b'
  have hLb : ‖Lb‖ ≤ CD := by
    apply ContinuousLinearMap.opNorm_le_bound _ hCD
    intro w
    change ‖w.1 • b'‖ ≤ _
    rw [norm_smul,mul_comm]
    exact mul_le_mul (hb'.trans (by dsimp [CD]; linarith)) (norm_fst_le w) (norm_nonneg _) hCD
  have hbF : ContDiffAt ℝ ∞ bF p := (contDiff_const.add (contDiff_fst.mul contDiff_const)).contDiffAt
  have hbFj (j : ℕ) (_hj : j ≤ 3) : ‖iteratedFDeriv ℝ j bF p‖ ≤ CD := by
    exact norm_iteratedFDeriv_affine_envelope_at Lb b p j CD hCD
      (by change ‖b+(0:ℝ) • b'‖ ≤ CD; rw [zero_smul,add_zero]; exact hb.trans
            (le_add_of_nonneg_right (by positivity))) hLb
  refine ⟨(Q.contDiff.contDiffAt.comp p hbF).clm_apply hC,fun j hj => ?_⟩
  have hPow : (2:ℝ)^j ≤ 8 := (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj).trans_eq (by norm_num)
  exact (norm_iteratedFDeriv_bilinear_envelope_at Q bF C p j hbF hC CD (6*T*S^3) hCD
    (by positivity) (fun k hk => hbFj k (hk.trans hj)) (fun k hk => hCj k (hk.trans hj))).trans (by gcongr)

end CalderonN

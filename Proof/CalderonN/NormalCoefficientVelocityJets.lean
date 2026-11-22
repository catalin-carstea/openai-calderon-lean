module

public import Proof.CalderonN.PullbackCoefficientJetBounds
public import Proof.CalderonN.NormalVerticalThirdDerivative
public import Proof.CalderonN.UniformFirstDensityTaylor

import Proof.CalderonN.SecondDerivativeCompositionBounds
import Proof.CalderonN.ThirdDerivativeProductBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Proof.CalderonN.BackgroundBudgets
import Proof.CalderonN.MetricConnection
import Proof.CalderonN.NormalVerticalJacobian
import Proof.CalderonN.NormalJacobianInverse
import Proof.CalderonN.NormalMapDerivativeTaylor
import Proof.CalderonN.FirstMetricConformalFactor
import Proof.CalderonN.FirstMetricConformalDepth
import Proof.CalderonN.ConnectionOperatorBounds
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise
set_option maxHeartbeats 4300000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The normalized coefficient evaluated at an independent initial velocity. -/
@[expose] def firstNormalVelocityCoefficient (d : Data dim) (y v : X dim) : Mat dim :=
  (firstMetricDensityFactor d.γ d.g₁ y)⁻¹ •
    pullbackDivergenceMatrix (d.g₁ (d.expMap (y,v)),
      (normalVerticalJacobian d.expMap y v).comp (frameVectorLinear d.frame y))

theorem firstNormalVelocityCoefficient_rescaled (d : Data dim) (y z : X dim) (s : ℝ) (i j : I dim) :
    firstNormalVelocityCoefficient d y (s • frameVector d.frame y z) i j =
      normalizedFirstNormalCoeff d y s z i j := by
  let v := s • frameVector d.frame y z
  let T := (normalVerticalJacobian d.expMap y v).comp (frameVectorLinear d.frame y)
  have hT (a b : I dim) : coordinateMatrix T a b = (normalVerticalJacobian d.expMap y v (d.frame y b)) a := by
    simp only [coordinateMatrix_apply,T,ContinuousLinearMap.comp_apply,frameVectorLinear_apply,frameVector_axis]
  have hM : pullbackMetricMatrix (d.g₁ (d.expMap (y,v)),T) =
      framedNormalMetric d.g₁ d.frame d.expMap y s z := by
    ext a b
    simp only [pullbackMetricMatrix,Matrix.mul_apply,Matrix.transpose_apply,hT,framedNormalMetric,
      normalPullbackMetricPair,metricPair]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [v,normalVerticalJacobian,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply]
    ring
  change ((firstMetricDensityFactor d.γ d.g₁ y)⁻¹ •
    pullbackDivergenceMatrix (d.g₁ (d.expMap (y,v)),T)) i j = _
  rw [pullbackDivergenceMatrix,hM]
  simp only [normalizedFirstNormalCoeff,divergenceCoeff,chartVolume,Matrix.smul_apply,smul_eq_mul,div_eq_mul_inv]
  ring

theorem Background.firstMetricDensityFactor_inverse_le {Ω : Set (X dim)} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField dim} {e : Frame dim}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) {x : X dim} (hx : x ∈ Ω) :
    (firstMetricDensityFactor γ g₁ x)⁻¹ ≤ K^(dim-2) := by
  have hγ := ((hB.1.2 x hx).2 (axis (0 : I dim))).2
  have hg := ((hB.2.1.2 x hx).2 (axis (0 : I dim))).1
  have hEntry (g : MetricField dim) : metricPair g x (axis (0 : I dim)) (axis (0 : I dim)) = g x 0 0 := by
    simp [metricPair,axis]
  rw [hEntry,norm_axis,one_pow,mul_one] at hγ hg
  have hc : (K⁻¹)^2 ≤ (firstMetricScale γ g₁ x)^2 := by
    rw [hB.firstMetricScale_sq hK hx,firstMetricConformalFactor,div_eq_mul_inv,pow_two]
    exact mul_le_mul hg ((inv_le_inv₀ hK (hB.1.diagonal_entry_pos hK hx 0)).2 hγ)
      (inv_nonneg.mpr hK.le) (hB.2.1.diagonal_entry_pos hK hx 0).le
  have hS : K⁻¹ ≤ firstMetricScale γ g₁ x :=
    (sq_le_sq₀ (inv_nonneg.mpr hK.le) (firstMetricScale_pos γ g₁ x).le).1 hc
  rw [firstMetricDensityFactor,← inv_pow]
  exact pow_le_pow_left₀ (inv_nonneg.mpr (firstMetricScale_pos γ g₁ x).le)
    (by simpa only [inv_inv] using (inv_le_inv₀ (firstMetricScale_pos γ g₁ x) (inv_pos.mpr hK)).2 hS) _

/-- Uniform second spatial jets are taken before the rescaling. The
admissible normal map is the same one used for the Dirichlet problem. -/
theorem exists_normalVelocityCoefficient_second_jet_bound
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ B ≥ (0 : ℝ), ∀ floor ε d, Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ y ∈ Y, ∀ v ∈ interior (disk d.γ y (max ρ (d.radius y))), ‖v‖ ≤ 1 →
      ‖normalVerticalJacobian d.expMap y v-ContinuousLinearMap.id ℝ (X dim)‖ ≤ (1/2 : ℝ) →
      ContDiffAt ℝ ∞ (firstNormalVelocityCoefficient d y) v ∧
        ‖fderiv ℝ (fderiv ℝ (firstNormalVelocityCoefficient d y)) v‖ ≤ B ∧
        (firstNormalVelocityCoefficient d y v).PosDef := by
  let M₀ := |M 0|
  let M₁ := |M ⟨1,by omega⟩|
  let M₂ := |M ⟨2,by omega⟩|
  let C := 3*(dim:ℝ)^4*K*M₁
  let D := backgroundConnectionDerivativeBudget dim (by omega) K M
  let H := backgroundSecondConnectionBudget dim (by omega) K M
  let F := backgroundThirdConnectionBudget dim hm K M
  let J₁ := secondNormalVariationBudget K C D H
  let J₂ := thirdNormalVariationBudget K C D H F
  let L := max M₀ (2*K)
  have hK' : 0 < K := zero_lt_one.trans_le hK
  have hM₁ : 0 ≤ M₁ := abs_nonneg _
  have hM₂ : 0 ≤ M₂ := abs_nonneg _
  have hC : 0 ≤ C := by dsimp [C,M₁]; positivity
  have hD : 0 ≤ D := by dsimp [D,backgroundConnectionDerivativeBudget]; positivity
  have hH : 0 ≤ H := by dsimp [H,backgroundSecondConnectionBudget,secondConnectionBudget]; positivity
  have hF : 0 ≤ F := by dsimp [F,backgroundThirdConnectionBudget,thirdConnectionBudget]; positivity
  have hJ₁ : 0 ≤ J₁ := by dsimp only [J₁,secondNormalVariationBudget]; positivity
  have hJ₂ : 0 ≤ J₂ := by dsimp only [J₂,thirdNormalVariationBudget,secondNormalVariationBudget]; positivity
  obtain ⟨B,hB,hJet⟩ := exists_pullbackDivergenceMatrix_jet_bound dim K L hK'
  let B₁ := max (M₁*2) (J₁*K)
  let B₂ := max (M₁*J₁+M₂*2^2) (J₂*K)
  have hB₁ : 0 ≤ B₁ := (by positivity : 0 ≤ M₁*2).trans (le_max_left _ _)
  have hB₂ : 0 ≤ B₂ := (by positivity : 0 ≤ M₁*J₁+M₂*2^2).trans (le_max_left _ _)
  refine ⟨K^(dim-2)*(B*B₂+B*B₁^2),by positivity,?_⟩
  intro floor ε d hd y hy v hv hv₁ hvJ
  let Xmap : X dim → X dim := fun z => d.expMap (y,z)
  let J := normalVerticalJacobian d.expMap y
  let U := frameVectorLinear d.frame y
  let W := d.g₁ ∘ Xmap
  let T : X dim → (X dim →L[ℝ] X dim) := fun z => (J z).comp U
  let P : X dim → PullbackCoefficientData dim := fun z => (W z,T z)
  have hvd := interior_subset hv
  have hx : Xmap v ∈ Ω := ((hd.2.1.2 y hy).2.2 v hvd).1
  have hyΩ := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hyΩ
  have hU := hd.1.1.norm_frameVectorLinear_le hK hyΩ d.frame hFrame
  have hConn (x : X dim) (hx : x ∈ Ω) :=
    hd.1.1.connection_operator_bounds hΩ hK' hx M₁ M₂ hM₁ hM₂
      (fun i j => (hd.1.reference_fderiv_bound (by omega) hx i j).trans (le_abs_self _))
      (fun i j => (hd.1.reference_second_fderiv_bound (by omega) hx i j).trans (le_abs_self _))
  have hΓ₀ (x : X dim) (hx : x ∈ Ω) : ‖connectionBilinear d.γ x‖ ≤ C := (hConn x hx).1.trans_eq (by dsimp only [C]; ring)
  have hΓ₁ (x : X dim) (hx : x ∈ Ω) : ‖fderiv ℝ (connectionBilinear d.γ) x‖ ≤ D := (hConn x hx).2
  have hΓ₂ (x : X dim) (hx : x ∈ Ω) := hd.1.connection_second_derivative_budget hΩ hK' (by omega : 3 ≤ m) hx
  have hΓ₃ (x : X dim) (hx : x ∈ Ω) := hd.1.connection_third_derivative_budget hΩ hK' hm hx
  have hJnorm : ‖J v‖ ≤ 2 := by
    calc
      _ = ‖(J v-ContinuousLinearMap.id ℝ (X dim))+ContinuousLinearMap.id ℝ (X dim)‖ := by rw [sub_add_cancel]
      _ ≤ ‖J v-ContinuousLinearMap.id ℝ (X dim)‖+‖ContinuousLinearMap.id ℝ (X dim)‖ := norm_add_le _ _
      _ ≤ (1/2:ℝ)+1 := add_le_add hvJ ContinuousLinearMap.norm_id_le
      _ ≤ 2 := by norm_num
  have hJderiv : ‖fderiv ℝ J v‖ ≤ J₁ := by
    have h := hd.1.normalVerticalJacobian_derivative_bound hΩ hK' (by omega : 3 ≤ m) hd.2.1 hy v hv hv₁
    exact h
  have hJsecond : ‖fderiv ℝ (fderiv ℝ J) v‖ ≤ J₂ :=
    hd.2.1.normalVerticalJacobian_second_derivative_bound hΩ hd.1.1 hK' hC hD hH hF
      hΓ₀ hΓ₁ hΓ₂ hΓ₃ hy v hv hv₁
  have hDJ : ContDiffAt ℝ ∞ J v := hd.2.1.contDiffAt_normalVerticalJacobian hy v hvd
  have hX : ContDiffAt ℝ ∞ Xmap v := by
    obtain ⟨O,hO,hTube,hSmooth⟩ := hd.2.1.1
    exact (hSmooth.contDiffAt (hO.mem_nhds (hTube ⟨hy,hvd⟩))).comp v
      (contDiffAt_const.prodMk contDiffAt_id)
  have hXDeriv : fderiv ℝ Xmap =ᶠ[𝓝 v] J := by
    filter_upwards [isOpen_interior.mem_nhds hv] with w hw
    exact (hd.2.1.hasFDerivAt_velocity_slice hy w (interior_subset hw)).fderiv
  have hG : ContDiffAt ℝ ∞ d.g₁ (Xmap v) := by
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    exact (hd.1.2.1.1 i j).contDiffAt (hΩ.mem_nhds hx)
  have hGj (j : Fin (m+1)) (i l : I dim) :
      ‖iteratedFDeriv ℝ j.val (fun x => d.g₁ x i l) (Xmap v)‖ ≤ |M j| :=
    (hd.1.2.2.2.2.1 d.g₁ (by simp) j i l _ hx).trans (le_abs_self _)
  have hG₀ : ‖W v‖ ≤ M₀ := (Matrix.norm_le_iff (abs_nonneg _)).2 fun i j =>
    by simpa only [W,Function.comp_apply,Fin.val_zero,norm_iteratedFDeriv_zero] using hGj 0 i j
  have hG₁ : ‖fderiv ℝ d.g₁ (Xmap v)‖ ≤ M₁ :=
    norm_fderiv_matrix_le_of_entries _ _ (hG.differentiableAt (by simp)) _ hM₁ fun i j =>
      by simpa only [norm_iteratedFDeriv_one] using hGj ⟨1,by omega⟩ i j
  have hG₂ : ‖fderiv ℝ (fderiv ℝ d.g₁) (Xmap v)‖ ≤ M₂ :=
    norm_second_fderiv_matrix_le_of_entries _ _ hG _ hM₂ fun i j =>
      by simpa only [← norm_iteratedFDeriv_fderiv (n := 1),norm_iteratedFDeriv_one] using hGj ⟨2,by omega⟩ i j
  have hW : ContDiffAt ℝ ∞ W v := hG.comp v hX
  have hW₁ : ‖fderiv ℝ W v‖ ≤ M₁*2 := by
    dsimp only [W]
    rw [fderiv_comp v (hG.differentiableAt (by simp)) (hX.differentiableAt (by simp)),hXDeriv.eq_of_nhds]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hG₁ hJnorm (norm_nonneg _) hM₁)
  have hW₂ : ‖fderiv ℝ (fderiv ℝ W) v‖ ≤ M₁*J₁+M₂*2^2 := by
    refine (norm_second_fderiv_comp_at Xmap d.g₁ v hX hG).trans ?_
    rw [hXDeriv.fderiv_eq,hXDeriv.eq_of_nhds]
    gcongr
  let Post := (ContinuousLinearMap.compL ℝ (X dim) (X dim) (X dim)).flip U
  have hPost : ‖Post‖ ≤ K := ContinuousLinearMap.opNorm_le_bound _ hK'.le fun A =>
    (ContinuousLinearMap.opNorm_comp_le A U).trans ((mul_le_mul_of_nonneg_left hU (norm_nonneg A)).trans_eq (mul_comm _ _))
  have hT : ContDiffAt ℝ ∞ T v := Post.contDiff.contDiffAt.comp v hDJ
  have hT₀ : ‖T v‖ ≤ 2*K :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hJnorm hU (norm_nonneg _) (by norm_num))
  have hT₁ : ‖fderiv ℝ T v‖ ≤ J₁*K := by
    have he := Post.norm_iteratedFDeriv_comp_left hDJ (n := 1) (by simp)
    simp only [norm_iteratedFDeriv_one] at he
    exact he.trans ((mul_le_mul hPost hJderiv (norm_nonneg _) hK'.le).trans_eq (mul_comm _ _))
  have hT₂ : ‖fderiv ℝ (fderiv ℝ T) v‖ ≤ J₂*K := by
    have he := Post.norm_iteratedFDeriv_comp_left hDJ (n := 2) (by simp)
    simp only [← norm_iteratedFDeriv_fderiv (n := 1),norm_iteratedFDeriv_one] at he
    exact he.trans ((mul_le_mul hPost hJsecond (norm_nonneg _) hK'.le).trans_eq (mul_comm _ _))
  have hP : ContDiffAt ℝ ∞ P v := hW.prodMk hT
  have hP₁ : ‖fderiv ℝ P v‖ ≤ B₁ := by
    rw [(hW.differentiableAt (by simp)).hasFDerivAt.prodMk
      (hT.differentiableAt (by simp)).hasFDerivAt |>.fderiv,ContinuousLinearMap.opNorm_prod,Prod.norm_def]
    exact max_le_max hW₁ hT₁
  have hP₂ : ‖fderiv ℝ (fderiv ℝ P) v‖ ≤ B₂ := by
    rw [← norm_iteratedFDeriv_two_eq_nested]
    change ‖iteratedFDeriv ℝ 2 (fun z => (W z,T z)) v‖ ≤ B₂
    rw [iteratedFDeriv_prodMk (hW.of_le (by simp : (2:ℕ∞ω) ≤ ∞))
      (hT.of_le (by simp : (2:ℕ∞ω) ≤ ∞)) le_rfl,ContinuousMultilinearMap.opNorm_prod,
      norm_iteratedFDeriv_two_eq_nested,norm_iteratedFDeriv_two_eq_nested]
    exact max_le_max hW₂ hT₂
  have hTLo (u : X dim) : ‖u‖ ≤ 2*K*‖T v u‖ := by
    have he := (hd.1.1.frameVector_norm_sq_bounds hK' hyΩ d.frame hFrame u).1
    rw [← frameVectorLinear_apply] at he
    have hULo : ‖u‖ ≤ K*‖U u‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      have hKK : K ≤ K^2 := by nlinarith
      exact he.trans ((mul_le_mul_of_nonneg_right hKK (sq_nonneg ‖U u‖)).trans_eq (by ring))
    have hErr := ((J v-ContinuousLinearMap.id ℝ (X dim)).le_opNorm (U u)).trans
      (mul_le_mul_of_nonneg_right hvJ (norm_nonneg _))
    have hEq : (J v-ContinuousLinearMap.id ℝ (X dim)) (U u) = J v (U u)-U u := by
      exact ContinuousLinearMap.sub_apply _ _ _
    rw [hEq] at hErr
    have hTri := norm_sub_le (J v (U u)) (J v (U u)-U u)
    rw [sub_sub_cancel] at hTri
    have h := mul_le_mul_of_nonneg_left (show ‖U u‖ ≤ 2*‖J v (U u)‖ by linarith) hK'.le
    exact hULo.trans (h.trans_eq (by dsimp only [T,ContinuousLinearMap.comp_apply];ring))
  obtain ⟨hφ,hφ₁,hφ₂⟩ := hJet (P v) (max_le_max hG₀ hT₀)
    (hd.1.2.1.2 _ hx).1 (fun u => ((hd.1.2.1.2 _ hx).2 u).1) hTLo
  let f := pullbackDivergenceMatrix ∘ P
  have hf : ContDiffAt ℝ ∞ f v := hφ.comp v hP
  have hf₂ : ‖fderiv ℝ (fderiv ℝ f) v‖ ≤ B*B₂+B*B₁^2 :=
    (norm_second_fderiv_comp_at P _ v hP hφ).trans (by gcongr)
  let c := firstMetricDensityFactor d.γ d.g₁ y
  have hc : |c⁻¹| ≤ K^(dim-2) := by
    rw [abs_of_pos (inv_pos.mpr (firstMetricDensityFactor_pos _ _ _))]
    exact hd.1.firstMetricDensityFactor_inverse_le hK' hyΩ
  have hInv : Function.Injective (T v) := by
    intro u w h
    have hN := hTLo (u-w)
    rw [map_sub,h,sub_self,norm_zero,mul_zero] at hN
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hN)
  have hPos := pullbackMetricMatrix_posDef (q := P v) (hd.1.2.1.posDef hK' hx) hInv
  have hCPos : (firstNormalVelocityCoefficient d y v).PosDef := by
    change (c⁻¹ • (Real.sqrt (pullbackMetricMatrix (P v)).det • (pullbackMetricMatrix (P v))⁻¹)).PosDef
    exact (hPos.inv.smul (Real.sqrt_pos.2 hPos.det_pos)).smul
      (inv_pos.mpr (firstMetricDensityFactor_pos _ _ _))
  change ContDiffAt ℝ ∞ (c⁻¹ • f) v ∧ ‖fderiv ℝ (fderiv ℝ (c⁻¹ • f)) v‖ ≤ _ ∧ _
  refine ⟨hf.const_smul c⁻¹,?_,hCPos⟩
  have he₁ := fderiv_const_smul_field (𝕜 := ℝ) (f := f) c⁻¹
  have he₂ := fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ f) c⁻¹
  rw [he₁,he₂]
  change ‖c⁻¹ • fderiv ℝ (fderiv ℝ f) v‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul hc hf₂ (norm_nonneg _) (by positivity)

end CalderonN

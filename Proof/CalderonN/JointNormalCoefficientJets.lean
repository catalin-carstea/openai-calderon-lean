module

public import Proof.CalderonN.CanonicalNormalCoefficientInputs
public import Proof.CalderonN.UniformNormalMapHigherJets
public import Proof.CalderonN.PullbackCoefficientFiniteJets

import Proof.CalderonN.FirstDensityJetBounds
import Proof.CalderonN.MetricConnection
import Mathlib.Tactic

/-! Joint finite jets of the actual normalized coefficient, prior to
substitution of the profile radius. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5400000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

private theorem metricField_local_jet_budget {Ω : Set (X dim)} (hΩ : IsOpen Ω) {K : ℝ}
    {m : ℕ} (M : Fin (m+1) → ℝ) {g : MetricField dim} (hg : Elliptic Ω K g)
    (hJets : ∀ (j : Fin (m+1)) i k, ∀ y ∈ Ω,
      ‖iteratedFDeriv ℝ j.val (fun x => g x i k) y‖ ≤ M j)
    {y : X dim} (hy : y ∈ Ω) :
    LocalSmoothJetBudget g y m (backgroundAllMetricJetBudget M) := by
  have hA : ContDiffAt ℝ ∞ g y := contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr
    (fun j => (hg.1 i j).contDiffAt (hΩ.mem_nhds hy)))
  refine ⟨hA,?_⟩
  intro j hj
  have hR : 0 ≤ backgroundAllMetricJetBudget M := zero_le_one.trans (backgroundAllMetricJetBudget_ge_one M)
  apply norm_iteratedFDeriv_matrix_le_of_entries g y j hA hR
  intro i k
  exact (hJets ⟨j,by omega⟩ i k y hy).trans ((le_abs_self _).trans (abs_metricJet_le_all_budget M _))

/-- At all controlled independent velocities, the actual first coefficient
has a uniform joint jet envelope in the center and velocity. -/
theorem uniform_actual_firstNormalVelocityCoefficient_jets
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ}
    (N : ℕ) (hm : N+2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ floor ε d, Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i, d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ y ∈ Y, ∀ v : X dim, metricPair d.γ y v v < (max ρ (d.radius y))^2 → ‖v‖ ≤ 1 →
      ‖normalVerticalJacobian d.expMap y v-ContinuousLinearMap.id ℝ (X dim)‖ ≤ (1/2:ℝ) →
      LocalSmoothJetBudget (fun p : X dim × X dim => firstNormalVelocityCoefficient d p.1 p.2) (y,v) N C := by
  let P := X dim × X dim
  let L := X dim →L[ℝ] X dim
  let B := backgroundAllMetricJetBudget M
  let π : P →L[ℝ] X dim := ContinuousLinearMap.fst ℝ _ _
  let R : (P →L[ℝ] X dim) →L[ℝ] L :=
    (ContinuousLinearMap.compL ℝ (X dim) P (X dim)).flip (ContinuousLinearMap.inr ℝ (X dim) (X dim))
  let Comp := ContinuousLinearMap.compL ℝ (X dim) (X dim) (X dim)
  let SM : ℝ →L[ℝ] Mat dim →L[ℝ] Mat dim := ContinuousLinearMap.lsmul ℝ ℝ
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hB : 1 ≤ B := backgroundAllMetricJetBudget_ge_one M
  obtain ⟨V,hV,hExp⟩ := uniform_normalMap_higher_jet_bounds (dim:=dim) hΩ K hKp M (N+1) hm
  obtain ⟨F,hF,hFrame⟩ := uniform_canonical_frameVectorLinear_jets (dim:=dim) K hKp M
  obtain ⟨I,hI,hInv⟩ := uniform_first_center_inverse_density_jets (dim:=dim) K hKp M
  obtain ⟨D,hD,hPullback⟩ := exists_pullbackDivergenceMatrix_finite_jet_bound (dim:=dim) K (max B (2*K)) hKp N
  let U := N.factorial*F*(max 1 ‖π‖)^N
  let S := N.factorial*I*(max 1 ‖π‖)^N
  let J := ‖R‖*V
  let Tc := (2:ℝ)^N*‖Comp‖*J*U
  let Gc := N.factorial*B*V^N
  let H := max 1 (max Gc Tc)
  let A := N.factorial*D*H^N
  let C := 1+(2:ℝ)^N*‖SM‖*S*A
  have hS₀ : 0 ≤ S := by dsimp only [S]; positivity
  have hA₀ : 0 ≤ A := by dsimp only [A,H]; positivity
  refine ⟨C,le_add_of_nonneg_right (by positivity),?_⟩
  intro floor ε d hd hdFrame y hy v hv hv₁ hJ
  let p : P := (y,v)
  let E := d.expMap
  let G (q : P) := d.g₁ (E q)
  let VJ (q : P) := normalVerticalJacobian E q.1 q.2
  let FrameL (q : P) := frameVectorLinear d.frame q.1
  let T (q : P) := (VJ q).comp (FrameL q)
  let Q (q : P) : PullbackCoefficientData dim := (G q,T q)
  let b (q : P) := (firstMetricDensityFactor d.γ d.g₁ q.1)⁻¹
  have hN := hd.2.1
  have hyΩ := hN.center_mem hy
  have hRadius : ContinuousAt (fun x => max ρ (d.radius x)) y :=
    continuousAt_const.max (((hd.2.2.2.2.1.1.continuousOn y hy).continuousAt (hY.mem_nhds hy)))
  have hVelocity : v ∈ disk d.γ y (max ρ (d.radius y)) := hv.le
  obtain ⟨W,hW,hTube,hES⟩ := hN.1
  have hESmooth : ContDiffAt ℝ ∞ E p := hES.contDiffAt (hW.mem_nhds (hTube (a:=p) ⟨hy,hVelocity⟩))
  have hEOmega : E p ∈ Ω := ((hN.2 y hy).2.2 v hVelocity).1
  have hEj (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N+1) : ‖iteratedFDeriv ℝ j E p‖ ≤ V :=
    (hExp _ _ _ _ hd.1 Y hY E _ hN y hy hRadius v hv hv₁ j hj hjN).2
  have hMatrix := (metricField_local_jet_budget hΩ M hd.1.2.1
    (hd.1.2.2.2.2.1 d.g₁ (by simp)) hEOmega).mono_order (by omega : N ≤ m)
  have hG : LocalSmoothJetBudget G p N Gc :=
    LocalSmoothJetBudget.comp_of_positive_inner hESmooth hMatrix hV (fun j hj hjN => hEj j hj (by omega))
  have hDExp : LocalSmoothJetBudget (fderiv ℝ E) p N V := by
    refine ⟨hESmooth.fderiv_right (m:=∞) (by simp),fun j hj => ?_⟩
    rw [norm_iteratedFDeriv_fderiv]
    exact hEj _ (by omega) (by omega)
  have hVJ : LocalSmoothJetBudget VJ p N J := by
    have he : VJ = R ∘ fderiv ℝ E := by
      funext q
      rfl
    rw [he]
    exact hDExp.linear_postcomp R
  have hFrameEq : d.frame = fun z => smoothMetricFrame (d.γ z) := by
    funext z i
    exact hdFrame z i
  have hFrameAt : LocalSmoothJetBudget (fun x => frameVectorLinear d.frame x) y N F := by
    rw [hFrameEq]
    exact (hFrame hΩ hd.1.1 (hd.1.2.2.2.2.1 d.γ (by simp)) y hyΩ).mono_order (by omega)
  have hFL : LocalSmoothJetBudget FrameL p N U := hFrameAt.linear_precomp π p
  have hT : LocalSmoothJetBudget T p N Tc := hVJ.bilinear hFL Comp
  have hQ : LocalSmoothJetBudget Q p N H :=
    (hG.prod hT).enlarge (le_max_right _ _)
  have hb : LocalSmoothJetBudget b p N S := ((hInv hΩ hd.1 y hyΩ).mono_order (by omega)).linear_precomp π p
  have hFramePt := hd.1.2.2.2.2.2.2.2 y hyΩ
  have hLnorm : ‖FrameL p‖ ≤ K := hd.1.1.norm_frameVectorLinear_le hK hyΩ d.frame hFramePt
  have hJnorm : ‖VJ p‖ ≤ 2 := by
    have h := norm_add_le (VJ p-ContinuousLinearMap.id ℝ (X dim)) (ContinuousLinearMap.id ℝ (X dim))
    rw [sub_add_cancel] at h
    exact h.trans ((add_le_add hJ ContinuousLinearMap.norm_id_le).trans (by norm_num))
  have hValT : ‖T p‖ ≤ 2*K := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul hJnorm hLnorm (norm_nonneg _) (by norm_num))
  have hValG : ‖G p‖ ≤ B := hMatrix.value_norm_le
  have hTLow (u : X dim) : ‖u‖ ≤ 2*K*‖T p u‖ := by
    have he := (hd.1.1.frameVector_norm_sq_bounds hKp hyΩ d.frame hFramePt u).1
    change ‖u‖^2 ≤ K*‖frameVector d.frame y u‖^2 at he
    rw [← frameVectorLinear_apply] at he
    have hu : ‖u‖ ≤ K*‖FrameL p u‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      have hKK : K ≤ K^2 := by nlinarith
      exact he.trans ((mul_le_mul_of_nonneg_right hKK (sq_nonneg ‖FrameL p u‖)).trans_eq (by ring))
    have hDiff := ((VJ p-ContinuousLinearMap.id ℝ (X dim)).le_opNorm (FrameL p u)).trans
      (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))
    rw [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply] at hDiff
    have hTri := norm_sub_le (VJ p (FrameL p u)) (VJ p (FrameL p u)-FrameL p u)
    rw [sub_sub_cancel] at hTri
    exact hu.trans ((mul_le_mul_of_nonneg_left (show ‖FrameL p u‖ ≤ 2*‖VJ p (FrameL p u)‖ by linarith)
      hKp.le).trans_eq (by dsimp only [T,ContinuousLinearMap.comp_apply]; ring))
  obtain ⟨hP,hPB⟩ := hPullback (Q p) (max_le_max hValG hValT)
    (hd.1.2.1.2 _ hEOmega).1 (fun u => ((hd.1.2.1.2 _ hEOmega).2 u).1) hTLow
  have hA : LocalSmoothJetBudget (pullbackDivergenceMatrix ∘ Q) p N A :=
    hQ.comp ⟨hP,hPB⟩ (le_max_left _ _)
  exact (hb.bilinear hA SM).enlarge (le_add_of_nonneg_left (zero_le_one : (0:ℝ) ≤ 1))

end CalderonN

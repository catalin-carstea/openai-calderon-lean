module

public import Proof.Manuscript.ScalarRestrictionSpectrum
public import Proof.Manuscript.ClosedCrossOverlap
public import Proof.Manuscript.ScalarNormalSeries

import Proof.CalderonN.StrongCrossExtension
import Mathlib.Tactic

public section

open Set Filter MeasureTheory CalderonN LocalMetricExtension
open scoped ContDiff ENNReal Topology

noncomputable section

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem SmoothOn.restrict {L : ScalarElliptic n} {D O : Set (X n)}
    (hL : L.SmoothOn D) (hOD : O ⊆ D) : L.SmoothOn O :=
  ⟨⟨fun i j => (hL.1.1 i j).mono hOD,fun x hx => hL.1.2 x (hOD hx)⟩,
    fun i => (hL.2.1 i).mono hOD,hL.2.2.mono hOD⟩

/-- A bound for the actual normal series, on one compact set and
at one selected order. -/
@[expose] def ScalarSeriesJetEstimate {D₁ D₂ : Set (X n)}
    (L₁ L₂ : ScalarElliptic n) (K : Set (X n × X n)) (k : ℕ) (C : ℝ) : Prop :=
    ∀ {ι : Type} (f : ι → ChartL2 D₁) (b : ι → ChartL2 D₂) (a c : ι → X n → ℝ),
      (∀ i, L₁.SolvesOn D₁ (a i)) → (∀ i, L₂.SolvesOn D₂ (c i)) →
      (∀ i, (f i : X n → ℝ) =ᵐ[chartMeasure D₁] a i) →
      (∀ i, (b i : X n → ℝ) =ᵐ[chartMeasure D₂] c i) →
      Summable (fun i => ‖f i‖ * ‖b i‖) →
      ∀ z ∈ K, ‖iteratedFDeriv ℝ k (fun z : X n × X n => ∑' i, a i z.1 * c i z.2) z‖ ≤
        C * (∑' i, ‖f i‖ * ‖b i‖)

open Classical in
set_option maxHeartbeats 3200000 in
/-- The scalar cross extension from a spectrum and quantitative estimate
for the actual normal series. The same function realizes every requested
jet estimate. -/
theorem scalar_crossExtension_of_spectrum_and_jets
    {D₁ D₂ S₁ S₂ O₁ O₂ : Set (X n)}
    (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂) (hConn₂ : IsConnected D₂)
    (hD₂finite : (volume : Measure (X n)) D₂ ≠ ⊤)
    (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂) (hSne₂ : S₂.Nonempty)
    (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    (hS₁D₁ : S₁ ⊆ D₁) (hS₂D₂ : S₂ ⊆ D₂)
    (hO₁D₁ : O₁ ⊆ D₁) (hO₂D₂ : O₂ ⊆ D₂)
    {L₁ L₂ : ScalarElliptic n} (hL₁ : L₁.SmoothOn D₁) (hL₂ : L₂.SmoothOn D₂)
    {C₁ C₂ γ₁ γ₂ P : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hγ₂ : 0 < γ₂) (hγ₂' : γ₂ ≤ 1)
    (hInterp₁ : L₁.Interpolates D₁ S₁ O₁ C₁ γ₁) (hInterp₂ : L₂.Interpolates D₂ S₂ O₂ C₂ γ₂)
    (hSpectrum :
      let H := scalarSolutionL2 hD₁ hL₁
      let R := closedRestrict H hS₁D₁
      ∃ (ι : Type) (w : HilbertBasis ι ℝ H) (μ : ι → ℝ),
        Countable ι ∧ (∀ i, 0 < μ i) ∧
        (∀ i, (R.adjoint ∘L R) (w i) = μ i ^ 2 • w i) ∧
        (∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0) ∧
        Summable (fun i => μ i ^ (γ₁+γ₂-1)) ∧ (∑' i, μ i ^ (γ₁+γ₂-1)) ≤ P)
    {T : Set (Set (X n × X n) × ℕ)} {C : Set (X n × X n) → ℕ → ℝ}
    (hJet : ∀ K ⊆ O₁ ×ˢ O₂, IsCompact K → ∀ j, (K,j) ∈ T →
      0 ≤ C K j ∧ ScalarSeriesJetEstimate (D₁ := O₁) (D₂ := O₂) L₁ L₂ K j (C K j))
    (F : X n × X n → ℝ) (M : ℝ) (hData : CrossData L₁ L₂ D₁ D₂ S₁ S₂ F M) :
    ∃ G, CrossExtension L₁ L₂ S₁ S₂ O₁ O₂ F G ∧
      ∀ K ⊆ O₁ ×ˢ O₂, IsCompact K → ∀ j, (K,j) ∈ T → ∀ z ∈ K,
        ‖iteratedFDeriv ℝ j G z‖ ≤ (C K j * (C₁*C₂*P)) * M := by
  classical
  let hSD₁ := hS₁D₁
  let H₁ := scalarSolutionL2 hD₁ hL₁
  let H₂ := scalarSolutionL2 hD₂ hL₂
  let R := closedRestrict H₁ hSD₁
  obtain ⟨ι,w,μ,hCnt,hμ,hEigen,hGram,hSum,hPower⟩ := hSpectrum
  let : Countable ι := hCnt
  let hLO₁ := hL₁.restrict hO₁D₁
  let hLO₂ := hL₂.restrict hO₂D₂
  let hJet₁ := scalarInteriorJets_of_smoothOn hO₁ hLO₁
  let hJet₂ := scalarInteriorJets_of_smoothOn hO₂ hLO₂
  obtain ⟨hF₁,hF₂,hMem₁,hMem₂,hNorm⟩ := hData
  let q₁ := hMem₁.toLp F
  let q₂ := hMem₂.toLp F
  have hq₁ : (q₁ : X n × X n → ℝ) =ᵐ[(chartMeasure D₁).prod (chartMeasure S₂)] F := hMem₁.coeFn_toLp
  have hq₂ : (q₂ : X n × X n → ℝ) =ᵐ[(chartMeasure S₁).prod (chartMeasure D₂)] F := hMem₂.coeFn_toLp
  have hqn₁ : ‖q₁‖ = lpNorm F 2 ((chartMeasure D₁).prod (chartMeasure S₂)) :=
    Lp.norm_toLp _ _
  have hqn₂ : ‖q₂‖ = lpNorm F 2 ((chartMeasure S₁).prod (chartMeasure D₂)) :=
    Lp.norm_toLp _ _
  change lpNorm F 2 ((chartMeasure D₁).prod (chartMeasure S₂)) +
    lpNorm F 2 ((chartMeasure S₁).prod (chartMeasure D₂)) ≤ M at hNorm
  rw [← hqn₁, ← hqn₂] at hNorm
  have hM : 0 ≤ M := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans hNorm
  have hM₁ := (le_add_of_nonneg_right (norm_nonneg q₂)).trans hNorm
  have hM₂ := (le_add_of_nonneg_left (norm_nonneg q₁)).trans hNorm
  have hSlice₁ := ae_firstArm_scalar_slices hD₁ hS₂.measurableSet hL₁ hq₁ (fun _ hy => hF₁.leftSlice hy)
  have hSlice₂ := ae_secondArm_scalar_slices hD₂ hS₁.measurableSet hL₂ hq₂ (fun _ hx => hF₂.rightSlice hx)
  have hAgree₁ : (q₁ : X n × X n → ℝ) =ᵐ[(chartMeasure S₁).prod (chartMeasure S₂)] F :=
    ae_mono (Measure.prod_mono (Measure.restrict_mono_set volume hSD₁) le_rfl) hq₁
  have hAgree₂ : (q₂ : X n × X n → ℝ) =ᵐ[(chartMeasure S₁).prod (chartMeasure S₂)] F :=
    ae_mono (Measure.prod_mono le_rfl (Measure.restrict_mono_set volume hS₂D₂)) hq₂
  have hAgree : (q₁ : X n × X n → ℝ) =ᵐ[(chartMeasure S₁).prod (chartMeasure S₂)] q₂ :=
    hAgree₁.trans hAgree₂.symm
  obtain ⟨b,Q,hBig,hSmall,hAbs,hSeries,hMass⟩ := exists_closed_crossSeries
    hSD₁ hS₂D₂ hO₁D₁ hO₂D₂ H₁ H₂ hD₂finite q₁ q₂ hAgree hSlice₁ hSlice₂
    w μ hμ hEigen hGram hC₁ hC₂ hM hγ₂ hγ₂'
    (closedInterpolation_of_interpolates hD₁ hL₁ hSD₁ hO₁D₁ hInterp₁)
    (closedInterpolation_of_interpolates hD₂ hL₂ hS₂D₂ hO₂D₂ hInterp₂) hM₁ hM₂ hSum hPower
  let fO (i : ι) : scalarSolutionL2 hO₁ hLO₁ :=
    ⟨closedRestrict H₁ hO₁D₁ (w i),closedRestrict_scalar_mem hD₁ hO₁ hO₁D₁ hL₁ (w i)⟩
  let bO (i : ι) : scalarSolutionL2 hO₂ hLO₂ :=
    ⟨closedRestrict H₂ hO₂D₂ (b i),closedRestrict_scalar_mem hD₂ hO₂ hO₂D₂ hL₂ (b i)⟩
  obtain ⟨G,a,c,hG,hQG,ha,hc,hFa,hBc,hFormula⟩ :=
    exists_smooth_scalar_productSeries hO₁ hO₂ hLO₁ hLO₂ hJet₁ hJet₂ fO bO hAbs hSeries
  let A := O₁ ∩ S₁
  let B := O₂ ∩ S₂
  have hAO : A ⊆ O₁ := inter_subset_left
  have hAS : A ⊆ S₁ := inter_subset_right
  have hBO : B ⊆ O₂ := inter_subset_left
  have hBS : B ⊆ S₂ := inter_subset_right
  have hcB (i : ι) : (bO i).1 =ᵐ[chartMeasure B] tensorCoefficient (w i).1 q₁ := by
    have hP₁ : (bO i).1 =ᵐ[chartMeasure B] (b i).1 :=
      ae_mono (Measure.restrict_mono_set volume hBO) (closedRestrict_ae H₂ hO₂D₂ (b i))
    have hP₂ : closedRestrict H₂ hS₂D₂ (b i) =ᵐ[chartMeasure B] (b i).1 :=
      ae_mono (Measure.restrict_mono_set volume hBS) (closedRestrict_ae H₂ hS₂D₂ (b i))
    rw [hSmall i] at hP₂
    exact hP₁.trans hP₂.symm
  have hcO (i : ι) : (bO i).1 =ᵐ[chartMeasure O₂] crossArmCoefficient (R (w i)) (μ i) q₂ := by
    simpa only [bO, R, hBig i] using closedRestrict_ae H₂ hO₂D₂ (b i)
  have hS₂finite := ((measure_mono hS₂D₂).trans_lt (lt_top_iff_ne_top.mpr hD₂finite)).ne
  have hLeft := closedCrossSeries_ae_eq_firstArm H₁ hO₁D₁ hBS hBO hS₂finite
    w (fun i => (bO i).1) q₁ hSlice₁ hcB hAbs hSeries
  have hRange := ae_secondArm_scalar_slices_mem_rangeClosure hD₁ hD₂ hConn₂ hS₂ hSne₂
    hSD₁ hS₂D₂ hL₁ hL₂ hD₂finite q₁ q₂ hAgree hSlice₁ hSlice₂
  have hRight := closedCrossSeries_ae_eq_secondArm H₁ hAS hAO hO₁D₁ hSD₁ hO₂D₂ hD₂finite
    w μ hμ hGram (fun i => (bO i).1) q₂ hRange hcO hAbs hSeries
  have hGLeft : (Q : X n × X n → ℝ) =ᵐ[(chartMeasure O₁).prod (chartMeasure B)] G :=
    ae_mono (Measure.prod_mono le_rfl (Measure.restrict_mono_set volume hBO)) hQG
  have hFLeft : (q₁ : X n × X n → ℝ) =ᵐ[(chartMeasure O₁).prod (chartMeasure B)] F :=
    ae_mono (Measure.prod_mono (Measure.restrict_mono_set volume hO₁D₁)
      (Measure.restrict_mono_set volume hBS)) hq₁
  have hGRight : (Q : X n × X n → ℝ) =ᵐ[(chartMeasure A).prod (chartMeasure O₂)] G :=
    ae_mono (Measure.prod_mono (Measure.restrict_mono_set volume hAO) le_rfl) hQG
  have hFRight : (q₂ : X n × X n → ℝ) =ᵐ[(chartMeasure A).prod (chartMeasure O₂)] F :=
    ae_mono (Measure.prod_mono (Measure.restrict_mono_set volume hAS)
      (Measure.restrict_mono_set volume hO₂D₂)) hq₂
  have hLeftG : EqOn G F (O₁ ×ˢ B) :=
    eqOn_open_rectangle_of_ae hO₁ (hO₂.inter hS₂)
      (hG.1.continuousOn.mono (prod_mono Subset.rfl hBO))
      (hF₁.1.continuousOn.mono (prod_mono hO₁D₁ hBS))
      (hGLeft.symm.trans (hLeft.trans hFLeft))
  have hRightG : EqOn G F (A ×ˢ O₂) :=
    eqOn_open_rectangle_of_ae (hO₁.inter hS₁) hO₂
      (hG.1.continuousOn.mono (prod_mono hAO Subset.rfl))
      (hF₂.1.continuousOn.mono (prod_mono hAS hO₂D₂))
      (hGRight.symm.trans (hRight.trans hFRight))
  refine ⟨G,⟨hG,hLeftG,hRightG⟩,?_⟩
  intro K hK hKc j hT z hz
  obtain ⟨hNonneg,hBound⟩ := hJet K hK hKc j hT
  have hAbs' : Summable (fun i => ‖(fO i).1‖ * ‖(bO i).1‖) := by
    simpa only [norm_tensorLp] using hAbs
  have hMass' : (∑' i, ‖(fO i).1‖ * ‖(bO i).1‖) ≤ C₁*C₂*M*P := by
    simpa only [norm_tensorLp] using hMass
  have hPoint := hBound (fun i => (fO i).1) (fun i => (bO i).1)
    a c ha hc hFa hBc hAbs' z hz
  rw [hFormula]
  refine hPoint.trans ((mul_le_mul_of_nonneg_left hMass' hNonneg).trans_eq ?_)
  ring


set_option maxHeartbeats 3200000 in
/-- Scalar cross continuation from the positive exponent margin, with
the actual series and a compact jet bound for each fixed pair of operators. -/
theorem exists_scalar_crossExtension_fixed
    {D₁ D₂ S₁ S₂ O₁ O₂ : Set (X n)}
    (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂) (hConn₁ : IsConnected D₁) (hConn₂ : IsConnected D₂)
    (hD₂finite : (volume : Measure (X n)) D₂ ≠ ⊤)
    (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂) (hSne₁ : S₁.Nonempty) (hSne₂ : S₂.Nonempty)
    (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    (hSc₁ : IsCompact (closure S₁)) (hS₁D₁ : closure S₁ ⊆ D₁) (hS₂D₂ : S₂ ⊆ D₂)
    (hO₁D₁ : O₁ ⊆ D₁) (hO₂D₂ : O₂ ⊆ D₂)
    {L₁ L₂ : ScalarElliptic n} (hL₁ : L₁.SmoothOn D₁) (hL₂ : L₂.SmoothOn D₂)
    {C₁ C₂ γ₁ γ₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hγ₂ : 0 < γ₂) (hγ₂' : γ₂ ≤ 1) (hγ : 0 < γ₁ + γ₂ - 1)
    (hInterp₁ : L₁.Interpolates D₁ S₁ O₁ C₁ γ₁) (hInterp₂ : L₂.Interpolates D₂ S₂ O₂ C₂ γ₂) :
    ∃ C : Set ((X n) × (X n)) → ℕ → ℝ,
      ∀ F : (X n) × (X n) → ℝ, ∀ M : ℝ, CrossData L₁ L₂ D₁ D₂ S₁ S₂ F M →
      ∃ G, CrossExtension L₁ L₂ S₁ S₂ O₁ O₂ F G ∧
        ∀ K ⊆ O₁ ×ˢ O₂, IsCompact K → ∀ j : ℕ, ∀ z ∈ K,
          ‖iteratedFDeriv ℝ j G z‖ ≤ C K j * M := by
  classical
  let hSD₁ : S₁ ⊆ D₁ := subset_closure.trans hS₁D₁
  obtain ⟨P,hP,ι,w,μ,hCnt,hμ,_,hEigen,hGram,hSum,hPower⟩ :=
    exists_scalar_restrictionSpectrum hD₁ hConn₁ hL₁ hS₁ hSne₁ hSc₁ hS₁D₁ hγ
  let hLO₁ := hL₁.restrict hO₁D₁
  let hLO₂ := hL₂.restrict hO₂D₂
  let hJet₁ := scalarInteriorJets_of_smoothOn hO₁ hLO₁
  let hJet₂ := scalarInteriorJets_of_smoothOn hO₂ hLO₂
  let hJet {K : Set (X n × X n)} (hK : K ⊆ O₁ ×ˢ O₂ ∧ IsCompact K) (j : ℕ) :=
    exists_scalar_productSeries_jetBound hO₁ hO₂ hJet₁ hJet₂ hK.2 hK.1 j
  let D (K : Set (X n × X n)) (j : ℕ) :=
    if h : K ⊆ O₁ ×ˢ O₂ ∧ IsCompact K then (hJet h j).choose else 0
  refine ⟨fun K j => D K j * (C₁*C₂*P),fun F M hData => ?_⟩
  have hDJet (K : Set (X n × X n)) (hK : K ⊆ O₁ ×ˢ O₂) (hKc : IsCompact K) (j : ℕ)
      (_ : (K,j) ∈ (univ : Set (Set (X n × X n) × ℕ))) :
      0 ≤ D K j ∧ ScalarSeriesJetEstimate (D₁ := O₁) (D₂ := O₂) L₁ L₂ K j (D K j) := by
    have h : K ⊆ O₁ ×ˢ O₂ ∧ IsCompact K := ⟨hK,hKc⟩
    rw [show D K j = (hJet h j).choose from dite_eq_left h]
    exact (hJet h j).choose_spec
  obtain ⟨G,hG,hEstimate⟩ := scalar_crossExtension_of_spectrum_and_jets hD₁ hD₂ hConn₂
    hD₂finite hS₁ hS₂ hSne₂ hO₁ hO₂ hSD₁ hS₂D₂ hO₁D₁ hO₂D₂ hL₁ hL₂
    hC₁ hC₂ hγ₂ hγ₂' hInterp₁ hInterp₂ ⟨ι,w,μ,hCnt,hμ,hEigen,hGram,hSum,hPower⟩
    hDJet F M hData
  exact ⟨G,hG,fun K hK hKc j => hEstimate K hK hKc j (mem_univ _)⟩

end CalderonPaper.ScalarElliptic

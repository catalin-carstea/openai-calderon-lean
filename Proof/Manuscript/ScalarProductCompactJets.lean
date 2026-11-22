module

public import Proof.Manuscript.ScalarCylinderSweep
import Proof.Manuscript.Lemma32
import Proof.Manuscript.ScalarFamilyBounds
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

public section

open CalderonN CalderonPaper.ScalarElliptic Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal BigOperators

namespace CalderonPaper

variable {n : ℕ} [NeZero n]

private theorem observes_itself (L : ScalarElliptic n) {D S : Set (X n)}
    (hSD : S ⊆ D) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    L.Interpolates D S S 1 γ := by
  intro f _ hf
  simp only [one_mul]
  let x := lpNorm f 2 ((volume : Measure (X n)).restrict S)
  let y := lpNorm f 2 ((volume : Measure (X n)).restrict D)
  have hxy : x ≤ y := by
    unfold x y
    rw [← toReal_eLpNorm, ← toReal_eLpNorm]
    exact ENNReal.toReal_mono hf.eLpNorm_ne_top
      (eLpNorm_mono_measure f (Measure.restrict_mono hSD le_rfl))
  change x ≤ x ^ γ * y ^ (1 - γ)
  have hx : 0 ≤ x := lpNorm_nonneg
  by_cases hx0 : x = 0
  · rw [hx0]
    exact mul_nonneg (Real.rpow_nonneg (le_rfl : (0 : ℝ) ≤ 0) _) (Real.rpow_nonneg lpNorm_nonneg _)
  · have hx' := lt_of_le_of_ne hx (Ne.symm hx0)
    calc
      x = x ^ γ * x ^ (1 - γ) := by
        rw [← Real.rpow_add hx', show γ + (1 - γ) = 1 by ring, Real.rpow_one]
      _ ≤ x ^ γ * y ^ (1 - γ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxy (sub_nonneg.mpr hγ.2.le))
          (Real.rpow_nonneg hx _)

private theorem compact_cross_norm {V : Set (X n × X n)} {A B : Set (X n)}
    (hA : IsOpen A) (hB : IsOpen B) (hA' : IsCompact (closure A)) (hB' : IsCompact (closure B))
    (hAB : A ×ˢ B ⊆ V) {f : X n × X n → ℝ} (hf : ContinuousOn f V)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x ∈ A ×ˢ B, |f x| ≤ M) :
    MemLp f 2 (crossMeasure A B) ∧
      lpNorm f 2 (crossMeasure A B) ≤ (crossMeasure A B).real univ ^ ((1 : ℝ) / 2) * M := by
  let μ := crossMeasure A B
  have hAμ : (volume : Measure (X n)) A ≠ (∞ : ℝ≥0∞) :=
    ne_of_lt ((measure_mono subset_closure).trans_lt hA'.measure_lt_top)
  have hBμ : (volume : Measure (X n)) B ≠ (∞ : ℝ≥0∞) :=
    ne_of_lt ((measure_mono subset_closure).trans_lt hB'.measure_lt_top)
  letI : IsFiniteMeasure ((volume : Measure (X n)).restrict A) :=
    isFiniteMeasure_restrict.mpr hAμ
  letI : IsFiniteMeasure ((volume : Measure (X n)).restrict B) :=
    isFiniteMeasure_restrict.mpr hBμ
  letI : IsFiniteMeasure μ := inferInstanceAs
    (IsFiniteMeasure (((volume : Measure (X n)).restrict A).prod
      ((volume : Measure (X n)).restrict B)))
  have hprod : μ = ((volume : Measure (X n)).prod volume).restrict (A ×ˢ B) :=
    Measure.prod_restrict A B
  have hmeas : MeasurableSet (A ×ˢ B) := (hA.prod hB).measurableSet
  have hfμ : AEStronglyMeasurable f μ := by
    rw [hprod]
    exact (hf.mono hAB).aestronglyMeasurable hmeas
  have hpoints : ∀ᵐ x ∂μ, ‖f x‖ ≤ M := by
    rw [hprod]
    exact (ae_restrict_iff' hmeas).mpr
      (.of_forall fun x hx => by simpa only [Real.norm_eq_abs] using hbound x hx)
  refine ⟨MemLp.of_bound hfμ M hpoints, ?_⟩
  change lpNorm f 2 μ ≤ _
  calc
    _ ≤ lpNorm (fun _ : X n × X n => M) 2 μ := by
      rw [← toReal_eLpNorm, ← toReal_eLpNorm]
      exact ENNReal.toReal_mono (memLp_const M).eLpNorm_ne_top (eLpNorm_mono_ae_real hfμ hpoints)
    _ = _ := by
      rw [lpNorm_const' (by norm_num) (by norm_num), Real.norm_eq_abs, abs_of_nonneg hM]
      norm_num [one_div, mul_comm, μ]

private theorem exists_reference_product_rectangular_jet_bound
    {D₁ D₂ O₁ O₂ : Set (X n)} {P₀ : Set (X n × X n)}
    {L₁₀ L₂₀ : ScalarElliptic n} (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂)
    (h₁₀ : L₁₀.SmoothOn D₁) (h₂₀ : L₂₀.SmoothOn D₂)
    {A₁ A₂ : Set (X n)} (hA₁ : IsOpen A₁) (hA₂ : IsOpen A₂)
    (hAc₁ : IsConnected A₁) (hAc₂ : IsConnected A₂)
    (hAb₁ : IsCompact (closure A₁)) (hAb₂ : IsCompact (closure A₂))
    (hAD₁ : closure A₁ ⊆ D₁) (hAD₂ : closure A₂ ⊆ D₂)
    (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂) (hOn₁ : O₁.Nonempty) (hOn₂ : O₂.Nonempty)
    (hOA₁ : closure O₁ ⊆ A₁) (hOA₂ : closure O₂ ⊆ A₂)
    (hRoom : closure A₁ ×ˢ closure A₂ ⊆ P₀)
    {J : Set (X n × X n)} (hJ : IsCompact J) (hJO : J ⊆ O₁ ×ˢ O₂) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ path : ScalarSweepPath D₁ D₂ L₁₀ L₂₀, ∀ᶠ t in 𝓝 (0 : ℝ), ∀ F,
        path.solves t P₀ F → ∀ M : ℝ, 0 ≤ M →
        (∀ x ∈ closure A₁ ×ˢ closure A₂, |F x| ≤ M) →
        ∀ j ≤ m, ∀ x ∈ J, ‖iteratedFDeriv ℝ j F x‖ ≤ C * M := by
  have hOA₁' : O₁ ⊆ A₁ := subset_closure.trans hOA₁
  have hOA₂' : O₂ ⊆ A₂ := subset_closure.trans hOA₂
  have hOb₁ : IsCompact (closure O₁) :=
    hAb₁.of_isClosed_subset isClosed_closure (hOA₁.trans subset_closure)
  have hOb₂ : IsCompact (closure O₂) :=
    hAb₂.of_isClosed_subset isClosed_closure (hOA₂.trans subset_closure)
  have hγ : (3 / 4 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  obtain ⟨N, hN⟩ := (lemma32 hA₁ hA₂ hAc₁ hAc₂ hAb₁ hAb₂ hO₁ hO₂ hOn₁ hOn₂
    hO₁ hO₂ hOA₁ hOA₂ hOA₁ hOA₂ (hC₁ := (by norm_num : (0 : ℝ) < 1))
    (hC₂ := (by norm_num : (0 : ℝ) < 1)) hγ hγ (by norm_num)).2
      (1 / 2) (by norm_num) J hJO hJ m
  obtain ⟨χ₁, hχ₁, hχD₁, hχ01₁, hχA₁⟩ := exists_scalar_operator_cutoff hD₁ hAb₁ hAD₁
  obtain ⟨χ₂, hχ₂, hχD₂, hχ01₂, hχA₂⟩ := exists_scalar_operator_cutoff hD₂ hAb₂ hAD₂
  have hS₁ := smoothFamilyOn_cutoffOperator hD₁ hχ₁ hχD₁ hχ01₁ (smoothFamilyOn_const h₁₀)
  have hS₂ := smoothFamilyOn_cutoffOperator hD₂ hχ₂ hχD₂ hχ01₂ (smoothFamilyOn_const h₂₀)
  obtain ⟨a₁, B₁, ha₁, hB₁, hBudget₁⟩ := exists_reference_scalar_coefficient_budget hAb₁ (hS₁.1 0) N
  obtain ⟨a₂, B₂, ha₂, hB₂, hBudget₂⟩ := exists_reference_scalar_coefficient_budget hAb₂ (hS₂.1 0) N
  let a := min a₁ a₂
  let B := max B₁ B₂
  obtain ⟨C, hC, hBound⟩ := hN a B (lt_min ha₁ ha₂) (hB₁.trans_le (le_max_left _ _))
  let P₁ := (crossMeasure A₁ O₂).real univ ^ ((1 : ℝ) / 2)
  let P₂ := (crossMeasure O₁ A₂).real univ ^ ((1 : ℝ) / 2)
  have hP : 0 ≤ P₁ + P₂ := by dsimp [P₁, P₂]; positivity
  refine ⟨C * (P₁ + P₂), mul_nonneg hC hP, fun path => ?_⟩
  let L (t : ℝ) := cutoffOperator χ₁ (path.left t)
  let R (t : ℝ) := cutoffOperator χ₂ (path.right t)
  have hSmoothL := smoothFamilyOn_cutoffOperator hD₁ hχ₁ hχD₁ hχ01₁ path.smoothLeft
  have hSmoothR := smoothFamilyOn_cutoffOperator hD₂ hχ₂ hχD₂ hχ01₂ path.smoothRight
  have hL₀ : L 0 = cutoffOperator χ₁ L₁₀ := congrArg (cutoffOperator χ₁) path.referenceLeft
  have hR₀ : R 0 = cutoffOperator χ₂ L₂₀ := congrArg (cutoffOperator χ₂) path.referenceRight
  filter_upwards [hBudget₁ L hSmoothL hL₀, hBudget₂ R hSmoothR hR₀] with t hL hR F hF M hM hFM
  have hLC : (L t).CoefficientBound A₁ a B N := by
    refine ⟨fun x hx v => ?_, fun x hx i hi => ?_⟩
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans
        (hL.1 x (subset_closure hx) v)
    · obtain ⟨hA, hB', hC'⟩ := hL.2 x (subset_closure hx) i hi
      exact ⟨fun j k => (hA j k).trans (le_max_left _ _),
        fun j => (hB' j).trans (le_max_left _ _), hC'.trans (le_max_left _ _)⟩
  have hRC : (R t).CoefficientBound A₂ a B N := by
    refine ⟨fun x hx v => ?_, fun x hx i hi => ?_⟩
    · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans
        (hR.1 x (subset_closure hx) v)
    · obtain ⟨hA, hB', hC'⟩ := hR.2 x (subset_closure hx) i hi
      exact ⟨fun j k => (hA j k).trans (le_max_right _ _),
        fun j => (hB' j).trans (le_max_right _ _), hC'.trans (le_max_right _ _)⟩
  have hAb : A₁ ×ˢ A₂ ⊆ closure A₁ ×ˢ closure A₂ :=
    Set.prod_mono subset_closure subset_closure
  have hF' : ProductSolvesOn (L t) (R t) (A₁ ×ˢ A₂) F := by
    refine ⟨hF.2.1.mono (hAb.trans hRoom), fun z hz => ?_, fun z hz => ?_⟩
    · exact (cutoffOperator_apply_of_one (hχA₁ _ (subset_closure hz.1)).eq_of_nhds _).trans
        (hF.2.2.1 z (hRoom (hAb hz)))
    · exact (cutoffOperator_apply_of_one (hχA₂ _ (subset_closure hz.2)).eq_of_nhds _).trans
        (hF.2.2.2 z (hRoom (hAb hz)))
  have hLeft : A₁ ×ˢ O₂ ⊆ A₁ ×ˢ A₂ := Set.prod_mono Subset.rfl hOA₂'
  have hRight : O₁ ×ˢ A₂ ⊆ A₁ ×ˢ A₂ := Set.prod_mono hOA₁' Subset.rfl
  obtain ⟨hMp₁, hMpB₁⟩ := compact_cross_norm hA₁ hO₂ hAb₁ hOb₂ ((hLeft.trans hAb).trans hRoom)
    hF.2.1.continuousOn hM (fun x hx => hFM x (hAb (hLeft hx)))
  obtain ⟨hMp₂, hMpB₂⟩ := compact_cross_norm hO₁ hA₂ hOb₁ hAb₂ ((hRight.trans hAb).trans hRoom)
    hF.2.1.continuousOn hM (fun x hx => hFM x (hAb (hRight hx)))
  have hCross : CrossData (L t) (R t) A₁ A₂ O₁ O₂ F ((P₁ + P₂) * M) :=
    ⟨hF'.mono hLeft, hF'.mono hRight, hMp₁, hMp₂,
      (add_le_add hMpB₁ hMpB₂).trans_eq (by ring)⟩
  obtain ⟨G, hExt, hJet⟩ := hBound (3 / 4) (3 / 4) hγ hγ (by norm_num)
    (L t) (R t) ((hSmoothL.1 t).restrict (subset_univ _)) ((hSmoothR.1 t).restrict (subset_univ _))
    hLC hRC (observes_itself _ hOA₁' hγ) (observes_itself _ hOA₂' hγ)
    F ((P₁ + P₂) * M) hCross
  have hEq : EqOn G F (O₁ ×ˢ O₂) := by simpa only [inter_self] using hExt.2.1
  intro j hj x hx
  rw [← (((hEq.eventuallyEq_of_mem ((hO₁.prod hO₂).mem_nhds (hJO hx))).iteratedFDeriv ℝ j).eq_of_nhds)]
  simpa only [mul_assoc] using hJet j hj x hx

set_option maxHeartbeats 3000000 in
/-- Apply the cross estimate on interior rectangles with the observation
set as the output. A finite cover produces one compact value budget. -/
theorem exists_reference_scalar_product_compact_jet_bound
    {D₁ D₂ : Set (X n)} {V : Set (X n × X n)} (hV : IsOpen V)
    (hVD : V ⊆ D₁ ×ˢ D₂) (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂)
    {L₁₀ L₂₀ : ScalarElliptic n} (h₁₀ : L₁₀.SmoothOn D₁) (h₂₀ : L₂₀.SmoothOn D₂)
    {K : Set (X n × X n)} (hKV : K ⊆ V) (hK : IsCompact K) (m : ℕ) :
    ∃ (K' : Set (X n × X n)) (C : ℝ), IsCompact K' ∧ K' ⊆ V ∧ 0 ≤ C ∧
      ∀ path : ScalarSweepPath D₁ D₂ L₁₀ L₂₀, ∀ᶠ t in 𝓝 (0 : ℝ), ∀ F,
        path.solves t V F → ∀ M : ℝ, 0 ≤ M →
        (∀ x ∈ K', |F x| ≤ M) →
        ∀ j ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ j F x‖ ≤ C * M := by
  classical
  have hrect (x : K) :
      ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧ (closedBall x.val.1 r ×ˢ closedBall x.val.2 r ⊆ V) ∧
        ∀ path : ScalarSweepPath D₁ D₂ L₁₀ L₂₀, ∀ᶠ t in 𝓝 (0 : ℝ), ∀ F,
          path.solves t V F → ∀ M : ℝ, 0 ≤ M →
          (∀ y ∈ closedBall x.val.1 r ×ˢ closedBall x.val.2 r, |F y| ≤ M) →
          ∀ j ≤ m, ∀ y ∈ closedBall x.val.1 (r / 4) ×ˢ closedBall x.val.2 (r / 4),
            ‖iteratedFDeriv ℝ j F y‖ ≤ C * M := by
    obtain ⟨s, hs, hsV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (hKV x.property))
    let r := s / 2
    have hr : 0 < r := half_pos hs
    have hVroom : closedBall x.val.1 r ×ˢ closedBall x.val.2 r ⊆ V := by
      intro q hq
      apply hsV
      rw [mem_ball, Prod.dist_eq]
      exact max_lt (hq.1.trans_lt (half_lt_self hs)) (hq.2.trans_lt (half_lt_self hs))
    have hA₁ : closure (ball x.val.1 r) = closedBall x.val.1 r := closure_ball _ hr.ne'
    have hA₂ : closure (ball x.val.2 r) = closedBall x.val.2 r := closure_ball _ hr.ne'
    have hOA₁ : closure (ball x.val.1 (r / 2)) ⊆ ball x.val.1 r := by
      rw [closure_ball _ (half_pos hr).ne']
      exact closedBall_subset_ball (half_lt_self hr)
    have hOA₂ : closure (ball x.val.2 (r / 2)) ⊆ ball x.val.2 r := by
      rw [closure_ball _ (half_pos hr).ne']
      exact closedBall_subset_ball (half_lt_self hr)
    have hAD₁ : closure (ball x.val.1 r) ⊆ D₁ := by
      rw [hA₁]
      intro y hy
      have hyp : (y, x.val.2) ∈ closedBall x.val.1 r ×ˢ closedBall x.val.2 r :=
        Set.mem_prod.mpr ⟨hy, mem_closedBall_self hr.le⟩
      exact (Set.mem_prod.mp (hVD (hVroom hyp))).1
    have hAD₂ : closure (ball x.val.2 r) ⊆ D₂ := by
      rw [hA₂]
      intro y hy
      have hyp : (x.val.1, y) ∈ closedBall x.val.1 r ×ˢ closedBall x.val.2 r :=
        Set.mem_prod.mpr ⟨mem_closedBall_self hr.le, hy⟩
      exact (Set.mem_prod.mp (hVD (hVroom hyp))).2
    have hSmall : closedBall x.val.1 (r / 4) ×ˢ closedBall x.val.2 (r / 4) ⊆
        ball x.val.1 (r / 2) ×ˢ ball x.val.2 (r / 2) :=
      Set.prod_mono (closedBall_subset_ball (by linarith))
        (closedBall_subset_ball (by linarith))
    obtain ⟨C, hC, h⟩ := exists_reference_product_rectangular_jet_bound hD₁ hD₂ h₁₀ h₂₀
      (P₀ := V) (A₁ := ball x.val.1 r) (A₂ := ball x.val.2 r)
      (O₁ := ball x.val.1 (r / 2)) (O₂ := ball x.val.2 (r / 2))
      isOpen_ball isOpen_ball
      ((convex_ball _ _).isConnected ⟨_, mem_ball_self hr⟩)
      ((convex_ball _ _).isConnected ⟨_, mem_ball_self hr⟩)
      (hA₁ ▸ isCompact_closedBall _ _) (hA₂ ▸ isCompact_closedBall _ _)
      hAD₁ hAD₂ isOpen_ball isOpen_ball ⟨_, mem_ball_self (half_pos hr)⟩
      ⟨_, mem_ball_self (half_pos hr)⟩ hOA₁ hOA₂ (by rwa [hA₁, hA₂])
      ((isCompact_closedBall _ (r / 4)).prod (isCompact_closedBall _ (r / 4))) hSmall m
    refine ⟨r, C, hr, hC, hVroom, fun path => ?_⟩
    filter_upwards [h path] with t ht F hF M hM hFM
    exact ht F hF M hM (by rwa [hA₁, hA₂])
  choose r C hr hC hRoom hRect using hrect
  let U (x : K) := ball x.val.1 (r x / 4) ×ˢ ball x.val.2 (r x / 4)
  have hU (x : K) : IsOpen (U x) := isOpen_ball.prod isOpen_ball
  have hCover : K ⊆ ⋃ x : K, U x := fun x hx => mem_iUnion.mpr
    ⟨⟨x, hx⟩, ⟨mem_ball_self (by linarith [hr ⟨x, hx⟩]),
      mem_ball_self (by linarith [hr ⟨x, hx⟩])⟩⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover U hU hCover
  let D (x : K) := closedBall x.val.1 (r x) ×ˢ closedBall x.val.2 (r x)
  let K' := ⋃ x ∈ I, D x
  let J := ∑ x ∈ I, C x
  have hK' : IsCompact K' :=
    I.finite_toSet.isCompact_biUnion fun x _ => (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hK'V : K' ⊆ V := iUnion₂_subset fun x _ => hRoom x
  refine ⟨K', J, hK', hK'V, Finset.sum_nonneg (fun x _ => hC x), fun path => ?_⟩
  have hEvt := (eventually_all_finset I).mpr (fun x _ => hRect x path)
  filter_upwards [hEvt] with t h F hF M hM hFM j hj y hy
  obtain ⟨x, hx⟩ := mem_iUnion.mp (hI hy)
  obtain ⟨hxI, hyx⟩ := mem_iUnion.mp hx
  have hSmall : y ∈ closedBall x.val.1 (r x / 4) ×ˢ closedBall x.val.2 (r x / 4) :=
    Set.prod_mono ball_subset_closedBall ball_subset_closedBall hyx
  have hD (z : X n × X n) (hz : z ∈ D x) : |F z| ≤ M :=
    hFM z (mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hxI, hz⟩⟩)
  exact (h x hxI F hF M hM hD j hj y hSmall).trans
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun x _ => hC x) hxI) hM)

end CalderonPaper

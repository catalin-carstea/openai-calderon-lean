module

public import Proof.CalderonPatch.GreenParameterJetOffPole
public import Proof.CalderonPatch.SecondJetIntegral

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X InteriorMetricChart IsDirichletGreenKernel parameterSecondOrder)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)

/-- Compactly supported source tests separated from the pole can be
paired with the differentiated Green kernel by differentiation under
the integral sign. -/
theorem greenParameterSecondOrder_pairing
    {μ : Measure M} {L : (M → ℝ) → M → ℝ}
    {G : M × M → ℝ} (hG : IsDirichletGreenKernel J μ L G)
    (A C : InteriorMetricChart J μ L)
    {U T : Set (X n)} (hU : IsOpen U) (hUA : U ⊆ A.chart.target)
    (hT : IsCompact T) (hTU : T ⊆ U)
    {z : X n} (hz : z ∈ C.chart.target)
    (hApart : C.chart.symm z ∉ A.chart.symm '' T)
    (w : X n → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwT : ∀ x ∈ U \ T, w x = 0)
    (a : I n → I n → ℝ) (b : I n → ℝ) (c : ℝ) :
    parameterSecondOrder a b c (fun s => ∫ x in U, w x * G (A.chart.symm x,C.chart.symm s)) z =
      ∫ x in U, w x *
        parameterSecondOrder a b c (fun s => G (A.chart.symm x,C.chart.symm s)) z := by
  obtain ⟨U',V,hU',hV,hT',hU'U,hz',hVC,hDis⟩ :=
    exists_green_chart_rectangle A C hU hUA hT hTU hz hApart
  let F (x s : X n) := w x * G (A.chart.symm x,C.chart.symm s)
  have hKernel : ContDiffOn ℝ ∞ (Function.uncurry (fun x s => G (A.chart.symm x,C.chart.symm s))) (U' ×ˢ V) :=
    contDiffOn_jointGreen_of_disjoint_charts hG A C (hU'U.trans hUA) hVC hDis
  have hF : ContDiffOn ℝ ∞ (Function.uncurry F) (U' ×ˢ V) :=
    (hw.comp contDiffOn_fst (fun _ hx => hU'U hx.1)).mul hKernel
  let ν := (volume : Measure (X n)).restrict T
  have : IsFiniteMeasure ν := ⟨by simpa only [ν,Measure.restrict_apply_univ] using hT.measure_lt_top⟩
  have hν : ν Tᶜ = 0 := by simp [ν,Measure.restrict_apply hT.measurableSet.compl,Set.compl_inter_self]
  have hD := CalderonN.integral_parameterSecondOrder hT hT' hU' hV hν
    (hF.of_le (by simp : (2 : WithTop ℕ∞) ≤ ∞)) a b c hz'
  have hInt : (fun s => ∫ x in U, w x * G (A.chart.symm x,C.chart.symm s)) =
      fun s => ∫ x, F x s ∂ν := by
    funext s
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hTU
      (fun x hx => mul_eq_zero_of_left (hwT x hx) _)
  rw [hInt,hD]
  change (∫ x in T, parameterSecondOrder a b c (F x) z) = _
  calc
    _ = ∫ x in T, w x * parameterSecondOrder a b c
        (fun s => G (A.chart.symm x,C.chart.symm s)) z := by
      apply setIntegral_congr_fun hT.measurableSet
      intro x hx
      have hS : ContDiffOn ℝ ∞ (fun s => G (A.chart.symm x,C.chart.symm s)) V :=
        hKernel.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => ⟨hT' hx,hy⟩)
      exact parameterSecondOrder_const_mul a b c (w x) hV hS hz'
    _ = _ := (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hTU
      (fun x hx => mul_eq_zero_of_left (hwT x hx) _)).symm

end CalderonPatch

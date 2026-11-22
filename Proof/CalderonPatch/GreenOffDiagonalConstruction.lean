module

public import Proof.CalderonPatch.GreenLocalSource

import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Tactic

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff ENNReal Manifold RealInnerProductSpace Topology

namespace CalderonPatch

open CalderonN (X)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "J" => 𝓡∂ (m+1)
local notation "R" => 𝓘(ℝ,ℝ)
local notation "Y" => X (m+1)

variable {D : DirichletData m M} (h : NativeInverseRegularity D)

local notation "L²" => Lp ℝ 2 D.volume

namespace GreenEvaluationChart

variable (C : GreenEvaluationChart D)

/-- The exact weak inverse of the interior evaluation source is a
classical zero-trace function on the exterior of the chart closure. -/
def poleCandidate (p : M) : M → ℝ :=
  (exists_localInverse h (f := C.evaluationSource (C.chart p))
    isClosed_closure.isOpen_compl ((C.evaluationSource_ae_zero_off_chart _).filter_mono
      (ae_mono (Measure.restrict_mono_set _ (compl_subset_compl.mpr subset_closure))))).choose

theorem poleCandidate_spec (p : M) :
    ContMDiffOn J R ∞ (C.poleCandidate h p) (closure C.chart.source)ᶜ ∧
    EqOn (C.poleCandidate h p) 0 ((closure C.chart.source)ᶜ ∩ (J).boundary M) ∧
    EqOn (nativeLaplace D.metric (C.poleCandidate h p)) 0
      ((closure C.chart.source)ᶜ ∩ (J).interior M) ∧
    (D.weakInverseL2 (C.evaluationSource (C.chart p)) : M → ℝ) =ᵐ[
      D.volume.restrict (closure C.chart.source)ᶜ] C.poleCandidate h p :=
  (exists_localInverse h (f := C.evaluationSource (C.chart p))
    isClosed_closure.isOpen_compl ((C.evaluationSource_ae_zero_off_chart _).filter_mono
      (ae_mono (Measure.restrict_mono_set _ (compl_subset_compl.mpr subset_closure))))).choose_spec

/-- Two choices of chart for a pole give exactly the same classical
column where both weak inverses are harmonic. -/
theorem poleCandidate_eqOn (E : GreenEvaluationChart D) {p : M}
    (hpC : p ∈ C.chart.source) (hpE : p ∈ E.chart.source) :
    EqOn (C.poleCandidate h p) (E.poleCandidate h p)
      ((closure C.chart.source)ᶜ ∩ (closure E.chart.source)ᶜ) := by
  let U := (closure C.chart.source)ᶜ ∩ (closure E.chart.source)ᶜ
  have hU : IsOpen U := isClosed_closure.isOpen_compl.inter isClosed_closure.isOpen_compl
  let a := D.weakInverseL2 (C.evaluationSource (C.chart p))
  let b := D.weakInverseL2 (E.evaluationSource (E.chart p))
  have hAE : (a : M → ℝ) =ᵐ[D.volume.restrict U] b := by
    apply lp_ae_eq_of_supported_pairings hU.measurableSet
    intro f hf
    have hC : C.chart.source ⊆ Uᶜ := fun x hx hbad => hbad.1 (subset_closure hx)
    have hE : E.chart.source ⊆ Uᶜ := fun x hx hbad => hbad.2 (subset_closure hx)
    exact evaluationSources_agree h C E hpC hpE
      (hf.filter_mono (ae_mono (Measure.restrict_mono_set _ hC)))
      (hf.filter_mono (ae_mono (Measure.restrict_mono_set _ hE)))
  have ha := (C.poleCandidate_spec h p).2.2.2.filter_mono
    (ae_mono (Measure.restrict_mono_set _ (show U ⊆ (closure C.chart.source)ᶜ from inter_subset_left)))
  have hb := (E.poleCandidate_spec h p).2.2.2.filter_mono
    (ae_mono (Measure.restrict_mono_set _ (show U ⊆ (closure E.chart.source)ᶜ from inter_subset_right)))
  exact D.eqOn_open_of_ae_eq hU ((C.poleCandidate_spec h p).1.continuousOn.mono inter_subset_left)
    ((E.poleCandidate_spec h p).1.continuousOn.mono inter_subset_right) (ha.symm.trans (hAE.trans hb))

end GreenEvaluationChart

omit [CompactSpace M] [PreconnectedSpace M] in
private theorem exists_poleChart {p q : M} (hq : q ∈ (J).interior M) (hpq : p ≠ q) :
    ∃ C : GreenEvaluationChart D, q ∈ C.chart.source ∧ p ∉ closure C.chart.source := by
  obtain ⟨C,hCq,hC⟩ := GreenEvaluationChart.exists_chart_at D hq
    (isClosed_singleton (x := p)).isOpen_compl (show q ∈ ({p} : Set M)ᶜ from
      notMem_singleton_iff.mpr hpq.symm)
  exact ⟨C,hCq,fun hp => (hC hp) (mem_singleton p)⟩

/-- The punctured native kernel from local harmonic evaluation
sources. The pole value itself is set to zero. -/
def nativeGreenCandidate (z : M × M) : ℝ := by
  classical
  exact if hz : z.2 ∈ (J).interior M ∧ z.1 ≠ z.2 then
    (exists_poleChart (D := D) hz.1 hz.2).choose.poleCandidate h z.2 z.1
  else 0

theorem nativeGreenCandidate_diagonal (p : M) : nativeGreenCandidate h (p,p) = 0 := by
  unfold nativeGreenCandidate
  rw [dite_eq_right (by simp)]

/-- Every admissible pole chart computes the same column pointwise. -/
theorem nativeGreenCandidate_eqOn (C : GreenEvaluationChart D) {q : M} (hq : q ∈ C.chart.source) :
    EqOn (fun x => nativeGreenCandidate h (x,q)) (C.poleCandidate h q)
      (closure C.chart.source)ᶜ := by
  intro x hx
  have hn : x ≠ q := fun he => hx (he.symm ▸ subset_closure hq)
  have H : q ∈ (J).interior M ∧ x ≠ q := ⟨C.source_interior hq,hn⟩
  change nativeGreenCandidate h (x,q) = C.poleCandidate h q x
  unfold nativeGreenCandidate
  dsimp only
  rw [dite_eq_left H]
  let E := (exists_poleChart (D := D) H.1 H.2).choose
  have he := (exists_poleChart (D := D) H.1 H.2).choose_spec
  exact E.poleCandidate_eqOn h C he.1 hq ⟨he.2,hx⟩

theorem nativeGreenCandidate_continuous_off_pole {q : M} (hq : q ∈ (J).interior M) :
    ContinuousOn (fun x => nativeGreenCandidate h (x,q)) ({q} : Set M)ᶜ := by
  intro p hp
  obtain ⟨C,hCq,hpC⟩ := exists_poleChart (D := D) hq
    (show p ≠ q from notMem_singleton_iff.mp hp)
  have hW := (isClosed_closure (s := C.chart.source)).isOpen_compl.mem_nhds hpC
  have he := eventually_of_mem hW (nativeGreenCandidate_eqOn h C hCq)
  exact ((C.poleCandidate_spec h q).1.continuousOn.continuousAt hW
    |>.congr_of_eventuallyEq he).continuousWithinAt

theorem nativeGreenCandidate_boundary_zero {x q : M}
    (hx : x ∈ (J).boundary M) (hq : q ∈ (J).interior M) :
    nativeGreenCandidate h (x,q) = 0 := by
  have hxNot : x ∉ (J).interior M := by
    change x ∈ ((J).interior M)ᶜ
    rwa [(J).compl_interior]
  have hn : x ≠ q := fun he => hxNot (he.symm ▸ hq)
  obtain ⟨C,hCq,hxC⟩ := exists_poleChart (D := D) hq hn
  exact (nativeGreenCandidate_eqOn h C hCq hxC).trans
    ((C.poleCandidate_spec h q).2.1 ⟨hxC,hx⟩)

/-- On separated chart sources, the kernel is an exact pairing
of two smooth families of L² evaluation sources. -/
theorem nativeGreenCandidate_pair_chart (C E : GreenEvaluationChart D)
    (hsep : Disjoint (closure C.chart.source) (closure E.chart.source))
    {x q : M} (hx : x ∈ C.chart.source) (hq : q ∈ E.chart.source) :
    nativeGreenCandidate h (x,q) =
      ⟪C.evaluationSource (C.chart x),D.weakInverseL2 (E.evaluationSource (E.chart q))⟫ := by
  have hSub : C.chart.source ⊆ (closure E.chart.source)ᶜ := fun p hp he =>
    Set.disjoint_left.mp hsep (subset_closure hp) he
  have hP := E.poleCandidate_spec h q
  have hv := C.evaluationSource_pair (hP.1.mono hSub)
    (hP.2.2.1.mono (show C.chart.source ⊆ (closure E.chart.source)ᶜ ∩ (J).interior M from
      fun p hp => ⟨hSub hp,C.source_interior hp⟩))
    (hP.2.2.2.filter_mono (ae_mono (Measure.restrict_mono_set _ hSub))) hx
  exact (nativeGreenCandidate_eqOn h E hq (hSub hx)).trans hv.symm

omit [PreconnectedSpace M] in
theorem exists_disjoint_poleCharts {x q : M} (hx : x ∈ (J).interior M)
    (hq : q ∈ (J).interior M) (hne : x ≠ q) :
    ∃ C E : GreenEvaluationChart D, x ∈ C.chart.source ∧ q ∈ E.chart.source ∧
      Disjoint (closure C.chart.source) (closure E.chart.source) := by
  obtain ⟨U,hxU,hU,V,hqV,hV,hDisj⟩ := exists_open_nhds_disjoint_closure hne
  obtain ⟨C,hCx,hCU⟩ := GreenEvaluationChart.exists_chart_at D hx hU hxU
  obtain ⟨E,hEq,hEV⟩ := GreenEvaluationChart.exists_chart_at D hq hV hqV
  exact ⟨C,E,hCx,hEq,hDisj.mono (hCU.trans subset_closure) (hEV.trans subset_closure)⟩

theorem nativeGreenCandidate_symmetric {x q : M} (hx : x ∈ (J).interior M)
    (hq : q ∈ (J).interior M) (hne : x ≠ q) :
    nativeGreenCandidate h (x,q) = nativeGreenCandidate h (q,x) := by
  obtain ⟨C,E,hCx,hEq,hDisj⟩ := exists_disjoint_poleCharts (D := D) hx hq hne
  rw [nativeGreenCandidate_pair_chart h C E hDisj hCx hEq,
    nativeGreenCandidate_pair_chart h E C hDisj.symm hEq hCx,
    ← D.weakInverseL2_symmetric, real_inner_comm]

/-- The kernel on the exterior of the pole chart gives the true inverse
value for each smooth source supported there. -/
theorem nativeGreenCandidate_integral_of_off_pole_source {q : M} (hq : q ∈ (J).interior M)
    (φ : smoothSourceSubmodule (m := m) (M := M)) (hφq : q ∉ tsupport (φ : M → ℝ)) :
    Integrable (fun p => nativeGreenCandidate h (p,q) * φ p) D.volume ∧
      (∫ p, nativeGreenCandidate h (p,q) * φ p ∂D.volume) = D.smoothInverse h φ q := by
  obtain ⟨C,hCq,hCU⟩ := GreenEvaluationChart.exists_chart_at D hq
    isClosed_closure.isOpen_compl hφq
  let a := D.weakInverseL2 (C.evaluationSource (C.chart q))
  let f := D.smoothSourceToLp 2 φ
  let u := D.smoothInverse h φ
  have hf : (f : M → ℝ) =ᵐ[D.volume.restrict C.chart.source] (φ : M → ℝ) :=
    ae_restrict_of_ae (D.smoothSourceToLp_ae 2 φ)
  have hL : ⟪a,f⟫ = u q := by
    rw [show a = D.weakInverseL2 (C.evaluationSource (C.chart q)) from rfl,D.weakInverseL2_symmetric]
    have hA := D.smoothInverse_spec h φ
    apply C.evaluationSource_pair hA.1.contMDiffOn _ (ae_restrict_of_ae hA.2.2.2) hCq
    intro p hp
    have hφ₀ := image_eq_zero_of_notMem_tsupport (hCU (subset_closure hp))
    have hU := hA.2.2.1 (C.source_interior hp)
    change -nativeLaplace D.metric u p = φ p at hU
    rw [show φ p = 0 from hφ₀,neg_eq_zero] at hU
    exact hU
  let W := (closure C.chart.source)ᶜ
  have hInt : Integrable (fun p => a p * f p) D.volume := (Lp.memLp a).integrable_mul (Lp.memLp f)
  have he : (fun p => a p * f p) =ᵐ[D.volume] (fun p => nativeGreenCandidate h (p,q) * φ p) := by
    have hR := (ae_restrict_iff' (isClosed_closure (s := C.chart.source)).measurableSet.compl).mp
      (C.poleCandidate_spec h q).2.2.2
    filter_upwards [D.smoothSourceToLp_ae 2 φ,hR] with p hfP hp
    by_cases hpW : p ∈ W
    · rw [hfP, hp hpW]
      exact congrArg (fun z => z * φ p) (nativeGreenCandidate_eqOn h C hCq hpW).symm
    · have hPC : p ∈ closure C.chart.source := by
        simpa only [W, mem_compl_iff, not_not] using hpW
      have hφ₀ : φ p = 0 := image_eq_zero_of_notMem_tsupport (hCU hPC)
      rw [hfP,hφ₀,mul_zero,mul_zero]
  refine ⟨hInt.congr he,(integral_congr_ae he).symm.trans ?_⟩
  change _ = u q
  rw [← hL,L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall (fun p => (Real.inner_apply _ _).symm)

end CalderonPatch

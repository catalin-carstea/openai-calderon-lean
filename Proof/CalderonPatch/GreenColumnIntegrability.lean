module

public import Proof.CalderonPatch.GreenOffDiagonalConstruction
public import Proof.CalderonPatch.GreenInversePositivity
public import Proof.CalderonPatch.GreenPoleNeighborhood

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Tactic

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace CalderonPatch

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "J" => 𝓡∂ (m+1)
local notation "R" => 𝓘(ℝ,ℝ)
local notation "Source" => smoothSourceSubmodule (m := m) (M := M)

variable {D : DirichletData m M} (h : NativeInverseRegularity D)

/-- A kernel column is measurable through its prescribed value at
the excluded point. -/
theorem measurable_nativeGreenCandidate {q : M} (hq : q ∈ (J).interior M) :
    Measurable (fun p => nativeGreenCandidate h (p,q)) := by
  classical
  let G (p : M) := nativeGreenCandidate h (p,q)
  have hG : ContinuousOn G ({q} : Set M)ᶜ := nativeGreenCandidate_continuous_off_pole h hq
  have he : ({q} : Set M)ᶜ.piecewise G (fun _ => (0 : ℝ)) = G := by
    funext x
    by_cases hx : x = q
    · subst x
      rw [piecewise_eq_of_notMem _ _ _ (not_not_intro (mem_singleton q))]
      exact (nativeGreenCandidate_diagonal h q).symm
    · exact piecewise_eq_of_mem _ _ _ (notMem_singleton_iff.mpr hx)
  change Measurable G
  rw [← he]
  exact hG.measurable_piecewise continuousOn_const (measurableSet_singleton q).compl

/-- Comparison for the actual inverse implies nonnegativity of its
off-pole kernel, by smooth tests supported where a column is negative. -/
theorem nativeGreenCandidate_nonneg {q : M} (hq : q ∈ (J).interior M) (p : M) :
    0 ≤ nativeGreenCandidate h (p,q) := by
  by_cases hpq : p = q
  · subst p
    rw [nativeGreenCandidate_diagonal]
  by_cases hp : p ∈ (J).interior M
  · by_contra! hneg
    let G (x : M) := nativeGreenCandidate h (x,q)
    let U := {x | x ∈ ({q} : Set M)ᶜ ∧ G x < 0}
    have hG : ContinuousOn G ({q} : Set M)ᶜ := nativeGreenCandidate_continuous_off_pole h hq
    have hU : IsOpen U :=
      hG.isOpen_inter_preimage (isClosed_singleton (x := q)).isOpen_compl isOpen_Iio
    have hpU : p ∈ U := ⟨notMem_singleton_iff.mpr hpq,hneg⟩
    obtain ⟨v,hv,_,hvS,hvp⟩ := exists_compactly_supported_interior_test hp hU hpU
    let φ : Source := ⟨fun x => (v x)^2,(contDiff_id.pow 2).contMDiff.comp hv⟩
    have hφ : ∀ x, 0 ≤ φ x := fun x => sq_nonneg _
    have hS : tsupport (φ : M → ℝ) ⊆ U := by
      change tsupport (fun x => (v x)^2) ⊆ U
      simp only [pow_two]
      exact tsupport_mul_subset_left.trans (hvS.trans inter_subset_left)
    have hφq : q ∉ tsupport (φ : M → ℝ) := fun hq' => (hS hq').1 (mem_singleton q)
    have hPair := nativeGreenCandidate_integral_of_off_pole_source h hq φ hφq
    have hPos := D.smoothInverse_nonneg h φ hφ q
    have hOpp : 0 < ∫ x, -(G x * φ x) ∂D.volume := by
      let F (x : M) := -(G x * φ x)
      have hF : Integrable F D.volume := hPair.1.neg
      have hf (x : M) : 0 ≤ F x := by
        by_cases hx : x ∈ tsupport (φ : M → ℝ)
        · exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (hS hx).2.le (hφ x))
        · simp [F,image_eq_zero_of_notMem_tsupport hx]
      apply (integral_pos_iff_support_of_nonneg hf hF).mpr
      let W := U ∩ {x | 0 < φ x}
      have hW : IsOpen W :=
        hU.inter ((show ContMDiff J R ∞ (φ : M → ℝ) from φ.property).continuous.isOpen_preimage _ isOpen_Ioi)
      have hpW : p ∈ W := ⟨hpU,by change 0 < (v p)^2; rw [hvp]; norm_num⟩
      have hWS : W ⊆ Function.support F := fun x hx =>
        (neg_pos.mpr (mul_neg_of_neg_of_pos hx.1.2 hx.2)).ne'
      exact (D.metric_volume.measure_pos_of_open_nonempty hW ⟨p,hpW⟩).trans_le (measure_mono hWS)
    rw [integral_neg,show (∫ x, G x * φ x ∂D.volume) = _ from hPair.2] at hOpp
    linarith
  · have hpB : p ∈ (J).boundary M := (J).compl_interior (M := M) ▸ hp
    rw [nativeGreenCandidate_boundary_zero h hpB hq]

private def sourceOne : Source := ⟨fun _ => 1,contMDiff_const⟩

private def cutoffComplement {q : M} (N : GreenPole.Neighborhoods (m := m) q) (n : ℕ) : Source :=
  sourceOne - N.cutoff n

omit [T2Space M] [CompactSpace M] [IsManifold J ∞ M] [MeasurableSpace M] [BorelSpace M]
  [PreconnectedSpace M] in
private theorem cutoffComplement_off {q : M} (N : GreenPole.Neighborhoods (m := m) q)
    (n : ℕ) : q ∉ tsupport (cutoffComplement N n : M → ℝ) := by
  rw [notMem_tsupport_iff_eventuallyEq]
  filter_upwards [N.cutoff_one_near n] with x hx
  change 1 - N.cutoff n x = 0
  rw [show N.cutoff n x = 1 from hx,sub_self]

/-- The genuine off-pole column is globally L¹. Smooth cutoffs
exhaust the punctured manifold and comparison bounds every integral
by the solution with constant right-hand side one. -/
theorem integrable_nativeGreenCandidate {q : M} (hq : q ∈ (J).interior M) :
    Integrable (fun p => nativeGreenCandidate h (p,q)) D.volume := by
  obtain ⟨N⟩ := GreenPole.exists_neighborhoods hq
  let G (x : M) := nativeGreenCandidate h (x,q)
  let F (n : ℕ) (x : M) := G x * cutoffComplement N n x
  have hG := measurable_nativeGreenCandidate h hq
  have hGp (p : M) : 0 ≤ G p := nativeGreenCandidate_nonneg h hq p
  have hF (n : ℕ) : Measurable (F n) := hG.mul
    ((show ContMDiff J R ∞ (cutoffComplement N n : M → ℝ) from
      (cutoffComplement N n).property).continuous.measurable)
  have hP (n : ℕ) := nativeGreenCandidate_integral_of_off_pole_source h hq
    (cutoffComplement N n) (cutoffComplement_off N n)
  have hBound (n : ℕ) :
      (∫⁻ x, ENNReal.ofReal (F n x) ∂D.volume) ≤ ENNReal.ofReal (D.smoothInverse h sourceOne q) := by
    have hN (x : M) : 0 ≤ F n x :=
      mul_nonneg (hGp x) (sub_nonneg.mpr (N.cutoff_in_range n x).2)
    rw [← ofReal_integral_eq_lintegral_ofReal (hP n).1 (Eventually.of_forall hN),(hP n).2]
    exact ENNReal.ofReal_le_ofReal (D.smoothInverse_mono h _ _ (fun x => by
      change 1 - N.cutoff n x ≤ 1
      linarith [(N.cutoff_in_range n x).1]) q)
  have hLim (x : M) :
      liminf (fun n => ENNReal.ofReal (F n x)) atTop = ENNReal.ofReal (G x) := by
    by_cases hx : x = q
    · subst x
      simp [F,G,nativeGreenCandidate_diagonal h q,liminf_const]
    · refine (liminf_congr ((N.eventually_off hx).mono fun n hn => ?_)).trans (liminf_const _)
      have hχ : N.cutoff n x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hs => hn (N.cutoff_support n hs))
      change ENNReal.ofReal (G x * (1-N.cutoff n x)) = ENNReal.ofReal (G x)
      rw [hχ,sub_zero,mul_one]
  refine ⟨hG.aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_norm]
  change (∫⁻ x, ENNReal.ofReal ‖G x‖ ∂D.volume) < (∞ : ℝ≥0∞)
  simp_rw [Real.norm_eq_abs,abs_of_nonneg (hGp _)]
  have hL := lintegral_liminf_le (μ := D.volume)
    (f := fun n x => ENNReal.ofReal (F n x)) (u := atTop) (fun n => (hF n).ennreal_ofReal)
  simpa only [hLim] using hL.trans_lt
    ((liminf_le_of_frequently_le' (Frequently.of_forall hBound)).trans_lt ENNReal.ofReal_lt_top)

end CalderonPatch

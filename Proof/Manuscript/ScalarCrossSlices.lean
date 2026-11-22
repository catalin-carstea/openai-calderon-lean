module

public import Proof.Manuscript.ScalarSolutionSpace
public import Proof.Manuscript.ClosedCrossSeries

import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

public section

open Set Metric Filter MeasureTheory CalderonN LocalMetricExtension
open scoped ContDiff ENNReal Topology

noncomputable section

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ}

theorem closedRestrict_ae {D S : Set (X n)} (H : ClosedSubmodule ℝ (ChartL2 D))
    (hSD : S ⊆ D) (u : H) :
    (closedRestrict H hSD u : X n → ℝ) =ᵐ[chartMeasure S] (u.1 : X n → ℝ) :=
  restrictL2_ae _ _

theorem norm_closedRestrict_le {D S : Set (X n)} (H : ClosedSubmodule ℝ (ChartL2 D))
    (hSD : S ⊆ D) : ‖closedRestrict H hSD‖ ≤ 1 := by
  let h := Measure.restrict_mono_set (volume : Measure (X n)) hSD
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
  change ‖restrictL2 h u.1‖ ≤ 1 * ‖u.1‖
  exact ((restrictL2 h).le_opNorm u.1).trans
    (mul_le_mul_of_nonneg_right (norm_restrictL2_le h) (norm_nonneg _))

theorem closedRestrict_injective {L : ScalarElliptic n} {D S : Set (X n)}
    (hD : IsOpen D) (hConn : IsConnected D) (hL : L.SmoothOn D) (hS : IsOpen S)
    (hSne : S.Nonempty) (hSD : S ⊆ D) :
    Function.Injective (closedRestrict (scalarSolutionL2 hD hL) hSD) := by
  intro u v hEq
  obtain ⟨f,hf,huf⟩ := (mem_scalarSolutionL2_iff hD hL u.1).mp u.2
  obtain ⟨g,hg,hvg⟩ := (mem_scalarSolutionL2_iff hD hL v.1).mp v.2
  have hSu := (closedRestrict_ae _ hSD u).trans (ae_mono (Measure.restrict_mono_set volume hSD) huf)
  have hSv := (closedRestrict_ae _ hSD v).trans (ae_mono (Measure.restrict_mono_set volume hSD) hvg)
  rw [hEq] at hSu
  have hFit := Measure.eqOn_open_of_ae_eq (hSu.symm.trans hSv) hS
    (hf.1.continuousOn.mono hSD) (hg.1.continuousOn.mono hSD)
  have hGlobal := eqOn_of_solutions_eqOn_open hD hConn hS hSne hSD hL hf hg hFit
  apply Subtype.ext
  apply Lp.ext
  have hfg : f =ᵐ[chartMeasure D] g :=
    (ae_restrict_mem hD.measurableSet).mono fun x hx => hGlobal hx
  exact huf.trans (hfg.trans hvg.symm)

theorem closedRestrict_scalar_mem {L : ScalarElliptic n} {D S : Set (X n)}
    (hD : IsOpen D) (hS : IsOpen S) (hSD : S ⊆ D) (hL : L.SmoothOn D)
    (u : scalarSolutionL2 hD hL) :
    closedRestrict (scalarSolutionL2 hD hL) hSD u ∈
      scalarSolutionL2 hS (⟨⟨fun i j => (hL.1.1 i j).mono hSD,fun x hx => hL.1.2 x (hSD hx)⟩,
        fun i => (hL.2.1 i).mono hSD,hL.2.2.mono hSD⟩ : L.SmoothOn S) := by
  obtain ⟨f,hf,heq⟩ := (mem_scalarSolutionL2_iff hD hL u.1).mp u.2
  refine (mem_scalarSolutionL2_iff hS _ _).mpr ⟨f,⟨hf.1.mono hSD,fun x hx => hf.2 x (hSD hx)⟩,?_⟩
  exact (closedRestrict_ae _ hSD u).trans (ae_mono (Measure.restrict_mono_set volume hSD) heq)

theorem closedInterpolation_of_interpolates {L : ScalarElliptic n} {D S O : Set (X n)}
    (hD : IsOpen D) (hL : L.SmoothOn D) (hSD : S ⊆ D) (hOD : O ⊆ D)
    {C γ : ℝ} (hInterp : L.Interpolates D S O C γ) :
    ClosedInterpolation (scalarSolutionL2 hD hL) hSD hOD C γ := by
  intro u
  obtain ⟨f,hf,heq⟩ := (mem_scalarSolutionL2_iff hD hL u.1).mp u.2
  have hMem : MemLp f 2 (chartMeasure D) := (Lp.memLp u.1).ae_eq heq
  have hDnorm : ‖u‖ = lpNorm f 2 (chartMeasure D) := by
    change ‖u.1‖ = _
    rw [Lp.norm_def, eLpNorm_congr_ae heq, toReal_eLpNorm]
  have hnorm {T : Set (X n)} (hTD : T ⊆ D) :
      ‖closedRestrict (scalarSolutionL2 hD hL) hTD u‖ = lpNorm f 2 (chartMeasure T) := by
    have hRep := (closedRestrict_ae _ hTD u).trans (ae_mono (Measure.restrict_mono_set volume hTD) heq)
    rw [Lp.norm_def, eLpNorm_congr_ae hRep, toReal_eLpNorm]
  rw [hnorm hOD, hnorm hSD, hDnorm]
  exact hInterp f hf hMem

theorem ProductSolvesOn.leftSlice {L M : ScalarElliptic n} {A B : Set (X n)}
    {F : X n × X n → ℝ} (h : L.ProductSolvesOn M (A ×ˢ B) F) {y : X n} (hy : y ∈ B) :
    L.SolvesOn A (fun x => F (x,y)) :=
  ⟨h.1.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hx => ⟨hx,hy⟩),
    fun x hx => h.2.1 (x,y) ⟨hx,hy⟩⟩

theorem ProductSolvesOn.rightSlice {L M : ScalarElliptic n} {A B : Set (X n)}
    {F : X n × X n → ℝ} (h : L.ProductSolvesOn M (A ×ˢ B) F) {x : X n} (hx : x ∈ A) :
    M.SolvesOn B (fun y => F (x,y)) :=
  ⟨h.1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hy => ⟨hx,hy⟩),
    fun y hy => h.2.2 (x,y) ⟨hx,hy⟩⟩

theorem ae_firstArm_scalar_slices {D S : Set (X n)} (hD : IsOpen D) (hS : MeasurableSet S)
    {L : ScalarElliptic n} (hL : L.SmoothOn D)
    {q : ChartProductL2 D S} {F : X n × X n → ℝ}
    (hq : (q : X n × X n → ℝ) =ᵐ[(chartMeasure D).prod (chartMeasure S)] F)
    (hF : ∀ y ∈ S, L.SolvesOn D (fun x => F (x,y))) :
    ∀ᵐ y ∂chartMeasure S, ∃ u : scalarSolutionL2 hD hL,
      (u.1 : X n → ℝ) =ᵐ[chartMeasure D] fun x => q (x,y) := by
  have hs := (Measure.measurePreserving_swap (μ := chartMeasure S)
    (ν := chartMeasure D)).quasiMeasurePreserving.ae hq
  filter_upwards [Measure.ae_ae_of_ae_prod hs, ae_memLp_left_of_prod q,
    ae_restrict_mem hS] with y hy hqMem hyS
  exact ⟨⟨hqMem.toLp _, (mem_scalarSolutionL2_iff hD hL _).mpr
    ⟨_,hF y hyS,hqMem.coeFn_toLp.trans hy⟩⟩,hqMem.coeFn_toLp⟩

theorem ae_secondArm_scalar_slices {D S : Set (X n)} (hD : IsOpen D) (hS : MeasurableSet S)
    {L : ScalarElliptic n} (hL : L.SmoothOn D)
    {q : ChartProductL2 S D} {F : X n × X n → ℝ}
    (hq : (q : X n × X n → ℝ) =ᵐ[(chartMeasure S).prod (chartMeasure D)] F)
    (hF : ∀ x ∈ S, L.SolvesOn D (fun y => F (x,y))) :
    ∀ᵐ x ∂chartMeasure S, ∃ u : scalarSolutionL2 hD hL,
      (u.1 : X n → ℝ) =ᵐ[chartMeasure D] fun y => q (x,y) := by
  filter_upwards [Measure.ae_ae_of_ae_prod hq, ae_memLp_right_of_prod q,
    ae_restrict_mem hS] with x hx hqMem hxS
  exact ⟨⟨hqMem.toLp _, (mem_scalarSolutionL2_iff hD hL _).mpr
    ⟨_,hF x hxS,hqMem.coeFn_toLp.trans hx⟩⟩,hqMem.coeFn_toLp⟩

end CalderonPaper.ScalarElliptic

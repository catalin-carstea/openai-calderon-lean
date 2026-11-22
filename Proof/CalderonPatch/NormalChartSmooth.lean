module

public import Proof.CalderonPatch.NormalChartHigher

import Proof.CalderonPatch.BoundaryVolume
import Proof.CalderonPatch.ChartCompactRegions
import Proof.CalderonPatch.HalfBallSmooth
import Proof.CalderonPatch.HalfBallZeroTraceValues
import Proof.CalderonPatch.InverseChartAE
import Proof.CalderonPatch.NormalChartInterior
import Proof.CalderonN.SobolevInteriorRepresentative
import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.Wkp.Classical
import Mathlib.Tactic

public section

noncomputable section
open Filter Metric MeasureTheory Set TopologicalSpace TauCeti
open scoped ContDiff ENNReal Manifold Topology

namespace CalderonPatch

open CalderonN (X I)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "N" => (m+1)
local notation "J" => 𝓡∂ N
local notation "R" => 𝓘(ℝ, ℝ)
local notation "μ" => (volume : Measure (X N))

set_option maxHeartbeats 5000000 in
/-- Local smooth regularity at a native boundary point for the actual
weak inverse. The representative reaches the boundary and vanishes there. -/
theorem exists_weakInverse_boundary_smooth_rep (D : DirichletData m M)
    {U : Set M} (hU : IsOpen U) {p : M} (hp : p ∈ U) (hpB : p ∈ (J).boundary M)
    (f : Lp ℝ 2 D.volume) {q : M → ℝ} (hq : ContMDiff J R ∞ q)
    (hf : (f : M → ℝ) =ᵐ[D.volume.restrict U] q) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
      ∃ u : M → ℝ, ContMDiffOn J R ∞ u V ∧ EqOn u 0 (V ∩ (J).boundary M) ∧
        (D.l2Value (D.weakDirichletInverse f) : M → ℝ) =ᵐ[D.volume.restrict V] u := by
  obtain ⟨A⟩ := exists_nativeBoundaryMetricChart D.metric p hpB
  let c := A.coord p
  have hcT : c ∈ A.coord.target := A.coord.map_source A.point_source
  have hcA : c ∈ A.ambient := (A.target_eq ▸ hcT).1
  have hcI : c ∈ inwardHalfSpace N := (A.target_eq ▸ hcT).2
  have hcU : A.coord.symm c ∈ U := (A.coord.left_inv A.point_source).symm ▸ hp
  obtain ⟨r₁,hr₁,hR₁⟩ := Metric.mem_nhds_iff.mp (A.open_ambient.mem_nhds hcA)
  obtain ⟨r₂,hr₂,hR₂⟩ := Metric.mem_nhdsWithin_iff.mp
    ((A.smooth_inverse.continuousOn c hcT).eventually (hU.mem_nhds hcU))
  let r := min r₁ r₂ / 2
  have hr : 0 < r := half_pos (lt_min hr₁ hr₂)
  let W := ball c r
  let C := closedBall c r ∩ inwardHalfSpace N
  have hC : IsCompact C := (isCompact_closedBall _ _).inter_right isClosed_inwardHalfSpace
  have hCn : C.Nonempty := ⟨c,mem_closedBall_self hr.le,hcI⟩
  have hr₁' : r < r₁ := ((half_lt_self (lt_min hr₁ hr₂)).trans_le (min_le_left _ _))
  have hr₂' : r < r₂ := ((half_lt_self (lt_min hr₁ hr₂)).trans_le (min_le_right _ _))
  have hCA : C ⊆ A.ambient := fun _ hx => hR₁ (closedBall_subset_ball hr₁' hx.1)
  have hWA : W ⊆ A.ambient :=
    ball_subset_closedBall.trans ((closedBall_subset_ball hr₁').trans hR₁)
  have hWC : W ∩ positiveHalfSpace N ⊆ C :=
    inter_subset_inter ball_subset_closedBall positiveHalfSpace_subset_inwardHalfSpace
  have hAE : W ∩ positiveHalfSpace N =ᵐ[μ] C := by
    filter_upwards [ae_ball_eq_closedBall c hr,ae_positiveHalfSpace_eq_inwardHalfSpace (n := N)]
      with z hzH hzI
    exact congrArg₂ And hzH hzI
  have hSrc : A.coord.symm '' (C ∩ inwardHalfSpace N) ⊆ U := by
    rintro _ ⟨z,hz,rfl⟩
    exact hR₂ ⟨closedBall_subset_ball hr₂' hz.1.1,A.target_eq.symm ▸ ⟨hCA hz.1,hz.2⟩⟩
  let s := r/2
  have hs : 0 < s := half_pos hr
  have hBall : closedBall c s ⊆ W := closedBall_subset_ball (half_lt_self hr)
  obtain ⟨ψ,hψ,hψc,hψs,hψOne⟩ :=
    CalderonN.Elliptic.exists_plateau_cutoff isOpen_ball (isCompact_closedBall c s) hBall
  let H := positiveHalfSpaceOpens N
  let O : Opens (X N) := ⟨ball c s ∩ positiveHalfSpace N,isOpen_ball.inter isOpen_positiveHalfSpace⟩
  let v (z : X N) := D.l2Value (D.weakDirichletInverse f) (A.coord.symm z)
  have hOW : (O : Set (X N)) ⊆ W ∩ positiveHalfSpace N :=
    inter_subset_inter_left _ (ball_subset_closedBall.trans hBall)
  have hOH : O ≤ H := inter_subset_right
  have hAll (k : ℕ) : ∃ Z : Wkp μ H 2 (k+1),
      Wkp.firstOrder k Z ∈ w1p0Submodule μ H 2 ∧
      (Wkp.value (k+1) Z : X N → ℝ) =ᵐ[(μ).restrict O] v := by
    obtain ⟨Z,hZ₀,hZ⟩ := A.exists_localized_sobolev_order D isOpen_ball hC hCn hCA hWA hWC
      hAE f hq hSrc hf hψ hψc hψs k
    refine ⟨Z,hZ₀,?_⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hOW hZ,
      ae_restrict_mem O.isOpen.measurableSet] with z hz hzO
    rw [hz,(hψOne z (ball_subset_closedBall hzO.1)).eq_of_nhds,one_mul]
  have hSobolev (k : ℕ) : ∃ Z : Wkp μ O 2 k,
      (Wkp.value k Z : X N → ℝ) =ᵐ[(μ).restrict O] v := by
    obtain ⟨Z,_,hZ⟩ := hAll k
    let T := Wkp.lowerOrder k Z
    exact ⟨Wkp.restrictL hOH k T,(Wkp.value_restrictL_ae hOH k T).trans
      (by simpa only [T,← Wkp.value_succ] using hZ)⟩
  have hSmooth : ∃ z : X N → ℝ, ContDiffOn ℝ ∞ z O ∧ z =ᵐ[(μ).restrict O] v := by
    apply CalderonN.exists_contDiffOn_ae_eq O.isOpen
    intro x hx
    obtain ⟨ρ,hρ,hB⟩ := Metric.mem_nhds_iff.mp (O.isOpen.mem_nhds hx)
    let B : Opens (X N) := ⟨ball x ρ,isOpen_ball⟩
    refine ⟨ρ,hρ,hB,fun k => ?_⟩
    obtain ⟨Z,hZ⟩ := hSobolev k
    have hBO : B ≤ O := hB
    exact ⟨Wkp.restrictL hBO k Z,(Wkp.value_restrictL_ae hBO k Z).trans
      (ae_restrict_of_ae_restrict_of_subset hB hZ)⟩
  obtain ⟨z,hz,hzV⟩ := hSmooth
  have hLp (k : ℕ) : MemLp (iteratedFDeriv ℝ k z) 2 ((μ).restrict O) := by
    obtain ⟨Z,hZ⟩ := hSobolev k
    exact Wkp.memLp_iteratedFDeriv_of_contDiffOn k Z (hz.of_le (by simp)) (hZ.trans hzV.symm) k le_rfl
  obtain ⟨b,hb,hbz⟩ := exists_contDiffOn_halfBall_closure_of_bulk_jets hs hz hLp
  let S := ball c (s/4)
  have hSO : S ∩ positiveHalfSpace N ⊆ (O : Set (X N)) :=
    inter_subset_inter_left _ (ball_subset_ball (by linarith))
  have hbS : ContDiffOn ℝ ∞ b (S ∩ inwardHalfSpace N) :=
    hb.mono (halfBall_inward_subset_closure c (s/4))
  have hbV : b =ᵐ[(μ).restrict (S ∩ positiveHalfSpace N)] v := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hSO hzV,
      ae_restrict_mem (isOpen_ball.inter isOpen_positiveHalfSpace).measurableSet] with x hx hxS
    exact (hbz hxS).trans hx
  obtain ⟨Z₀,hZ₀,hValue⟩ := hAll 0
  let w₀ : W1p0 μ H 2 := ⟨Wkp.firstOrder 0 Z₀,hZ₀⟩
  have hTraceVal : (W1p.value (w₀ : W1p μ H 2) : X N → ℝ) =ᵐ[(μ).restrict (S ∩ positiveHalfSpace N)] b := by
    rw [show W1p.value (w₀ : W1p μ H 2) = Wkp.value (0+1) Z₀ from Wkp.value_firstOrder 0 Z₀]
    exact EventuallyEq.trans (ae_restrict_of_ae_restrict_of_subset hSO hValue) hbV.symm
  have hb0 (x : X N) (hx : x ∈ S) (hx₀ : x 0 = 0) : b x = 0 :=
    eq_zero_on_face_of_locally_continuous_zero_trace w₀ isOpen_ball hbS.continuousOn hTraceVal hx hx₀
  let V := A.coord.source ∩ A.coord ⁻¹' S
  have hV : IsOpen V := A.smooth.continuousOn.isOpen_inter_preimage A.open_source isOpen_ball
  have hpV : p ∈ V := ⟨A.point_source,mem_ball_self (by positivity)⟩
  have hSV : S ⊆ W := ball_subset_ball (by dsimp [s]; linarith)
  have hMap : MapsTo A.coord V (S ∩ inwardHalfSpace N) := fun x hx =>
    ⟨hx.2,(A.target_eq ▸ A.coord.map_source hx.1).2⟩
  let u : M → ℝ := b ∘ A.coord
  refine ⟨V,hV,hpV,?_,u,hbS.contMDiffOn.comp (A.smooth.mono inter_subset_left) hMap,?_,?_⟩
  · intro x hx
    rw [← A.coord.left_inv hx.1]
    have hxPos := hMap hx
    exact hSrc (mem_image_of_mem _ ⟨⟨ball_subset_closedBall (hSV hxPos.1),hxPos.2⟩,hxPos.2⟩)
  · intro x hx
    have hh : ¬ 0 < A.coord x 0 := fun h =>
      ((J).isInteriorPoint_iff_not_isBoundaryPoint x).1 ((A.interior_iff x hx.1.1).2 h) hx.2
    exact hb0 (A.coord x) hx.1.2 (le_antisymm (le_of_not_gt hh) (hMap hx.1).2)
  · obtain ⟨e,hT,hCoord,hInv,heI,he,hes,_⟩ := A.exists_interior_restriction isOpen_ball (hSV.trans hWA)
    have heV : e.source = V ∩ (J).interior M := by
      ext x
      refine ⟨fun hx => ⟨?_,heI hx⟩,fun hx => ?_⟩
      · have heT := hT ▸ e.map_source hx
        refine ⟨?_,hCoord ▸ heT.1⟩
        rw [← e.left_inv hx,hInv]
        exact A.coord.map_target (A.target_eq.symm ▸ ⟨hWA (hSV heT.1),positiveHalfSpace_subset_inwardHalfSpace heT.2⟩)
      · have hcoordT : A.coord x ∈ e.target :=
          hT.symm ▸ ⟨hx.1.2,(A.interior_iff x hx.1.1).1 hx.2⟩
        have ht := e.map_target hcoordT
        rwa [hInv,A.coord.left_inv hx.1.1] at ht
    have hAE' : (D.l2Value (D.weakDirichletInverse f) : M → ℝ) =ᵐ[D.volume.restrict e.source] u := by
      apply ae_native_of_ae_coordinate D.metric D.volume D.metric_volume e heI he hes
      rw [hT]
      filter_upwards [hbV,ae_restrict_mem (isOpen_ball.inter isOpen_positiveHalfSpace).measurableSet]
        with y hy hyS
      have hyT : y ∈ e.target := hT.symm ▸ hyS
      rw [show u (e.symm y) = b y by simp only [u,Function.comp_apply,← hCoord,e.right_inv hyT],hInv]
      exact hy.symm
    have hmeas : e.source =ᵐ[D.volume] V := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp
        (metricVolume_boundary_eq_zero D.metric D.volume D.metric_volume)] with x hx
      apply propext
      rw [heV]
      exact and_iff_left (((J).isInteriorPoint_iff_not_isBoundaryPoint x).2 hx)
    rwa [← Measure.restrict_congr_set hmeas]

end CalderonPatch

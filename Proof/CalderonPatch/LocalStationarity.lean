module

public import Proof.CalderonPatch.BoundaryChartTests
public import Proof.CalderonPatch.InteriorStationarity
public import Proof.CalderonPatch.NormalChartFunctions

import Mathlib.Tactic.Linarith

public section

noncomputable section
open Filter MeasureTheory Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X coordDeriv)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (𝓡∂ (m + 1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

local notation "N" => (m + 1)
local notation "J" => 𝓡∂ N
local notation "R" => 𝓘(ℝ, ℝ)
local notation "H" => inwardHalfSpace N

omit [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The native part of a half box is an open neighborhood in the
manifold, including points on the flat face. -/
theorem NativeBoundaryMetricChart.isOpen_preimage_normalHalfBox
    {g : SmoothMetric N M} {p : M} (D : NativeBoundaryMetricChart g p) (a b : I N → ℝ) :
    IsOpen (D.coord.source ∩ D.coord ⁻¹' normalHalfBox a b) := by
  let W := (⋂ i : I N, {x : X N | x i < b i}) ∩
    (⋂ i : {i : I N // i ≠ 0}, {x : X N | a i.1 < x i.1})
  have hW : IsOpen W := (isOpen_iInter_of_finite fun i =>
      isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) i).continuous continuous_const).inter
    (isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) i.1).continuous)
  have hEq : D.coord.source ∩ D.coord ⁻¹' normalHalfBox a b = D.coord.source ∩ D.coord ⁻¹' W := by
    ext x
    have hP {x : X N} (h : x ∈ W) (hpos : x ∈ H) : x ∈ normalHalfBox a b :=
      ⟨hpos, fun i => mem_iInter.mp h.1 i, fun i hi => mem_iInter.mp h.2 ⟨i,hi⟩⟩
    constructor
    · rintro ⟨hx,hN⟩
      exact ⟨hx, mem_iInter.mpr hN.2.1,mem_iInter.mpr (fun i => hN.2.2 i i.2)⟩
    · rintro ⟨hx,hW'⟩
      have hH : D.coord x ∈ H := (D.target_eq ▸ D.coord.map_source hx : _ ∈ D.ambient ∩ H).2
      exact ⟨hx,hP hW' hH⟩
  rw [hEq]
  exact D.smooth.continuousOn.isOpen_inter_preimage D.open_source hW

omit [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Every native normal chart contains a small closed half box
whose relative interior contains the boundary point. -/
theorem NativeBoundaryMetricChart.exists_normalHalfBox
    {g : SmoothMetric N M} {p : M} (D : NativeBoundaryMetricChart g p) :
    ∃ a b : I N → ℝ, a ≤ b ∧ a 0 = 0 ∧ 0 < b 0 ∧
      D.coord p ∈ normalHalfBox a b ∧ MapsTo (WithLp.toLp 2) (Icc a b) D.ambient := by
  let q := WithLp.ofLp (D.coord p)
  have hq : q 0 = 0 := D.point_face
  have hpD : D.coord p ∈ D.ambient :=
    (D.target_eq ▸ D.coord.map_source D.point_source : _ ∈ D.ambient ∩ H).1
  have hU : IsOpen ((WithLp.toLp 2) ⁻¹' D.ambient) :=
    D.open_ambient.preimage (PiLp.continuous_toLp 2 (fun _ : I N => ℝ))
  have hqU : q ∈ (WithLp.toLp 2) ⁻¹' D.ambient := by
    change WithLp.toLp 2 (WithLp.ofLp (D.coord p)) ∈ D.ambient
    rwa [WithLp.toLp_ofLp]
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hqU)
  let a (i : I N) := if i = 0 then 0 else q i - r / 2
  let b (i : I N) := q i + r / 2
  have hLower (i : I N) : q i - r / 2 ≤ a i := by
    by_cases hi : i = 0
    · subst i
      simp only [a,ite_eq_left rfl,hq]
      linarith
    · simp [a,hi]
  have ha : a 0 = 0 := ite_eq_left rfl
  have hb : 0 < b 0 := by simp only [b,hq,zero_add]; positivity
  refine ⟨a,b,?_,ha,hb,?_,?_⟩
  · intro i
    by_cases hi : i = 0
    · subst i
      exact ha.symm ▸ hb.le
    · simp only [a,b,hi,ite_false]
      linarith
  · refine ⟨D.point_face.ge,?_,?_⟩
    · intro i
      change q i < q i + r / 2
      linarith
    · intro i hi
      change (if i = 0 then 0 else q i - r / 2) < q i
      rw [ite_eq_right hi]
      linarith
  · intro x hx
    apply hBall
    apply Metric.mem_ball.mpr
    apply (dist_pi_lt_iff hr).mpr
    intro i
    rw [Real.dist_eq]
    have hL := (hLower i).trans (hx.1 i)
    have hR := hx.2 i
    change x i ≤ q i + r / 2 at hR
    exact abs_lt.mpr ⟨by linarith,by linarith⟩

/-- In a boundary chart, smooth zero-trace tests supported in the
half box have vanishing integrated native Green pairing. -/
theorem integral_nativeGreenPairing_zeroTrace_normalHalfBox
    {g : SmoothMetric N M} {p : M} (D : NativeBoundaryMetricChart g p)
    (μ : Measure M) (hμ : IsMetricVolume g μ)
    {a b : I N → ℝ} (hab : a ≤ b) (hBottom : a 0 = 0)
    (hBox : MapsTo (WithLp.toLp 2) (Icc a b) D.ambient)
    {u v : M → ℝ} (hu : ContMDiff J R ∞ u) (hv : ContMDiff J R ∞ v)
    (hZeroTrace : EqOn v 0 ((J).boundary M))
    (hSupport : tsupport v ⊆ D.coord.source ∩ D.coord ⁻¹' normalHalfBox a b) :
    (∫ x, v x * nativeLaplace g u x + energyPairingDensity g u v x ∂μ) = 0 := by
  let C := (WithLp.toLp 2) '' Icc a b
  have hC : IsCompact C := isCompact_Icc.image (PiLp.continuous_toLp 2 (fun _ : I N => ℝ))
  obtain ⟨u₀,U₁,hu₀,hU₁,hCU₁,hU₁D,hU⟩ := D.exists_smooth_function_extension hu hC (image_subset_iff.mpr hBox)
  obtain ⟨v₀,U₂,hv₀,hU₂,hCU₂,hU₂D,hV⟩ := D.exists_smooth_function_extension hv hC (image_subset_iff.mpr hBox)
  let U := U₁ ∩ U₂
  have hUD : U ⊆ D.ambient := inter_subset_left.trans hU₁D
  have hC' : MapsTo (WithLp.toLp 2) (Icc a b) U :=
    fun z hz => ⟨hCU₁ (mem_image_of_mem _ hz),hCU₂ (mem_image_of_mem _ hz)⟩
  have hV' := hV.symm.mono (inter_subset_inter_left H (show U ⊆ U₂ from inter_subset_right))
  have h := integral_nativeGreenPairing_normalHalfBox D μ hμ hab hBottom (hU₁.inter hU₂) hUD hC'
    hu hv hu₀.contDiffOn hv₀.contDiffOn
    (hU.symm.mono (inter_subset_inter_left H (show U ⊆ U₁ from inter_subset_left))) hV' hSupport
  rw [h,neg_eq_zero]
  calc
    _ = ∫ z in Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0), (0 : ℝ) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro z hz
      let x : X N := normalFacePoint (WithLp.toLp 2 z)
      have h0 : x 0 = 0 := normalFacePoint_height _
      have hX : x ∈ U ∩ H := ⟨hC' (insertNth_mem_box 0 ⟨hBottom.le,hBottom ▸ hab 0⟩ hz),
        (mem_inwardHalfSpace).mpr h0.ge⟩
      have hT : x ∈ D.coord.target := D.target_eq.symm ▸ ⟨hUD hX.1,hX.2⟩
      have hB : D.coord.symm x ∈ (J).boundary M := by
        rw [← (J).compl_interior]
        intro hi
        have hP := (D.interior_iff _ (D.coord.map_target hT)).mp hi
        rw [D.coord.right_inv hT] at hP
        exact (mem_positiveHalfSpace.mp hP).ne' h0
      have hz' : v₀ x = 0 := (hV' hX).symm.trans (hZeroTrace hB)
      change v₀ x * (CalderonN.chartVolume D.field x * coordDeriv 0 u₀ x) = 0
      rw [hz',zero_mul]
    _ = _ := by simp

/-- An open cover with the local zero-trace Green identity. In the
interior the test is supported strictly in a chart, and at a boundary
point the test is supported in a relative half box. -/
theorem exists_neighborhood_zeroTrace_greenPairing (g : SmoothMetric N M)
    (μ : Measure M) (hμ : IsMetricVolume g μ) (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∀ u v : M → ℝ, ContMDiff J R ∞ u → ContMDiff J R ∞ v →
        EqOn v 0 ((J).boundary M) → tsupport v ⊆ U →
        (∫ x, v x * nativeLaplace g u x + energyPairingDensity g u v x ∂μ) = 0 := by
  by_cases hp : p ∈ (J).interior M
  · obtain ⟨e,hPe,_,heI,he,hes⟩ := exists_interiorChart p hp isOpen_univ (mem_univ p)
    exact ⟨e.source,e.open_source,hPe,fun u v hu hv _ hS =>
      integral_nativeGreenPairing_interior_support_eq_zero g μ hμ e heI he hes hu hv
        (HasCompactSupport.of_compactSpace v) hS⟩
  · have hpB : p ∈ (J).boundary M := by
      rw [← (J).compl_interior (M := M)]
      exact hp
    obtain ⟨D⟩ := exists_nativeBoundaryMetricChart g p hpB
    obtain ⟨a,b,hab,hBottom,_,hpBox,hBox⟩ := D.exists_normalHalfBox
    exact ⟨_,D.isOpen_preimage_normalHalfBox a b,⟨D.point_source,hpBox⟩,
      fun _ _ hu hv hZ hS => integral_nativeGreenPairing_zeroTrace_normalHalfBox D μ hμ hab
        hBottom hBox hu hv hZ hS⟩

end CalderonPatch

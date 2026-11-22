module

public import Proof.CalderonPatch.GaugeFromCauchy
public import Proof.CalderonPatch.IsometryInCommonNormals
public import Proof.CalderonPatch.NormalChartFunctions
public import Proof.CalderonPatch.NormalChartInterior

import Proof.CalderonN.LocalChartExtension

public section

noncomputable section
open Filter Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X coordDeriv)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "R" => 𝓘(ℝ, ℝ)
local notation "H" => inwardHalfSpace n

variable [ConnectedSpace M]

/-- At a fixed seam, equality of the measured normal derivatives in
common normal coordinates gives equality of the pulled-back harmonic
functions on the original manifold. -/
theorem eq_of_nativeHarmonic_normalDerivativeAgreement
    {g₁ g₂ : SmoothMetric n M} (Φ : M ≃ₘ⟮J, J⟯ M) (hΦ : PullbackMetric g₁ g₂ Φ)
    {p : M} (hpB : p ∈ (J).boundary M)
    (D₁ : NativeBoundaryMetricChart g₁ p) (D₂ : NativeBoundaryMetricChart g₂ p)
    {V : Set M} (hV : IsOpen V) (hpV : p ∈ V)
    (hFix : EqOn Φ id (V ∩ (J).boundary M))
    (hCoords : EqOn D₁.coord D₂.coord (V ∩ (J).boundary M))
    {u₁ u₂ : M → ℝ} (hu₁ : ContMDiff J R ∞ u₁) (hu₂ : ContMDiff J R ∞ u₂)
    (hH₁ : EqOn (nativeLaplace g₁ u₁) 0 ((J).interior M))
    (hH₂ : EqOn (nativeLaplace g₂ u₂) 0 ((J).interior M))
    (hTrace : EqOn u₁ u₂ ((J).boundary M))
    (hDerivative : D₁.inwardDerivative u₁ =ᶠ[𝓝[{y : X n | y (0 : I n) = 0}] (D₂.coord p)]
      D₂.inwardDerivative u₂) :
    u₂ = u₁ ∘ Φ := by
  let x := D₂.coord p
  have hxT : x ∈ D₂.coord.target := D₂.coord.map_source D₂.point_source
  have hxA : x ∈ D₂.ambient := (D₂.target_eq ▸ hxT : x ∈ D₂.ambient ∩ H).1
  have hxEq : D₁.coord p = x := hCoords ⟨hpV,hpB⟩
  obtain ⟨a,ha,haU⟩ := D₁.exists_smooth_function_germ hu₁
  obtain ⟨b,hb,hbU⟩ := D₂.exists_smooth_function_germ hu₂
  have hDa := D₁.coordDeriv_eq_inwardDerivative ha haU
  have hDb := D₂.coordDeriv_eq_inwardDerivative hb hbU
  rw [hxEq] at hDa haU
  have hFaceH : {y : X n | y (0 : I n) = 0} ⊆ H := fun _ hy =>
    (mem_inwardHalfSpace).mpr hy.ge
  have hNormal := (hDa.filter_mono (nhdsWithin_mono _ hFaceH)).trans
    (hDerivative.trans (hDb.filter_mono (nhdsWithin_mono _ hFaceH)).symm)
  have hAlign := eventually_eq_in_commonNormalCoordinates Φ hΦ D₁ D₂ hV hpV hpB hFix hCoords
  have hDest : ∀ᶠ z in 𝓝[D₂.coord.target] x,
      Φ (D₂.coord.symm z) ∈ D₁.coord.source ∧ D₂.coord.symm z ∈ V := by
    have h := D₂.smooth_inverse.continuousOn x hxT
    have hpFix : Φ p = p := hFix ⟨hpV,hpB⟩
    have hp2 : D₂.coord.symm x = p := D₂.coord.left_inv D₂.point_source
    exact ((Φ.continuous.continuousAt.comp_continuousWithinAt h).eventually_mem
      (D₁.open_source.mem_nhds (by rw [Function.comp_apply, hp2, hpFix]; exact D₁.point_source))).and
      (h.eventually_mem (hV.mem_nhds (hp2.symm ▸ hpV)))
  have hWithin : 𝓝[H] x = 𝓝[D₂.coord.target] x := by
    rw [D₂.target_eq, nhdsWithin_inter_of_mem
      (mem_nhdsWithin_of_mem_nhds (D₂.open_ambient.mem_nhds hxA))]
  rw [← hWithin] at hDest
  have hPull : a =ᶠ[𝓝[H] x] u₁ ∘ Φ ∘ D₂.coord.symm := by
    filter_upwards [haU,hAlign,hDest] with z hz hId hs
    change D₁.coord (Φ (D₂.coord.symm z)) = z at hId
    change a z = u₁ (Φ (D₂.coord.symm z))
    exact hz.trans ((congrArg (u₁ ∘ D₁.coord.symm) hId.symm).trans
      (congrArg u₁ (D₁.coord.left_inv hs.1)))
  have hRead : ∀ᶠ z in 𝓝 x, z ∈ D₂.ambient ∧
      (z ∈ H → a z = (u₁ ∘ Φ ∘ D₂.coord.symm) z ∧
        b z = (u₂ ∘ D₂.coord.symm) z ∧ D₂.coord.symm z ∈ V) ∧
      (z (0 : I n) = 0 → coordDeriv 0 a z = coordDeriv 0 b z) :=
    Filter.Eventually.and (D₂.open_ambient.mem_nhds hxA) ((eventually_nhdsWithin_iff.mp
      (hPull.and (hbU.and (hDest.mono fun _ h => h.2)))).and (eventually_nhdsWithin_iff.mp hNormal))
  obtain ⟨γ,hγ,hγNear⟩ := CalderonN.exists_global_chart_metric D₂.open_ambient
    (isCompact_singleton (x := x)) (singleton_subset_iff.mpr hxA) D₂.smooth_field
  obtain ⟨r,hr,hrRead⟩ := Metric.mem_nhds_iff.mp (hRead.and (hγNear x (mem_singleton x)))
  let U := ball x r
  have hUD : U ⊆ D₂.ambient := fun _ h => (hrRead h).1.1
  obtain ⟨e,hET,_,hInv,heI,he,hes,hMetric⟩ := D₂.exists_interior_restriction isOpen_ball hUD
  have hFace : (boundaryFace U (0 : I n)).Nonempty :=
    ⟨x,mem_ball_self hr,D₂.point_face⟩
  have hNe : e.source.Nonempty := by
    have ht : x ∈ closure e.target := by
      rw [hET]
      exact boundaryFace_subset_closure_positive (i := (0 : I n)) isOpen_ball
        ⟨mem_ball_self hr,D₂.point_face⟩
    obtain ⟨z,hz⟩ := closure_nonempty_iff.mp ⟨x,ht⟩
    exact ⟨e.symm z,e.map_target hz⟩
  have hComp : EqOn (nativeLaplace g₂ (u₁ ∘ Φ)) 0 ((J).interior M) := by
    intro q hq
    have hΦq : Φ q ∈ (J).interior M := by
      rw [← Φ.image_interior (by simp)]
      exact mem_image_of_mem Φ hq
    exact (nativeLaplace_comp_of_pullbackMetric Φ hΦ hu₁ hq).trans (hH₁ hΦq)
  apply eq_of_native_harmonic_agreement g₂ hu₂ (hu₁.comp Φ.contMDiff) hH₂ hComp
    e.open_source hNe heI
  refine eqOn_native_harmonic_of_agreeing_cauchy g₂ hu₂ (hu₁.comp Φ.contMDiff) hH₂ hComp
    e heI he hes isOpen_ball ((convex_ball x r).isConnected ⟨x,mem_ball_self hr⟩)
    hFace hET hγ ?_ hb ha ?_ ?_ ?_ ?_
  · intro z hz
    have hrz : z ∈ U := (hET ▸ hz : z ∈ U ∩ positiveHalfSpace n).1
    exact (hMetric hz).trans (hrRead hrz).2.symm
  · intro z hz
    have hz' : z ∈ U ∩ positiveHalfSpace n := hET ▸ hz
    have h := ((hrRead hz'.1).1.2.1 (positiveHalfSpace_subset_inwardHalfSpace hz'.2)).2.1
    simpa only [hInv, Function.comp_apply] using h.symm
  · intro z hz
    have hz' : z ∈ U ∩ positiveHalfSpace n := hET ▸ hz
    have h := ((hrRead hz'.1).1.2.1 (positiveHalfSpace_subset_inwardHalfSpace hz'.2)).1
    simpa only [hInv, Function.comp_apply] using h.symm
  · intro z hz
    have hzH : z ∈ H := (mem_inwardHalfSpace).mpr hz.2.ge
    obtain ⟨hA,hB,hV⟩ := (hrRead hz.1).1.2.1 hzH
    have hzT : z ∈ D₂.coord.target := D₂.target_eq.symm ▸ ⟨hUD hz.1,hzH⟩
    have hzB : D₂.coord.symm z ∈ (J).boundary M := by
      rw [← (J).compl_interior]
      intro h
      have hPos := (D₂.interior_iff _ (D₂.coord.map_target hzT)).mp h
      rw [D₂.coord.right_inv hzT] at hPos
      exact ((mem_positiveHalfSpace).mp hPos).ne' hz.2
    rw [hB,hA, Function.comp_apply, Function.comp_apply, Function.comp_apply, hFix ⟨hV,hzB⟩]
    exact (hTrace hzB).symm
  · exact fun z hz => ((hrRead hz.1).1.2.2 hz.2).symm

variable [CompactSpace M]

/-- Agreement of normal derivatives of the measured Dirichlet
solutions at one fixed seam determines the gauge on the whole patch. -/
theorem fixesPatch_of_native_normalDerivativeAgreement {g₁ g₂ : SmoothMetric n M}
    {Γ : Set ((𝓡∂ n).boundary M)} (hΓ : IsOpen Γ)
    (Φ : M ≃ₘ⟮J, J⟯ M) (hΦ : PullbackMetric g₁ g₂ Φ)
    {p : M} (hpB : p ∈ (J).boundary M)
    (D₁ : NativeBoundaryMetricChart g₁ p) (D₂ : NativeBoundaryMetricChart g₂ p)
    {V : Set M} (hV : IsOpen V) (hpV : p ∈ V)
    (hFix : EqOn Φ id (V ∩ (J).boundary M))
    (hCoords : EqOn D₁.coord D₂.coord (V ∩ (J).boundary M))
    (hSolutions : ∀ f : M → ℝ, ContMDiff J R ∞ f →
      tsupport (fun q : (J).boundary M => f q) ⊆ Γ →
      ∃ (u₁ u₂ : M → ℝ), ContMDiff J R ∞ u₁ ∧ ContMDiff J R ∞ u₂ ∧
        EqOn u₁ f ((J).boundary M) ∧ EqOn u₂ f ((J).boundary M) ∧
        EqOn (nativeLaplace g₁ u₁) 0 ((J).interior M) ∧
        EqOn (nativeLaplace g₂ u₂) 0 ((J).interior M) ∧
        D₁.inwardDerivative u₁ =ᶠ[𝓝[{y : X n | y (0 : I n) = 0}] (D₂.coord p)]
          D₂.inwardDerivative u₂) :
    FixesPatch Γ Φ := by
  apply fixesPatch_of_supported_trace_eq hΓ Φ
  intro f hf hfs q
  obtain ⟨u₁,u₂,hu₁,hu₂,hT₁,hT₂,hH₁,hH₂,hDerivative⟩ := hSolutions f hf hfs
  have h := eq_of_nativeHarmonic_normalDerivativeAgreement Φ hΦ hpB D₁ D₂ hV hpV hFix hCoords
    hu₁ hu₂ hH₁ hH₂ (fun x hx => (hT₁ hx).trans (hT₂ hx).symm) hDerivative
  have hΦq : Φ q ∈ (J).boundary M :=
    (Φ.image_boundary (by simp)).subset (mem_image_of_mem Φ q.property)
  exact (hT₂ q.property).symm.trans ((congrFun h q).trans (hT₁ hΦq))

end CalderonPatch

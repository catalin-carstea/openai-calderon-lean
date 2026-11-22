module

public import Proof.CalderonPatch.NativeBoundaryLayerResidual
public import Proof.CalderonPatch.BoundaryChartTests

import Proof.CalderonPatch.NormalChartInterior
import Proof.CalderonN.GreenWeak
import Mathlib.Tactic

public section

noncomputable section
open Filter Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (X I laplace)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]

local notation "N" => (n + 1)
local notation "J" => 𝓡∂ N
local notation "R" => 𝓘(ℝ, ℝ)
local notation "Y" => X n
local notation "Z" => X N

/-- The coordinate Laplacian of any signed smooth chart test gives its
true native Laplacian at points on the interior side of the chart. -/
theorem NativeBoundaryMetricChart.nativeLaplace_boundaryChartTest
    {g : SmoothMetric N M} {p : M} (D : NativeBoundaryMetricChart g p)
    {f : Z → ℝ} (hf : ContDiff ℝ ∞ f)
    {q : M} (hq : q ∈ D.coord.source) (hqI : q ∈ (J).interior M) :
    nativeLaplace g (boundaryChartTest D f) q = laplace D.field f (D.coord q) := by
  obtain ⟨e,hT,he,heInv,heI,heSmooth,heInvSmooth,hMetric⟩ :=
    D.exists_interior_restriction D.open_ambient Subset.rfl
  have hzT : D.coord q ∈ e.target := hT.symm ▸
    ⟨(show D.coord q ∈ D.ambient ∩ inwardHalfSpace N from D.target_eq ▸ D.coord.map_source hq).1,
      (D.interior_iff q hq).mp hqI⟩
  have heq : e.symm (D.coord q) = q := by
    rw [heInv,D.coord.left_inv hq]
  have hqe : q ∈ e.source := heq ▸ e.map_target hzT
  have hsub : e.source ⊆ D.coord.source := by
    intro x hx
    have hxT := e.map_source hx
    rw [he,hT] at hxT
    have hxD : D.coord x ∈ D.coord.target := D.target_eq.symm ▸
      ⟨hxT.1,positiveHalfSpace_subset_inwardHalfSpace hxT.2⟩
    have hxs := D.coord.map_target hxD
    have hxEq := e.left_inv hx
    rw [he,heInv] at hxEq
    exact hxEq ▸ hxs
  have hu : ContMDiffOn J R ∞ (boundaryChartTest D f) e.source := by
    refine (hf.contMDiff.comp_contMDiffOn (D.smooth.mono hsub)).congr fun x hx => ?_
    simp only [boundaryChartTest,indicator_of_mem (hsub hx)]
  have hRead : EqOn (boundaryChartTest D f ∘ e.symm) f e.target := by
    rw [heInv]
    apply (boundaryChartTest_comp_inverse D f).mono
    rw [hT,D.target_eq]
    exact inter_subset_inter_right _ positiveHalfSpace_subset_inwardHalfSpace
  rw [nativeLaplace_eq_coordinate g e heI heSmooth heInvSmooth hu hqe]
  exact (CalderonN.laplace_congrOn e.open_target hMetric hRead (e.map_source hqe)).trans
    (congrArg (laplace D.field f) (congrFun he q))

namespace BoundaryLayer

/-- Extend either real-linear component of a signed complex wave by
zero outside the normal chart. -/
@[expose] def nativeWaveComponent {g : SmoothMetric N M} {p : M} (D : NativeBoundaryMetricChart g p)
    (V : Y × ℝ → ℂ) (L : ℂ →L[ℝ] ℝ) : M → ℝ :=
  boundaryChartTest D (L ∘ V ∘ signedLayerCoordinates.symm)

theorem waveComponent_support {V : Y × ℝ → ℂ} (L : ℂ →L[ℝ] ℝ) :
    tsupport (L ∘ V ∘ signedLayerCoordinates.symm) ⊆
      signedLayerCoordinates.symm ⁻¹' tsupport V := by
  apply closure_minimal _ ((isClosed_tsupport V).preimage signedLayerCoordinates.symm.continuous)
  intro x hx
  apply subset_closure
  intro hn
  apply hx
  change L (V (signedLayerCoordinates.symm x)) = 0
  rw [hn,map_zero]

theorem waveComponent_compactSupport {V : Y × ℝ → ℂ} (hV : HasCompactSupport V)
    (L : ℂ →L[ℝ] ℝ) : HasCompactSupport (L ∘ V ∘ signedLayerCoordinates.symm) :=
  (signedLayerCoordinates.symm.toHomeomorph.isCompact_preimage.mpr hV).of_isClosed_subset
    (isClosed_tsupport _) (waveComponent_support L)

theorem nativeWaveComponent_contMDiff {g : SmoothMetric N M} {p : M}
    (D : NativeBoundaryMetricChart g p) {V : Y × ℝ → ℂ} (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (L : ℂ →L[ℝ] ℝ)
    (hSupp : signedLayerCoordinates.symm ⁻¹' tsupport V ∩ inwardHalfSpace N ⊆ D.coord.target) :
    ContMDiff J R ∞ (nativeWaveComponent D V L) :=
  contMDiff_boundaryChartTest D (L.contDiff.comp (hV.comp signedLayerCoordinates.symm.contDiff))
    (waveComponent_compactSupport hVc L) ((inter_subset_inter_left _ (waveComponent_support L)).trans hSupp)

/-- The trial waves are genuine smooth native functions. Their two
scaled Laplacians have the collar residual bound everywhere on the
manifold, including off their common compact support. -/
theorem exists_native_finiteWave_laplace_bound
    {g : SmoothMetric N M} {p : M} (D : NativeBoundaryMetricChart g p)
    {U : Set Y} (hU : IsOpen U)
    (hFace : MapsTo (fun y : Y => signedLayerCoordinates (y,(0 : ℝ))) U D.ambient)
    (ξ : I n → ℝ) (hξ : ξ ≠ 0)
    {K : Set Y} (hK : IsCompact K) (hKU : K ⊆ U)
    (a : Y → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (η : ContDiffBump (0 : ℝ))
    (hRect : K ×ˢ Icc 0 η.rOut ⊆ signedLayerCoordinates ⁻¹' D.ambient) (M₀ : ℕ) :
    let B := boundaryLayerCoefficientsOfMetric D.open_ambient D.field D.smooth_field hFace ξ hξ
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      let V := B.finiteWave a η M₀ h
      let f := nativeWaveComponent D V Complex.reCLM
      let k := nativeWaveComponent D V Complex.imCLM
      ContMDiff J R ∞ f ∧ ContMDiff J R ∞ k ∧
        ∀ x : M,
          ‖(h : ℂ) ^ 2 * (⟨-nativeLaplace g f x, -nativeLaplace g k x⟩ : ℂ)‖ ≤
            C * h ^ (M₀ + 1) := by
  let B := boundaryLayerCoefficientsOfMetric D.open_ambient D.field D.smooth_field hFace ξ hξ
  obtain ⟨C,hC,hB⟩ := exists_signed_finiteWave_laplace_bound D.open_ambient D.field D.smooth_field
    D.normal_field hU hFace ξ hξ hK hKU a ha ha0 η hRect M₀
  refine ⟨C,hC,fun h hh hh1 => ?_⟩
  let V := B.finiteWave a η M₀ h
  have hV := B.finiteWave_contDiff hU hK.isClosed hKU a ha ha0 η η.contDiff M₀ h
  have hVc := B.finiteWave_hasCompactSupport hU hK a ha ha0 η η.hasCompactSupport M₀ h
  have hVS := B.finiteWave_tsupport_subset hU hK.isClosed a ha ha0 η M₀ h
  have hVRect (z : Z) (hz : z ∈ signedLayerCoordinates.symm ⁻¹' tsupport V ∩ inwardHalfSpace N) :
      signedLayerCoordinates.symm z ∈ K ×ˢ Icc 0 η.rOut := by
    have h := hVS hz.1
    have ht : (signedLayerCoordinates.symm z).2 = z 0 := by
      rw [← signedLayerCoordinates_height (signedLayerCoordinates.symm z), signedLayerCoordinates.apply_symm_apply]
    have ht' := h.2
    rw [η.tsupport_eq,Metric.mem_closedBall,Real.dist_eq,sub_zero] at ht'
    refine ⟨h.1,?_⟩
    rw [ht] at ht' ⊢
    exact ⟨mem_inwardHalfSpace.mp hz.2,(le_abs_self _).trans ht'⟩
  have hT : signedLayerCoordinates.symm ⁻¹' tsupport V ∩ inwardHalfSpace N ⊆ D.coord.target := by
    intro z hz
    rw [D.target_eq]
    have h := hRect (hVRect z hz)
    rw [mem_preimage,signedLayerCoordinates.apply_symm_apply] at h
    exact ⟨h,hz.2⟩
  refine ⟨nativeWaveComponent_contMDiff D hV hVc _ hT,nativeWaveComponent_contMDiff D hV hVc _ hT,fun x => ?_⟩
  by_cases hxI : x ∈ (J).interior M
  · by_cases hxS : x ∈ D.coord.symm '' (signedLayerCoordinates.symm ⁻¹' tsupport V ∩ inwardHalfSpace N)
    · obtain ⟨z,hz,rfl⟩ := hxS
      have hzT := hT hz
      have hX := D.coord.map_target hzT
      obtain ⟨⟨y,t⟩,rfl⟩ := signedLayerCoordinates.surjective z
      have hyT := hVRect _ hz
      rw [signedLayerCoordinates.symm_apply_apply] at hyT
      change ‖(h : ℂ) ^ 2 * (⟨
        -nativeLaplace g (nativeWaveComponent D V Complex.reCLM) _,
        -nativeLaplace g (nativeWaveComponent D V Complex.imCLM) _⟩ : ℂ)‖ ≤ _
      unfold nativeWaveComponent
      rw [D.nativeLaplace_boundaryChartTest (Complex.reCLM.contDiff.comp (hV.comp signedLayerCoordinates.symm.contDiff)) hX hxI,
        D.nativeLaplace_boundaryChartTest (Complex.imCLM.contDiff.comp (hV.comp signedLayerCoordinates.symm.contDiff)) hX hxI,
        D.coord.right_inv hzT]
      exact hB y hyT.1 t hyT.2 h hh hh1
    · have hz (L : ℂ →L[ℝ] ℝ) : nativeLaplace g (nativeWaveComponent D V L) x = 0 := by
        have hs : tsupport (nativeWaveComponent D V L) ⊆
            D.coord.symm '' (signedLayerCoordinates.symm ⁻¹' tsupport V ∩ inwardHalfSpace N) :=
          (tsupport_boundaryChartTest_subset D (waveComponent_compactSupport hVc L)
            ((inter_subset_inter_left _ (waveComponent_support L)).trans hT)).trans
              (image_mono (inter_subset_inter_left _ (waveComponent_support L)))
        exact image_eq_zero_of_notMem_tsupport (fun h =>
          hxS (hs (tsupport_nativeLaplace_subset g _ h)))
      change ‖(h : ℂ) ^ 2 * (⟨
        -nativeLaplace g (nativeWaveComponent D V Complex.reCLM) x,
        -nativeLaplace g (nativeWaveComponent D V Complex.imCLM) x⟩ : ℂ)‖ ≤ _
      rw [hz,hz]
      have hZero : (⟨-0,-0⟩ : ℂ) = 0 := by simp [Complex.ext_iff]
      simp only [hZero,mul_zero,norm_zero]
      positivity
  · have hZero : (⟨-0,-0⟩ : ℂ) = 0 := by simp [Complex.ext_iff]
    simp only [nativeLaplace,dite_eq_right hxI,hZero,mul_zero,norm_zero]
    positivity

end BoundaryLayer
end CalderonPatch

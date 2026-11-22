module

public import Proof.CalderonPatch.BoundaryChartTests
public import Proof.CalderonPatch.NormalChartFunctions
public import Proof.CalderonPatch.MeasuredPolarization
public import Proof.CalderonPatch.GlobalStationarity

import Proof.CalderonN.MetricCalculus

@[expose] public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN (I X chartVolume coordDeriv)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (𝓡∂ (m + 1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

local notation "N" => (m + 1)
local notation "J" => 𝓡∂ N
local notation "R" => 𝓘(ℝ, ℝ)
local notation "H" => inwardHalfSpace N

omit [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Outward unit-normal derivative times the induced Riemannian
surface density in the tangential coordinates. -/
def NativeBoundaryMetricChart.outwardConormalDensity
    {g : SmoothMetric N M} {p : M} (D : NativeBoundaryMetricChart g p) (u : M → ℝ)
    (z : X m) : ℝ :=
  -(chartVolume D.field (normalFacePoint z) * D.inwardDerivative u (normalFacePoint z))

private theorem normalFacePoint_mapsTo_of_closedBox {a b : I N → ℝ}
    (hBottom : a 0 = 0) (hb : 0 ≤ b 0) {U : Set (X N)}
    (hBox : MapsTo (WithLp.toLp 2) (Icc a b) U) :
    MapsTo normalFacePoint (WithLp.ofLp ⁻¹' Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0)) (U ∩ H) := by
  intro z hz
  have h := hBox (normalFacePoint_in_closedBox hBottom hb hz)
  change WithLp.toLp 2 (WithLp.ofLp (normalFacePoint z)) ∈ U at h
  rw [WithLp.toLp_ofLp] at h
  exact ⟨h, (mem_inwardHalfSpace).mpr (normalFacePoint_height z).ge⟩

private theorem tangentialBox_subset_closedBox (a b : I N → ℝ) :
    tangentialBox a b ⊆ WithLp.ofLp ⁻¹' Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0) :=
  fun _ h => ⟨fun i => (h i).1.le,fun i => (h i).2.le⟩

omit [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The density-valued conormal has a continuous representative on
the bottom face of the box. -/
theorem NativeBoundaryMetricChart.continuousOn_outwardConormalDensity
    {g : SmoothMetric N M} {p : M} (D : NativeBoundaryMetricChart g p)
    {a b : I N → ℝ} (hBottom : a 0 = 0) (hb : 0 ≤ b 0)
    {U : Set (X N)} (hU : IsOpen U) (hUD : U ⊆ D.ambient)
    (hBox : MapsTo (WithLp.toLp 2) (Icc a b) U)
    {u : M → ℝ} {v : X N → ℝ} (hv : ContDiffOn ℝ ∞ v U)
    (hA : EqOn (u ∘ D.coord.symm) v (U ∩ H)) :
    ContinuousOn (D.outwardConormalDensity u) (tangentialBox a b) := by
  have hFace := (normalFacePoint_mapsTo_of_closedBox hBottom hb hBox).mono_left
    (tangentialBox_subset_closedBox a b)
  have hDeriv := D.inwardDerivative_eq_coordDeriv hU hv hA
  have hA' := ((CalderonN.contDiffOn_metric_volume D.smooth_field).mono hUD).continuousOn
  have hB' := (CalderonN.contDiffOn_coordDeriv hv hU 0).continuousOn
  refine (((hA'.mul hB').neg).comp continuous_normalFacePoint.continuousOn
    (hFace.mono_right inter_subset_left)).congr ?_
  intro x hx
  change -(chartVolume D.field (normalFacePoint x) * D.inwardDerivative u (normalFacePoint x)) = _
  rw [hDeriv (hFace hx)]
  rfl

/-- A compactly supported signed extension of a tangential test
measures the outward conormal of a smooth harmonic function. -/
theorem integral_energyPairing_boundaryChartTest_eq_outwardConormal
    {g : SmoothMetric N M} {p : M} (D : NativeBoundaryMetricChart g p)
    (μ : Measure M) (hμ : IsMetricVolume g μ)
    {a b : I N → ℝ} (hab : a ≤ b) (hBottom : a 0 = 0)
    {U : Set (X N)} (hU : IsOpen U) (hUD : U ⊆ D.ambient)
    (hBox : MapsTo (WithLp.toLp 2) (Icc a b) U)
    {u : M → ℝ} (hu : ContMDiff J R ∞ u)
    (hH : EqOn (nativeLaplace g u) 0 ((J).interior M))
    {u₀ : X N → ℝ} (hu₀ : ContDiffOn ℝ ∞ u₀ U)
    (hA : EqOn (u ∘ D.coord.symm) u₀ (U ∩ H))
    {f : X N → ℝ} (hf : ContDiff ℝ ∞ f) (hfC : HasCompactSupport f)
    (hSupp : tsupport f ∩ H ⊆ normalHalfBox a b)
    {φ : X m → ℝ} (hTrace : f ∘ normalFacePoint = φ) :
    (∫ x, energyPairingDensity g u (boundaryChartTest D f) x ∂μ) =
      ∫ z in tangentialBox a b, φ z * D.outwardConormalDensity u z := by
  let v := boundaryChartTest D f
  have hDomain : U ∩ H ⊆ D.coord.target := by
    rw [D.target_eq]
    exact inter_subset_inter_left H hUD
  have hHalf : MapsTo (WithLp.toLp 2) (Icc a b) D.ambient := hBox.mono_right hUD
  have hTest : tsupport f ∩ H ⊆ D.coord.target := by
    intro x hx
    have h := hBox (normalHalfBox_subset_closedBox hBottom (hSupp hx))
    change WithLp.toLp 2 (WithLp.ofLp x) ∈ U at h
    rw [WithLp.toLp_ofLp] at h
    exact hDomain ⟨h,hx.2⟩
  have hv : ContMDiff J R ∞ v := contMDiff_boundaryChartTest D hf hfC hTest
  have hvA : EqOn (v ∘ D.coord.symm) f (U ∩ H) := (boundaryChartTest_comp_inverse D f).mono hDomain
  have hVs := tsupport_boundaryChartTest_subset_halfBox D hBottom hHalf hfC hSupp
  have hGreen := integral_nativeGreenPairing_normalHalfBox D μ hμ hab hBottom hU hUD hBox hu hv
    hu₀ hf.contDiffOn hA hvA hVs
  have hAE : ∀ᵐ x ∂μ, x ∈ (J).interior M := by
    rw [ae_iff]
    change μ (((J).interior M)ᶜ) = 0
    rw [(J).compl_interior]
    exact metricVolume_boundary_eq_zero g μ hμ
  let Q := Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0)
  let Q' := Set.pi univ (fun j : I m => Ioo ((a ∘ Fin.succAbove 0) j) ((b ∘ Fin.succAbove 0) j))
  let W (z : X m) := φ z * D.outwardConormalDensity u z
  have hT := normalFacePoint_mapsTo_of_closedBox hBottom (hBottom ▸ hab 0) hBox
  calc
    _ = ∫ x, v x * nativeLaplace g u x + energyPairingDensity g u v x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hAE] with x hx
      have h : nativeLaplace g u x = 0 := hH hx
      simp only [h,mul_zero,zero_add,v]
    _ = _ := hGreen
    _ = ∫ z in Q, W (WithLp.toLp 2 z) := by
      rw [← integral_neg]
      apply setIntegral_congr_fun measurableSet_Icc
      intro z hz
      let z' : X m := WithLp.toLp 2 z
      have hZ : z' ∈ WithLp.ofLp ⁻¹' Q := hz
      have hTrace' : f (normalFacePoint z') = φ z' := congrFun hTrace z'
      have hD := D.inwardDerivative_eq_coordDeriv hU hu₀ hA (hT hZ)
      change -(f (normalFacePoint z') *
        (chartVolume D.field (normalFacePoint z') * coordDeriv 0 u₀ (normalFacePoint z'))) = W z'
      rw [hTrace', ← hD]
      exact neg_mul_eq_mul_neg _ _
    _ = ∫ z in Q', W (WithLp.toLp 2 z) :=
      setIntegral_congr_set Measure.univ_pi_Ioo_ae_eq_Icc.symm
    _ = _ := by
      let l := MeasurableEquiv.toLp 2 (I m → ℝ)
      have he : l ⁻¹' tangentialBox a b = Q' := by
        ext z
        simp [tangentialBox,Q',Set.mem_pi,l]
      rw [← he]
      exact (PiLp.volume_preserving_toLp (I m)).setIntegral_preimage_emb l.measurableEmbedding W _

/-- Equality of the measured quadratic energy determines the same
outward conormal density in shared boundary coordinates. The input
potentials are smooth harmonic extensions of a common supported trace. -/
theorem outwardConormalDensity_eq_of_patchEnergy
    {g₁ g₂ : SmoothMetric N M} {μ₁ μ₂ : Measure M}
    (hμ₁ : IsMetricVolume g₁ μ₁) (hμ₂ : IsMetricVolume g₂ μ₂)
    {Γ : Set ((J).boundary M)} (hEnergy : PatchEnergyEqual g₁ g₂ μ₁ μ₂ Γ)
    {p₁ p₂ : M} (D₁ : NativeBoundaryMetricChart g₁ p₁) (D₂ : NativeBoundaryMetricChart g₂ p₂)
    {a b : I N → ℝ} (hab : a ≤ b) (hBottom : a 0 = 0) (hb : 0 < b 0)
    {U : Set (X N)} (hU : IsOpen U) (hUD₁ : U ⊆ D₁.ambient) (hUD₂ : U ⊆ D₂.ambient)
    (hBox : MapsTo (WithLp.toLp 2) (Icc a b) U)
    (hSame : EqOn D₁.coord.symm D₂.coord.symm (U ∩ {x | x 0 = 0}))
    (hΓ : MapsTo (D₁.coord.symm ∘ normalFacePoint) (tangentialBox a b) (Subtype.val '' Γ))
    {u₁ u₂ : M → ℝ} (hu₁ : ContMDiff J R ∞ u₁) (hu₂ : ContMDiff J R ∞ u₂)
    (hH₁ : EqOn (nativeLaplace g₁ u₁) 0 ((J).interior M))
    (hH₂ : EqOn (nativeLaplace g₂ u₂) 0 ((J).interior M))
    (hTrace : EqOn u₁ u₂ ((J).boundary M))
    (hSupp : tsupport (fun x : (J).boundary M => u₁ x) ⊆ Γ)
    {r₁ r₂ : X N → ℝ} (hr₁ : ContDiffOn ℝ ∞ r₁ U) (hr₂ : ContDiffOn ℝ ∞ r₂ U)
    (hR₁ : EqOn (u₁ ∘ D₁.coord.symm) r₁ (U ∩ H))
    (hR₂ : EqOn (u₂ ∘ D₂.coord.symm) r₂ (U ∩ H))
    (hSolve : ∀ v : M → ℝ, ContMDiff J R ∞ v →
      tsupport (fun p : (J).boundary M => v p) ⊆ Γ →
      ∃ w₁ w₂ : M → ℝ, ContMDiff J R ∞ w₁ ∧ ContMDiff J R ∞ w₂ ∧
        EqOn w₁ v ((J).boundary M) ∧ EqOn w₂ v ((J).boundary M) ∧
        EqOn (nativeLaplace g₁ w₁) 0 ((J).interior M) ∧
        EqOn (nativeLaplace g₂ w₂) 0 ((J).interior M)) :
    EqOn (D₁.outwardConormalDensity u₁) (D₂.outwardConormalDensity u₂) (tangentialBox a b) := by
  let S := tangentialBox a b
  have hS : IsOpen S := isOpen_tangentialBox a b
  have hc₁ := D₁.continuousOn_outwardConormalDensity hBottom hb.le hU hUD₁ hBox hr₁ hR₁
  have hc₂ := D₂.continuousOn_outwardConormalDensity hBottom hb.le hU hUD₂ hBox hr₂ hR₂
  refine eqOn_of_weighted_test_pairings hS Subset.rfl (ρ := fun _ => 1) continuousOn_const
    (fun _ _ => zero_lt_one) hc₁ hc₂ ?_
  intro φ hφ hφC hφS
  obtain ⟨f,hf,hfC,hfS,hfT⟩ := exists_halfBoxTest hb hφ hφC hφS
  have hK : tsupport f ∩ H ⊆ U ∩ H := by
    intro x hx
    have h := hBox (normalHalfBox_subset_closedBox hBottom (hfS hx))
    change WithLp.toLp 2 (WithLp.ofLp x) ∈ U at h
    rw [WithLp.toLp_ofLp] at h
    exact ⟨h,hx.2⟩
  have hT₁ : tsupport f ∩ H ⊆ D₁.coord.target := by
    rw [D₁.target_eq]
    exact hK.trans (inter_subset_inter_left H hUD₁)
  have hT₂ : tsupport f ∩ H ⊆ D₂.coord.target := by
    rw [D₂.target_eq]
    exact hK.trans (inter_subset_inter_left H hUD₂)
  let v₁ := boundaryChartTest D₁ f
  let v₂ := boundaryChartTest D₂ f
  have hv₁ : ContMDiff J R ∞ v₁ := contMDiff_boundaryChartTest D₁ hf hfC hT₁
  have hv₂ : ContMDiff J R ∞ v₂ := contMDiff_boundaryChartTest D₂ hf hfC hT₂
  have hV : EqOn v₁ v₂ ((J).boundary M) :=
    eqOn_boundaryChartTests_of_paired_coordinates D₁ D₂ hfC hT₁ hT₂
      (fun x hx => hSame ⟨(hK ⟨hx.1,(mem_inwardHalfSpace).mpr hx.2.ge⟩).1,hx.2⟩)
  have hs₁ := tsupport_boundaryChartTest_subset_halfBox D₁ hBottom (hBox.mono_right hUD₁) hfC hfS
  have hΓ₁ : tsupport (fun x : (J).boundary M => v₁ x) ⊆ Γ := by
    have hIncl : tsupport (fun x : (J).boundary M => v₁ x) ⊆ Subtype.val ⁻¹' tsupport v₁ := by
      apply closure_minimal _ ((isClosed_tsupport v₁).preimage continuous_subtype_val)
      intro x hx
      have hx' : (x : M) ∈ Function.support v₁ := hx
      exact subset_closure hx'
    apply hIncl.trans
    intro x hx
    have hxS : (x : M) ∈ tsupport v₁ := hx
    have hxD := hs₁ hxS
    let z := normalTangentialCoordinates (D₁.coord x)
    have hz : z ∈ S := by
      intro i
      have h := (show D₁.coord x ∈ normalHalfBox a b from hxD.2)
      exact ⟨h.2.2 _ (Fin.succAbove_ne _ _),h.2.1 _⟩
    have he := hΓ hz
    change D₁.coord.symm (normalFacePoint (normalTangentialCoordinates (D₁.coord x))) ∈ _ at he
    rw [normalFacePoint_tangentialCoordinates (D₁.coord_height_eq_zero hxD.1 x.property),
      D₁.coord.left_inv hxD.1] at he
    obtain ⟨y,hy,hyx⟩ := he
    exact (Subtype.ext hyx : y = x) ▸ hy
  obtain ⟨w₁,w₂,hw₁,hw₂,hwT₁,hwT₂,hwH₁,hwH₂⟩ := hSolve v₁ hv₁ hΓ₁
  have hI₁ (a b : M → ℝ) := integrable_energyPairingDensity g₁ μ₁ hμ₁ (u := a) (v := b)
  have hI₂ (a b : M → ℝ) := integrable_energyPairingDensity g₂ μ₂ hμ₂ (u := a) (v := b)
  have hSta₁ := isDirichletStationary_of_nativeHarmonic g₁ μ₁ hμ₁ hu₁ hH₁
  have hSta₂ := isDirichletStationary_of_nativeHarmonic g₂ μ₂ hμ₂ hu₂ hH₂
  have hwS₁ := isDirichletStationary_of_nativeHarmonic g₁ μ₁ hμ₁ hw₁ hwH₁
  have hwS₂ := isDirichletStationary_of_nativeHarmonic g₂ μ₂ hμ₂ hw₂ hwH₂
  have he := integral_energyPairing_eq_of_patchEnergy hEnergy hu₁ hu₂ hv₁ hv₂ hw₁ hw₂
    hTrace hwT₁ (hwT₂.trans hV) hV hSupp hΓ₁ hSta₁ hSta₂ hwS₁ hwS₂ hI₁ hI₂
  have h₁ := integral_energyPairing_boundaryChartTest_eq_outwardConormal D₁ μ₁ hμ₁
    hab hBottom hU hUD₁ hBox hu₁ hH₁ hr₁ hR₁ hf hfC hfS hfT
  have h₂ := integral_energyPairing_boundaryChartTest_eq_outwardConormal D₂ μ₂ hμ₂
    hab hBottom hU hUD₂ hBox hu₂ hH₂ hr₂ hR₂ hf hfC hfS hfT
  simp only [mul_one]
  exact h₁.symm.trans (he.trans h₂)

end CalderonPatch

module

public import Proof.CalderonPatch.BoundaryGreenBox
public import Proof.CalderonPatch.BoundaryVolume
public import Proof.CalderonPatch.ChartEnergyIntegral
public import Proof.CalderonPatch.NormalChartInterior

import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.MeasureTheory.Constructions.Pi

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X chartVolume coordDeriv divergenceFlux laplace)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (𝓡∂ (m + 1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

local notation "N" => (m + 1)
local notation "J" => 𝓡∂ N
local notation "R" => 𝓘(ℝ, ℝ)
local notation "H" => inwardHalfSpace N

/-- The part of a normal coordinate box that includes the measured
face and excludes the other faces. -/
@[expose] def normalHalfBox (a b : I N → ℝ) : Set (X N) :=
  {x | 0 ≤ x 0 ∧ (∀ i, x i < b i) ∧ ∀ i ≠ 0, a i < x i}

/-- For a test supported in a boundary normal half box, the integrated
native Green pairing is the outward conormal pairing on its bottom
face. The canonical native volume is the Euclidean metric density in
the chart. -/
theorem integral_nativeGreenPairing_normalHalfBox
    {g : SmoothMetric N M} {p : M} (D : NativeBoundaryMetricChart g p)
    (μ : Measure M) (hμ : IsMetricVolume g μ)
    {a b : I N → ℝ} (hab : a ≤ b) (hBottom : a 0 = 0)
    {U : Set (X N)} (hU : IsOpen U) (hUD : U ⊆ D.ambient)
    (hBox : MapsTo (WithLp.toLp 2) (Icc a b) U)
    {u v : M → ℝ} (hu : ContMDiff J R ∞ u) (hv : ContMDiff J R ∞ v)
    {u₀ v₀ : X N → ℝ} (hu₀ : ContDiffOn ℝ ∞ u₀ U) (hv₀ : ContDiffOn ℝ ∞ v₀ U)
    (hUA : EqOn (u ∘ D.coord.symm) u₀ (U ∩ H))
    (hVA : EqOn (v ∘ D.coord.symm) v₀ (U ∩ H))
    (hSupport : tsupport v ⊆ D.coord.source ∩ D.coord ⁻¹' normalHalfBox a b) :
    (∫ x, v x * nativeLaplace g u x + energyPairingDensity g u v x ∂μ) =
      -∫ z in Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0),
        v₀ (WithLp.toLp 2 (Fin.insertNth 0 0 z)) *
          (chartVolume D.field (WithLp.toLp 2 (Fin.insertNth 0 0 z)) *
            coordDeriv 0 u₀ (WithLp.toLp 2 (Fin.insertNth 0 0 z))) := by
  let B := Set.pi univ (fun i : I N => Ioo (a i) (b i))
  let l := MeasurableEquiv.toLp 2 (I N → ℝ)
  let V : Set (X N) := l.symm ⁻¹' B
  have hB : IsOpen B := isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo
  have hV : IsOpen V := hB.preimage (PiLp.continuous_ofLp 2 (fun _ : I N => ℝ))
  have hVU : V ⊆ U := by
    intro x hx
    have h := Set.mem_pi.mp hx
    have hb : l.symm x ∈ Icc a b :=
      ⟨fun i => (h i (mem_univ i)).1.le,fun i => (h i (mem_univ i)).2.le⟩
    have h := hBox hb
    change l (l.symm x) ∈ U at h
    rwa [l.apply_symm_apply] at h
  have hVPos : V ⊆ positiveHalfSpace N := by
    intro x hx
    have h := (Set.mem_pi.mp hx 0 (mem_univ 0)).1
    change a 0 < x 0 at h
    exact (mem_positiveHalfSpace).mpr (hBottom ▸ h)
  obtain ⟨e,het,heFun,heInv,heI,he,hes,hMetric⟩ := D.exists_interior_restriction hV (hVU.trans hUD)
  have heT : e.target = V := het.trans (inter_eq_left.mpr hVPos)
  have hUe : e.target ⊆ U ∩ H := by
    rw [heT]
    exact subset_inter hVU (hVPos.trans positiveHalfSpace_subset_inwardHalfSpace)
  have hUS : EqOn (u ∘ e.symm) u₀ e.target := by rw [heInv]; exact hUA.mono hUe
  have hVS : EqOn (v ∘ e.symm) v₀ e.target := by rw [heInv]; exact hVA.mono hUe
  have hS : tsupport v ∩ ((J).interior M) ⊆ e.source := by
    intro x hx
    have hxD := hSupport hx.1
    have hxPos := (D.interior_iff x hxD.1).mp hx.2
    have hxA : D.coord x ∈ normalHalfBox a b := hxD.2
    have hxV : D.coord x ∈ V := by
      apply Set.mem_pi.mpr
      intro i _
      change a i < D.coord x i ∧ D.coord x i < b i
      refine ⟨?_,hxA.2.1 i⟩
      by_cases hi : i = 0
      · subst i
        exact hBottom.symm ▸ (mem_positiveHalfSpace.mp hxPos)
      · exact hxA.2.2 i hi
    have hh := e.map_target (heT.symm ▸ hxV)
    rw [heInv, D.coord.left_inv hxD.1] at hh
    exact hh
  have hAE : ∀ᵐ x ∂μ, x ∈ (J).interior M := by
    rw [ae_iff]
    change μ (((J).interior M)ᶜ) = 0
    rw [(J).compl_interior]
    exact metricVolume_boundary_eq_zero g μ hμ
  let F (x : X N) := v₀ x * (chartVolume D.field x * laplace D.field u₀ x) +
    ∑ i : I N, coordDeriv i v₀ x * divergenceFlux D.field u₀ x i
  have hInt :
      (∫ x, v x * nativeLaplace g u x + energyPairingDensity g u v x ∂μ) =
        ∫ y in Icc a b, F (WithLp.toLp 2 y) := by
    calc
      _ = ∫ x in e.source, v x * nativeLaplace g u x + energyPairingDensity g u v x ∂μ := by
        rw [← integral_indicator e.open_source.measurableSet]
        apply integral_congr_ae
        filter_upwards [hAE] with x hxI
        by_cases hx : x ∈ e.source
        · rw [indicator_of_mem hx]
        · have hSupp : x ∉ tsupport v := fun h => hx (hS ⟨h,hxI⟩)
          rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hSupp, zero_mul,
            energyPairingDensity_eq_zero_off_tsupport g u v hSupp, zero_add]
      _ = ∫ x in e.target, F x :=
        integral_nativeGreenPairing_in_coordinates g μ hμ e heI he hes hu.contMDiffOn
          hv.contMDiffOn hMetric hUS hVS
      _ = ∫ x in V, F x := by rw [heT]
      _ = ∫ y in B, F (WithLp.toLp 2 y) := by
        have hV' : l '' B = V := l.toEquiv.image_eq_preimage_symm B
        rw [← hV']
        exact (PiLp.volume_preserving_toLp (I N)).setIntegral_image_emb l.measurableEmbedding F B
      _ = _ := setIntegral_congr_set Measure.univ_pi_Ioo_ae_eq_Icc
  have hZero {y : I N → ℝ} (hy : y ∈ Icc a b) (hSide : l y ∉ normalHalfBox a b) :
      v₀ (l y) = 0 := by
    have hyH : l y ∈ H := (mem_inwardHalfSpace).mpr (hBottom ▸ hy.1 0)
    have hyT : l y ∈ D.coord.target := D.target_eq.symm ▸ ⟨hUD (hBox hy),hyH⟩
    have hz := hVA (show l y ∈ U ∩ H from ⟨hBox hy,hyH⟩)
    have hNot : D.coord.symm (l y) ∉ tsupport v := by
      intro h
      have hs : D.coord (D.coord.symm (l y)) ∈ normalHalfBox a b := (hSupport h).2
      rw [D.coord.right_inv hyT] at hs
      exact hSide hs
    change v (D.coord.symm (l y)) = v₀ (l y) at hz
    exact hz.symm.trans (image_eq_zero_of_notMem_tsupport hNot)
  have hTop (i : I N) : EqOn
      (fun z => v₀ (WithLp.toLp 2 (Fin.insertNth i (b i) z))) 0
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) := by
    intro z hz
    apply hZero (insertNth_mem_box i ⟨hab i,le_rfl⟩ hz)
    intro h
    have hx := h.2.1 i
    change Fin.insertNth (α := fun _ : I N => ℝ) i (b i) z i < b i at hx
    simp at hx
  have hSide (i : I N) (hi : i ≠ 0) : EqOn
      (fun z => v₀ (WithLp.toLp 2 (Fin.insertNth i (a i) z))) 0
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) := by
    intro z hz
    apply hZero (insertNth_mem_box i ⟨le_rfl,hab i⟩ hz)
    intro h
    have hx := h.2.2 i hi
    change a i < Fin.insertNth (α := fun _ : I N => ℝ) i (a i) z i at hx
    simp at hx
  rw [hInt]
  exact greenIdentity_normalBox hab hBottom hU hBox
    ⟨fun i j => (D.smooth_field.1 i j).mono hUD,fun x hx => D.smooth_field.2 x (hUD hx)⟩
    (fun x hx => D.normal_field x (hUD hx)) hu₀ hv₀ hTop hSide

end CalderonPatch

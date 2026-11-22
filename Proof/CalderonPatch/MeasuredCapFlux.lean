module

public import Proof.CalderonPatch.BoundaryFluxPairing
public import Proof.CalderonPatch.CapTraceCutoff

import Proof.CalderonPatch.DirichletHilbert
import Proof.CalderonPatch.GaugeFromCauchy
import Mathlib.Tactic

public section
noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN (I X)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

local notation "N" => (n+1)
local notation "J" => 𝓡∂ N
local notation "R" => 𝓘(ℝ, ℝ)
local notation "H" => inwardHalfSpace N

omit [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
private theorem energyPairingDensity_capTraceCutoff (g : SmoothMetric N M)
    {u : M → ℝ} (hu : ContMDiff J R ∞ u) (ε : ℝ) (p : M) :
    energyPairingDensity g u (capTraceCutoff ε ∘ u) p =
      deriv (capTraceCutoff ε) (u p) * energyPairingDensity g u u p := by
  let A : TangentSpace J p →L[ℝ] ℝ := mfderiv J R u p
  let B : TangentSpace J p →L[ℝ] ℝ := mfderiv J R (capTraceCutoff ε ∘ u) p
  have hd : B = deriv (capTraceCutoff ε) (u p) • A := by
    change mfderiv J R (capTraceCutoff ε ∘ u) p = _
    rw [mfderiv_comp p ((capTraceCutoff_contDiff ε).contMDiff.mdifferentiableAt (by simp))
      (hu.mdifferentiableAt (by simp)),mfderiv_eq_fderiv]
    ext v
    change fderiv ℝ (capTraceCutoff ε) (u p) (A v) = deriv (capTraceCutoff ε) (u p) * A v
    calc
      _ = fderiv ℝ (capTraceCutoff ε) (u p) (A v • (1 : ℝ)) := by rw [smul_eq_mul,mul_one]
      _ = A v * deriv (capTraceCutoff ε) (u p) := by rw [map_smul,smul_eq_mul,deriv]
      _ = _ := mul_comm _ _
  rw [energyPairingDensity_symm g u (capTraceCutoff ε ∘ u)]
  change g.inner p (metricDual g p B) (metricDual g p A) =
    deriv (capTraceCutoff ε) (u p) * g.inner p (metricDual g p A) (metricDual g p A)
  rw [metricDual_spec,metricDual_spec,hd]
  rfl

omit [T2Space M] [CompactSpace M] [IsManifold J ∞ M] [MeasurableSpace M] [BorelSpace M] in
private theorem tsupport_truncated_sub_trace_subset {u v : M → ℝ}
    {Γ : Set ((J).boundary M)} (hu : tsupport (fun p : (J).boundary M => u p) ⊆ Γ)
    (hv : tsupport (fun p : (J).boundary M => v p) ⊆ Γ) {ε : ℝ} (hε : 0 < ε) :
    tsupport (fun p : (J).boundary M => capTraceCutoff ε (u p-v p)) ⊆ Γ := by
  apply (closure_minimal _ ((isClosed_tsupport (fun p : (J).boundary M => u p)).union
    (isClosed_tsupport (fun p : (J).boundary M => v p)))).trans (union_subset hu hv)
  intro p hp
  by_contra hn
  have h0 : capTraceCutoff ε 0 = 0 :=
    capTraceCutoff_zero_of_abs_le hε (by simpa using hε.le)
  have hUp : u p = 0 := image_eq_zero_of_notMem_tsupport
    (f := fun q : (J).boundary M => u q) (x := p) (fun h => hn (Or.inl h))
  have hVp : v p = 0 := image_eq_zero_of_notMem_tsupport
    (f := fun q : (J).boundary M => v q) (x := p) (fun h => hn (Or.inr h))
  change capTraceCutoff ε (u p-v p) ≠ 0 at hp
  rw [hUp,hVp,sub_zero,h0] at hp
  exact hp rfl

/-- The measured energy controls the sign of the difference of the
outward conormal pairings. Each test has the same boundary trace, namely
the smooth truncation of the difference of the solution traces. -/
theorem integral_sub_outwardConormal_nonneg_of_patchEnergy
    {g₁ g₂ : SmoothMetric N M} {μ₁ μ₂ : Measure M}
    (hμ₁ : IsMetricVolume g₁ μ₁) (hμ₂ : IsMetricVolume g₂ μ₂)
    {Γ : Set ((J).boundary M)} (hEnergy : PatchEnergyEqual g₁ g₂ μ₁ μ₂ Γ)
    {p₁ p₂ : M} (A₁ : NativeBoundaryMetricChart g₁ p₁) (A₂ : NativeBoundaryMetricChart g₂ p₂)
    {a b : I N → ℝ} (hab : a ≤ b) (hBottom : a 0 = 0)
    {U : Set (X N)} (hU : IsOpen U) (hUA₁ : U ⊆ A₁.ambient) (hUA₂ : U ⊆ A₂.ambient)
    (hBox : MapsTo (WithLp.toLp 2) (Icc a b) U)
    {u₁ u₂ : M → ℝ} (hu₁ : ContMDiff J R ∞ u₁) (hu₂ : ContMDiff J R ∞ u₂)
    (hH₁ : EqOn (nativeLaplace g₁ u₁) 0 ((J).interior M))
    (hH₂ : EqOn (nativeLaplace g₂ u₂) 0 ((J).interior M))
    (hs₁ : tsupport (fun p : (J).boundary M => u₁ p) ⊆ Γ)
    (hs₂ : tsupport (fun p : (J).boundary M => u₂ p) ⊆ Γ)
    {r₁ r₂ : X N → ℝ} (hr₁ : ContDiffOn ℝ ∞ r₁ U) (hr₂ : ContDiffOn ℝ ∞ r₂ U)
    (hR₁ : EqOn (u₁ ∘ A₁.coord.symm) r₁ (U ∩ H))
    (hR₂ : EqOn (u₂ ∘ A₂.coord.symm) r₂ (U ∩ H))
    {ε : ℝ} (hε : 0 < ε)
    {f : X N → ℝ} (hf : ContDiff ℝ ∞ f) (hfC : HasCompactSupport f)
    (hfS : tsupport f ∩ H ⊆ normalHalfBox a b)
    {φ : X n → ℝ} (hfT : f ∘ normalFacePoint = φ)
    (hTrace₁ : EqOn (boundaryChartTest A₁ f) (capTraceCutoff ε ∘ (u₁ - u₂)) ((J).boundary M))
    (hTrace₂ : EqOn (boundaryChartTest A₂ f) (capTraceCutoff ε ∘ (u₁ - u₂)) ((J).boundary M))
    (hSolve₁ : ∀ v : M → ℝ, ContMDiff J R ∞ v →
      ∃ w : M → ℝ, ContMDiff J R ∞ w ∧ EqOn w v ((J).boundary M) ∧
        EqOn (nativeLaplace g₁ w) 0 ((J).interior M))
    (hSolve₂ : ∀ v : M → ℝ, ContMDiff J R ∞ v →
      ∃ w : M → ℝ, ContMDiff J R ∞ w ∧ EqOn w v ((J).boundary M) ∧
        EqOn (nativeLaplace g₂ w) 0 ((J).interior M)) :
    0 ≤ ∫ z in tangentialBox a b,
      φ z * (A₁.outwardConormalDensity u₁ z - A₂.outwardConormalDensity u₂ z) := by
  let t₁ := boundaryChartTest A₁ f
  let t₂ := boundaryChartTest A₂ f
  have hK : tsupport f ∩ H ⊆ U ∩ H := by
    intro x hx
    have he := hBox (normalHalfBox_subset_closedBox hBottom (hfS hx))
    change WithLp.toLp 2 (WithLp.ofLp x) ∈ U at he
    rw [WithLp.toLp_ofLp] at he
    exact ⟨he,hx.2⟩
  have ht₁ : ContMDiff J R ∞ t₁ :=
    contMDiff_boundaryChartTest A₁ hf hfC (hK.trans (A₁.target_eq.symm ▸
      inter_subset_inter_left H hUA₁))
  have ht₂ : ContMDiff J R ∞ t₂ :=
    contMDiff_boundaryChartTest A₂ hf hfC (hK.trans (A₂.target_eq.symm ▸
      inter_subset_inter_left H hUA₂))
  have hTest : EqOn t₁ t₂ ((J).boundary M) := hTrace₁.trans hTrace₂.symm
  have hSup : tsupport (fun p : (J).boundary M => t₁ p) ⊆ Γ := by
    have he : (fun p : (J).boundary M => t₁ p) =
        fun p : (J).boundary M => capTraceCutoff ε (u₁ p - u₂ p) :=
      funext fun p => hTrace₁ p.property
    rw [he]
    exact tsupport_truncated_sub_trace_subset hs₁ hs₂ hε
  obtain ⟨v,hv,hvTrace,hvH⟩ := hSolve₁ u₂ hu₂
  obtain ⟨w₁,hw₁,hwT₁,hwH₁⟩ := hSolve₁ t₁ ht₁
  obtain ⟨w₂,hw₂,hwT₂,hwH₂⟩ := hSolve₂ t₂ ht₂
  let r := u₁ - v
  have hr : ContMDiff J R ∞ r := hu₁.sub hv
  have hrH : EqOn (nativeLaplace g₁ r) 0 ((J).interior M) := by
    intro p hp
    have hp₁ : nativeLaplace g₁ u₁ p = 0 := hH₁ hp
    have hp₂ : nativeLaplace g₁ v p = 0 := hvH hp
    change nativeLaplace g₁ (fun y => u₁ y - v y) p = 0
    rw [nativeLaplace_sub g₁ hu₁ hv hp,hp₁,hp₂,sub_zero]
  have hTrunc : EqOn t₁ (capTraceCutoff ε ∘ r) ((J).boundary M) := by
    intro p hp
    change boundaryChartTest A₁ f p = _
    rw [hTrace₁ hp]
    change capTraceCutoff ε (u₁ p - u₂ p) = capTraceCutoff ε (u₁ p - v p)
    rw [hvTrace hp]
  have hvS : tsupport (fun p : (J).boundary M => v p) ⊆ Γ := by
    rw [show (fun p : (J).boundary M => v p) = fun p : (J).boundary M => u₂ p
      from funext fun p => hvTrace p.property]
    exact hs₂
  have hI₁ (a b : M → ℝ) := integrable_energyPairingDensity g₁ μ₁ hμ₁ (u := a) (v := b)
  have hI₂ (a b : M → ℝ) := integrable_energyPairingDensity g₂ μ₂ hμ₂ (u := a) (v := b)
  have hP := integral_energyPairing_eq_of_patchEnergy hEnergy hv hu₂ ht₁ ht₂ hw₁ hw₂ hvTrace
    hwT₁ hwT₂ hTest hvS hSup
    (isDirichletStationary_of_nativeHarmonic g₁ μ₁ hμ₁ hv hvH)
    (isDirichletStationary_of_nativeHarmonic g₂ μ₂ hμ₂ hu₂ hH₂)
    (isDirichletStationary_of_nativeHarmonic g₁ μ₁ hμ₁ hw₁ hwH₁)
    (isDirichletStationary_of_nativeHarmonic g₂ μ₂ hμ₂ hw₂ hwH₂) hI₁ hI₂
  have hStat := isDirichletStationary_of_nativeHarmonic g₁ μ₁ hμ₁ hr hrH
  have hNonneg : 0 ≤ ∫ x, energyPairingDensity g₁ r t₁ x ∂μ₁ := by
    rw [hStat.integral_eq_of_same_trace hr ht₁ ((capTraceCutoff_contDiff ε).contMDiff.comp hr)
      hTrunc hI₁]
    exact integral_nonneg fun x => by
      rw [energyPairingDensity_capTraceCutoff g₁ hr ε x,energyPairingDensity_self]
      exact mul_nonneg (capTraceCutoff_deriv_nonneg ε _) (covectorEnergy_nonneg g₁ x _)
  have hsum : u₁ = v + r := by
    funext x
    change u₁ x = v x + (u₁ x - v x)
    ring
  have hE : (∫ x, energyPairingDensity g₁ u₁ t₁ x ∂μ₁) =
      (∫ x, energyPairingDensity g₂ u₂ t₂ x ∂μ₂) + ∫ x, energyPairingDensity g₁ r t₁ x ∂μ₁ := by
    rw [hsum,show energyPairingDensity g₁ (v+r) t₁ =
        (fun x => energyPairingDensity g₁ v t₁ x + energyPairingDensity g₁ r t₁ x) from
      funext (energyPairingDensity_add_left g₁ hv hr t₁)]
    exact (integral_add (hI₁ v t₁ hv ht₁) (hI₁ r t₁ hr ht₁)).trans (congrArg (· + _) hP)
  have hFace₁ := integral_energyPairing_boundaryChartTest_eq_outwardConormal A₁ μ₁ hμ₁
    hab hBottom hU hUA₁ hBox hu₁ hH₁ hr₁ hR₁ hf hfC hfS hfT
  have hFace₂ := integral_energyPairing_boundaryChartTest_eq_outwardConormal A₂ μ₂ hμ₂
    hab hBottom hU hUA₂ hBox hu₂ hH₂ hr₂ hR₂ hf hfC hfS hfT
  let W := tangentialBox a b
  let Q : Set (X n) := WithLp.ofLp ⁻¹' Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0)
  have hWQ : W ⊆ Q := fun _ hz => ⟨fun i => (hz i).1.le,fun i => (hz i).2.le⟩
  have hQc : IsCompact Q :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I n => ℝ)).toHomeomorph.isClosedEmbedding.isCompact_preimage isCompact_Icc
  have hFaceMap : MapsTo normalFacePoint Q (U ∩ H) := by
    intro z hz
    have hZ := hBox (normalFacePoint_in_closedBox hBottom (hBottom ▸ hab 0) hz)
    exact ⟨by simpa using hZ,(mem_inwardHalfSpace).mpr (normalFacePoint_height z).ge⟩
  have hJ (g : SmoothMetric N M) {p : M} (A : NativeBoundaryMetricChart g p)
      (hUA : U ⊆ A.ambient) {u : M → ℝ} {r : X N → ℝ}
      (hr : ContDiffOn ℝ ∞ r U) (hR : EqOn (u ∘ A.coord.symm) r (U ∩ H)) :
      IntegrableOn (fun z => φ z * A.outwardConormalDensity u z) W := by
    have hCρ := ((CalderonN.contDiffOn_metric_volume A.smooth_field).mono hUA).continuousOn
    have hCDr := (CalderonN.contDiffOn_coordDeriv hr hU 0).continuousOn
    have hCon : ContinuousOn (A.outwardConormalDensity u) Q := by
      refine ((hCρ.mul hCDr).neg.comp continuous_normalFacePoint.continuousOn
        (hFaceMap.mono_right inter_subset_left)).congr ?_
      intro z hz
      change A.outwardConormalDensity u z =
        -(CalderonN.chartVolume A.field (normalFacePoint z) * CalderonN.coordDeriv 0 r (normalFacePoint z))
      rw [NativeBoundaryMetricChart.outwardConormalDensity,
        A.inwardDerivative_eq_coordDeriv hU hr hR (hFaceMap hz)]
    have hφ : Continuous φ := hfT ▸ hf.continuous.comp continuous_normalFacePoint
    exact ((hφ.continuousOn.mul hCon).integrableOn_compact hQc).mono_set hWQ
  rw [show (fun z => φ z * (A₁.outwardConormalDensity u₁ z - A₂.outwardConormalDensity u₂ z)) =
      (fun z => φ z * A₁.outwardConormalDensity u₁ z - φ z * A₂.outwardConormalDensity u₂ z) by
    funext z
    exact mul_sub _ _ _,
    integral_sub (hJ _ A₁ hUA₁ hr₁ hR₁) (hJ _ A₂ hUA₂ hr₂ hR₂),
    ← hFace₁,← hFace₂,hE,add_sub_cancel_left]
  exact hNonneg

end CalderonPatch

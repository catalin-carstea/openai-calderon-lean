module

public import Proof.CalderonPatch.EnergyIntegrable

import Proof.CalderonPatch.SmoothNativeLaplace
import Proof.CalderonPatch.MetricVolumeFinite
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Algebra.Structures

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold BigOperators

namespace CalderonPatch

open CalderonN (X)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "R" => 𝓘(ℝ, ℝ)

private theorem energyPairingDensity_finsetSum_right
    (g : SmoothMetric n M) (u : M → ℝ) {ι : Type*} (s : Finset ι) (v : ι → M → ℝ)
    (hv : ∀ i, ContMDiff J R ∞ (v i)) (x : M) :
    energyPairingDensity g u (∑ i ∈ s, v i) x = ∑ i ∈ s, energyPairingDensity g u (v i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty,Finset.sum_empty]
    apply energyPairingDensity_eq_zero_off_tsupport
    simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi,
      energyPairingDensity_add_right g u (hv i) (contMDiff_finsetSum' fun j _ => hv j),ih]

variable {m : ℕ} {P : Type*} [TopologicalSpace P] [T2Space P] [CompactSpace P]
  [MeasurableSpace P] [BorelSpace P]
  [ChartedSpace (EuclideanHalfSpace (m + 1)) P] [IsManifold (𝓡∂ (m + 1)) ∞ P]

local notation "Jp" => 𝓡∂ (m + 1)

theorem integrable_mul_nativeLaplace
    (g : SmoothMetric (m + 1) P) (μ : Measure P) (hμ : IsMetricVolume g μ)
    {u v : P → ℝ} (hu : ContMDiff Jp R ∞ u) (hv : ContMDiff Jp R ∞ v) :
    Integrable (fun x => v x * nativeLaplace g u x) μ := by
  let : IsFiniteMeasure μ := hμ.isFiniteMeasure
  obtain ⟨L,hL,hEq⟩ := exists_smooth_nativeLaplace g hu
  have hI : ∀ᵐ x ∂μ, x ∈ (Jp).interior P := by
    rw [ae_iff]
    change μ (((Jp).interior P)ᶜ) = 0
    rw [(Jp).compl_interior]
    exact metricVolume_boundary_eq_zero g μ hμ
  have hL₁ : Integrable (fun x => v x * L x) μ :=
    integrableOn_univ.mp ((hv.continuous.mul hL.continuous).continuousOn.integrableOn_compact
      isCompact_univ)
  exact hL₁.congr (hI.mono fun x hx => congrArg (v x * ·) (hEq hx))

/-- Global integration by parts against a smooth zero-trace variation.
A finite partition of unity reduces it to the native interior and
half-box Green identities. -/
theorem integral_nativeGreenPairing_zeroTrace
    (g : SmoothMetric (m + 1) P) (μ : Measure P) (hμ : IsMetricVolume g μ)
    {u v : P → ℝ} (hu : ContMDiff Jp R ∞ u) (hv : ContMDiff Jp R ∞ v)
    (hTrace : EqOn v 0 ((Jp).boundary P)) :
    (∫ x, v x * nativeLaplace g u x + energyPairingDensity g u v x ∂μ) = 0 := by
  classical
  choose U hUo hUp hGreen using exists_neighborhood_zeroTrace_greenPairing g μ hμ
  have hCover : (univ : Set P) ⊆ ⋃ p, U p := fun p _ => mem_iUnion.mpr ⟨p,hUp p⟩
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U hUo hCover
  let O (i : s) := U i
  have hO : (univ : Set P) ⊆ ⋃ i : s, O i := by
    intro x hx
    obtain ⟨i,hi,hxU⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,hxU⟩
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := Jp)
    isClosed_univ O (fun i => hUo i) hO
  let w (i : s) : P → ℝ := (ρ i : P → ℝ) * v
  have hw (i : s) : ContMDiff Jp R ∞ (w i) := (ρ i).contMDiff.mul hv
  have hWZ (i : s) : EqOn (w i) 0 ((Jp).boundary P) := by
    intro p hp
    change ρ i p * v p = 0
    have h : v p = 0 := hTrace hp
    rw [h,mul_zero]
  have hWs (i : s) : tsupport (w i) ⊆ U i := tsupport_mul_subset_left.trans (hρ i)
  let F (i : s) (x : P) := w i x * nativeLaplace g u x + energyPairingDensity g u (w i) x
  have hz (i : s) : (∫ x, F i x ∂μ) = 0 := by
    exact hGreen i u (w i) hu (hw i) (hWZ i) (hWs i)
  have hDecomp : v = ∑ i : s, w i := by
    funext x
    have hOne : ∑ i : s, ρ i x = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
    rw [Finset.sum_apply]
    change v x = ∑ i : s, ρ i x * v x
    rw [← Finset.sum_mul,hOne,one_mul]
  have hF (x : P) : (∑ i : s, w i) x * nativeLaplace g u x +
      energyPairingDensity g u (∑ i : s, w i) x = ∑ i : s, F i x := by
    rw [energyPairingDensity_finsetSum_right g u _ w hw, Finset.sum_apply, Finset.sum_mul]
    exact (Finset.sum_add_distrib).symm
  calc
    _ = ∫ x, (∑ i : s, w i) x * nativeLaplace g u x +
        energyPairingDensity g u (∑ i : s, w i) x ∂μ := by rw [← hDecomp]
    _ = ∫ x, ∑ i : s, F i x ∂μ := integral_congr_ae (Eventually.of_forall hF)
    _ = ∑ i : s, ∫ x, F i x ∂μ := integral_finsetSum _ (fun i _ =>
      (integrable_mul_nativeLaplace g μ hμ hu (hw i)).add
        (integrable_energyPairingDensity g μ hμ hu (hw i)))
    _ = 0 := Finset.sum_eq_zero fun i _ => hz i

/-- The actual Dirichlet energy tests the positive operator `−Δ_g`
against smooth zero-trace functions. -/
theorem integral_energyPairingDensity_eq_neg_laplace
    (g : SmoothMetric (m + 1) P) (μ : Measure P) (hμ : IsMetricVolume g μ)
    {u v : P → ℝ} (hu : ContMDiff Jp R ∞ u) (hv : ContMDiff Jp R ∞ v)
    (hTrace : EqOn v 0 ((Jp).boundary P)) :
    (∫ x, energyPairingDensity g u v x ∂μ) = ∫ x, (-nativeLaplace g u x) * v x ∂μ := by
  have h := integral_nativeGreenPairing_zeroTrace g μ hμ hu hv hTrace
  rw [integral_add (integrable_mul_nativeLaplace g μ hμ hu hv)
    (integrable_energyPairingDensity g μ hμ hu hv)] at h
  rw [show (fun x => (-nativeLaplace g u x) * v x) =
      (fun x => -(v x * nativeLaplace g u x)) from funext (fun _ => by ring),integral_neg]
  exact eq_neg_of_add_eq_zero_right h

/-- A smooth function whose native Laplacian vanishes in the interior
is stationary for the Dirichlet energy. -/
theorem isDirichletStationary_of_nativeHarmonic
    (g : SmoothMetric (m + 1) P) (μ : Measure P) (hμ : IsMetricVolume g μ)
    {u : P → ℝ} (hu : ContMDiff Jp R ∞ u)
    (hH : EqOn (nativeLaplace g u) 0 ((Jp).interior P)) :
    IsDirichletStationary g μ u := by
  intro v hv hTrace
  have hLap : nativeLaplace g u = 0 := by
    funext x
    by_cases hx : x ∈ (Jp).interior P
    · exact hH hx
    · unfold nativeLaplace
      exact dite_eq_right hx
  rw [integral_energyPairingDensity_eq_neg_laplace g μ hμ hu hv hTrace,hLap]
  simp only [Pi.zero_apply,neg_zero,zero_mul,integral_zero]

end CalderonPatch

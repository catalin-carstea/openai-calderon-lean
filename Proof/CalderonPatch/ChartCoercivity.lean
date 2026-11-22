module

public import Proof.CalderonPatch.EnergyIntegrable
public import Proof.CalderonPatch.MetricVolumeFinite

import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.CompactEllipticity
import Proof.CalderonN.GreenRestriction
import Proof.CalderonN.MetricCalculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic.Ring

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold RealInnerProductSpace

namespace CalderonPatch

open CalderonN (I X Mat MetricField axis chartVolume coordDeriv divergenceCoeff divergenceFlux)

private theorem norm_sq_dual_eq_sum_axis {n : ℕ} (A : X n →L[ℝ] ℝ) :
    ‖A‖^2 = ∑ i : I n, (A (axis i))^2 := by
  let v := (InnerProductSpace.toDual ℝ (X n)).symm A
  have hNorm : ‖v‖ = ‖A‖ := (InnerProductSpace.toDual ℝ (X n)).symm.norm_map A
  have hAxis (i : I n) : v i = A (axis i) := by
    have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := axis i) (y := A)
    rw [axis,EuclideanSpace.inner_single_right,one_mul] at h
    change (star (v i) : ℝ) = A (axis i) at h
    simpa only [star_trivial] using h
  rw [← hNorm,EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_congr rfl (fun i _ => congrArg (· ^ 2) (hAxis i))

variable {n : ℕ} [NeZero n]

/-- On a compact coordinate set the Riemannian density is bounded
above and its divergence-form energy is uniformly elliptic. -/
theorem exists_chart_coercivity {Ω C : Set (X n)} {γ : MetricField n}
    (hγ : CalderonN.SmoothMetric Ω γ) (hC : IsCompact C) (hCΩ : C ⊆ Ω) :
    ∃ L R : ℝ, 0 < L ∧ 0 < R ∧
      (∀ x ∈ C, chartVolume γ x ≤ R) ∧
      ∀ x ∈ C, ∀ u : X n → ℝ, L * ‖fderiv ℝ u x‖^2 ≤
        ∑ i : I n, coordDeriv i u x * divergenceFlux γ u x i := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let a (i j : I n) (x : C) := divergenceCoeff γ x i j
  have hA (i j : I n) : Continuous (a i j) := continuousOn_iff_continuous_domRestrict.mp
    (((CalderonN.contDiffOn_divergenceCoeff hγ i j).continuousOn).mono hCΩ)
  have hPos (x : C) (_ : x ∈ (univ : Set C)) : Matrix.PosDef (fun i j => a i j x : Mat n) :=
    CalderonN.divergenceMatrix_posDef γ x (hγ.2 x (hCΩ x.2))
  obtain ⟨L,hL,hBound⟩ := CalderonN.Elliptic.lower_ellipticity_on_compact
    hA isCompact_univ hPos
  have hρC : ContinuousOn (chartVolume γ) C :=
    (CalderonN.continuousOn_metricVolumeDensity hγ).mono hCΩ
  obtain ⟨R,hR⟩ := ((hC.image_of_continuousOn hρC).bddAbove : BddAbove (chartVolume γ '' C))
  refine ⟨L,max 1 R,hL,lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun x hx => (hR (mem_image_of_mem _ hx)).trans (le_max_right _ _),?_⟩
  intro x hx u
  have h := hBound ⟨x,hx⟩ (mem_univ _) (fun i => coordDeriv i u x)
  rw [norm_sq_dual_eq_sum_axis]
  change L * (∑ i, coordDeriv i u x ^ 2) ≤ _
  simp only [a,divergenceFlux,Finset.mul_sum,mul_assoc] at h ⊢
  exact h

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (𝓡∂ (m + 1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

local notation "N" => (m + 1)
local notation "J" => 𝓡∂ N
local notation "K" => 𝓘(ℝ, X N)
local notation "R" => 𝓘(ℝ, ℝ)

/-- Import the Euclidean squared integral and export the squared
differential bound using the true native metric energy. The compact
set may contain a null boundary outside the open chart target. -/
theorem exists_native_chart_energy_comparison
    (g : SmoothMetric N M) (μ : Measure M) (hμ : IsMetricVolume g μ)
    (e : OpenPartialHomeomorph M (X N)) (heI : e.source ⊆ (J).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    {C Ω : Set (X N)} (hC : IsCompact C) (hCΩ : C ⊆ Ω)
    (heC : e.target ⊆ C) (hAE : e.target =ᵐ[volume] C)
    {γ : MetricField N} (hγ : CalderonN.SmoothMetric Ω γ)
    (hMetric : EqOn (coordinateMetric g e) γ e.target) :
    ∃ L B : ℝ, 0 < L ∧ 0 < B ∧
      ∀ {u : M → ℝ} {v : X N → ℝ},
        ContMDiff J R ∞ u → ContDiff ℝ ∞ v → EqOn (u ∘ e.symm) v e.target →
        (∀ c : ℝ, (∫ p in e.source, (u p - c)^2 ∂μ) ≤
          B * ∫ x in C, (v x - c)^2) ∧
        L * (∫ x in C, ‖fderiv ℝ v x‖^2) ≤ ∫ p, energyPairingDensity g u u p ∂μ := by
  obtain ⟨L,B,hL,hB,hρ,hCoercive⟩ := exists_chart_coercivity hγ hC hCΩ
  refine ⟨L,B,hL,hB,fun {u v} hu hv hRepr => ⟨?_,?_⟩⟩
  · intro c
    let V (x : X N) := (v x - c)^2
    have hV : Continuous V := (hv.continuous.sub continuous_const).pow 2
    have hVρ : ContinuousOn (fun x => V x * chartVolume γ x) C :=
      hV.continuousOn.mul ((CalderonN.continuousOn_metricVolumeDensity hγ).mono hCΩ)
    let D := nativeInteriorMetricChart g μ hμ e heI he hes
    have hR : EqOn ((fun p => (u p - c)^2) ∘ D.chart.symm) V e.target := by
      intro x hx
      change (u (e.symm x) - c)^2 = _
      exact congrArg (fun t : ℝ => (t - c)^2) (hRepr hx)
    calc
      _ = ∫ x in e.target, V x * chartVolume (coordinateMetric g e) x :=
        integral_interiorChart_of_coordinateRepresentation D hV.continuousOn hR
      _ = ∫ x in C, V x * chartVolume γ x := by
        rw [← setIntegral_congr_set hAE (f := fun x => V x * chartVolume γ x)]
        apply setIntegral_congr_fun e.open_target.measurableSet
        intro x hx
        simp only [chartVolume,hMetric hx]
      _ ≤ _ := by
        rw [← integral_const_mul]
        apply setIntegral_mono_on
          (hVρ.integrableOn_compact hC)
          ((hV.const_mul B).continuousOn.integrableOn_compact hC) hC.isClosed.measurableSet
        intro x hx
        simpa only [mul_comm B] using mul_le_mul_of_nonneg_left (hρ x hx) (sq_nonneg (v x - c))
  · let q (x : X N) := ‖fderiv ℝ v x‖^2
    let F (x : X N) := ∑ i : I N, coordDeriv i v x * divergenceFlux γ v x i
    have hFint : IntegrableOn F e.target := by
      have hC' : ContinuousOn F C := by
        apply continuousOn_finsetSum
        intro i _
        have hi := (CalderonN.contDiffOn_coordDeriv hv.contDiffOn isOpen_univ i).continuousOn
        have hFlux : ContinuousOn (fun x => divergenceFlux γ v x i) C := by
          unfold divergenceFlux
          apply continuousOn_finsetSum
          intro j _
          exact ((CalderonN.contDiffOn_divergenceCoeff hγ i j).continuousOn.mono hCΩ).mul
            ((CalderonN.contDiffOn_coordDeriv hv.contDiffOn isOpen_univ j).continuousOn.mono
              (subset_univ _))
        exact (hi.mono (subset_univ _)).mul hFlux
      exact (hC'.integrableOn_compact hC).mono_set heC
    have hQ : Continuous q := (hv.continuous_fderiv (by simp)).norm.pow 2
    have hEnergy := integral_energyPairingDensity_in_coordinates g μ hμ e heI he hes
      hu.contMDiffOn hu.contMDiffOn
    have hEq : (∫ p in e.source, energyPairingDensity g u u p ∂μ) = ∫ x in e.target, F x := by
      rw [hEnergy]
      apply setIntegral_congr_fun e.open_target.measurableSet
      intro x hx
      have hD (i : I N) := CalderonN.eqOn_coordDeriv e.open_target hRepr i hx
      simp only [F,divergenceFlux,divergenceCoeff,chartVolume,hMetric hx,hD]
    calc
      _ = ∫ x in e.target, L * q x := by
        rw [← integral_const_mul,setIntegral_congr_set hAE]
      _ ≤ ∫ x in e.target, F x :=
        setIntegral_mono_on ((hQ.const_mul L).continuousOn.integrableOn_compact hC |>.mono_set heC)
          hFint e.open_target.measurableSet (fun x hx => hCoercive x (heC hx) v)
      _ = ∫ p in e.source, energyPairingDensity g u u p ∂μ := hEq.symm
      _ ≤ _ := setIntegral_le_integral (integrable_energyPairingDensity g μ hμ hu hu)
        (Eventually.of_forall fun p => by rw [energyPairingDensity_self]; exact covectorEnergy_nonneg g p _)

end CalderonPatch

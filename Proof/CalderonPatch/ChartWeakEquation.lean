module

public import Proof.CalderonPatch.ChartSobolev
public import Proof.ReleasedAnalysis.TauCeti.Analysis.PDE.EnergyForm.Sobolev

import Proof.CalderonN.ClassicalSourceEquation
import Proof.CalderonPatch.KernelJetTransposition

public section

noncomputable section
open Filter MeasureTheory Set TopologicalSpace TauCeti TauCeti.PDE
open scoped ContDiff Distributions ENNReal Gradient Manifold RealInnerProductSpace

namespace CalderonPatch

open CalderonN (X I axis coordDeriv chartVolume chartTest contMDiff_chartTest
  tsupport_chartTest_subset divergenceCoeff divergenceFlux)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (𝓡∂ (m + 1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "N" => (m + 1)
local notation "J" => 𝓡∂ N
local notation "K" => 𝓘(ℝ, X N)
local notation "R" => 𝓘(ℝ, ℝ)

/-- The density-weighted inverse metric of the actual chart metric. -/
@[expose] def chartDivergenceMatrix (g : SmoothMetric N M)
    (e : OpenPartialHomeomorph M (X N)) (z : X N) : Matrix (I N) (I N) ℝ :=
  divergenceCoeff (coordinateMetric g e) z

private theorem gradient_coordinate (v : X N → ℝ) (z : X N) (i : I N) :
    gradient v z i = coordDeriv i v z := by
  rw [coordDeriv, ← inner_gradient_left]
  simp only [axis, EuclideanSpace.inner_single_right, conj_trivial, one_mul]

/-- A smooth test supported in an interior chart, extended by zero. -/
@[expose] def nativeChartTest (D : DirichletData m M)
    (e : OpenPartialHomeomorph M (X N)) (heI : e.source ⊆ (J).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    DirichletTest D :=
  DirichletTest.ofSmooth (chartTest e φ)
    (contMDiff_chartTest e he φ.contDiff φ.hasCompactSupport φ.tsupport_subset)
    (fun p hp => indicator_of_notMem (fun h => (Set.disjoint_left.mp (J).disjoint_interior_boundary) (heI h) hp) _)

private theorem tsupport_nativeChartTest_subset (D : DirichletData m M)
    (e : OpenPartialHomeomorph M (X N)) (heI : e.source ⊆ (J).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    tsupport (nativeChartTest D e heI he φ : M → ℝ) ⊆ e.source := by
  intro p hp
  obtain ⟨z,hz,rfl⟩ := tsupport_chartTest_subset e φ.hasCompactSupport φ.tsupport_subset hp
  exact e.map_target (φ.tsupport_subset hz)

set_option maxHeartbeats 1200000 in
/-- Compare native completed energy with the coordinate matrix form against
a smooth test supported wholly inside the chart. -/
theorem chartSobolev_energy_eq (D : DirichletData m M)
    (e : OpenPartialHomeomorph M (X N)) (heI : e.source ⊆ (J).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    (F : DirichletHilbert D →L[ℝ] W1p (volume : Measure (X N)) ⟨e.target,e.open_target⟩ 2)
    (hF : ∀ u : DirichletTest D,
      (W1p.value (F (u : DirichletHilbert D)) : X N → ℝ)
        =ᵐ[(volume : Measure (X N)).restrict e.target] u ∘ e.symm)
    (hRepr : ∀ u : DirichletTest D, ∃ v : X N → ℝ,
      ContDiff ℝ ∞ v ∧ EqOn (u ∘ e.symm) v e.target)
    (hCoeff : MemLp (fun z => energyIntegrand (chartDivergenceMatrix D.metric e z) 0 0) ⊤
      ((volume : Measure (X N)).restrict e.target))
    (φ : 𝓓(⟨e.target,e.open_target⟩, ℝ)) (w : DirichletHilbert D) :
    energyFormH1 (chartDivergenceMatrix D.metric e) 0 0 (F w)
      (W1p.ofTestFunctionₗ volume ⟨e.target,e.open_target⟩ 2 φ) =
      ⟪w, (nativeChartTest D e heI he φ : DirichletHilbert D)⟫ := by
  let U : Opens (X N) := ⟨e.target,e.open_target⟩
  let s := W1p.ofTestFunctionₗ volume U 2 φ
  let v := nativeChartTest D e heI he φ
  change energyFormH1 (chartDivergenceMatrix D.metric e) 0 0 (F w) s =
    ⟪w, (v : DirichletHilbert D)⟫
  rw [← energyFormH1L_apply hCoeff]
  refine UniformSpace.Completion.induction_on w (isClosed_eq
    (((energyFormH1L hCoeff).continuous.comp F.continuous).clm_apply continuous_const)
    (continuous_id.inner continuous_const)) ?_
  intro u
  rw [energyFormH1L_apply, inner_dirichletHilbert_coe, energyFormH1_def]
  obtain ⟨b,hb,hbEq⟩ := hRepr u
  have hGr := CalderonN.weak_gradient_eq_gradient_of_ae_value (U := U) le_rfl
    (F (u : DirichletHilbert D)) hb ((hF u).trans
      ((ae_restrict_mem e.open_target.measurableSet).mono fun _ hx => hbEq hx))
  have hφGr : (W1p.gradient s : X N → X N) =ᵐ[(volume : Measure (X N)).restrict e.target]
      gradient (φ : X N → ℝ) := by
    unfold s
    rw [W1p.gradient_ofTestFunctionₗ]
    exact gradientTestFunctionLp_apply_ae 2 φ
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := e.source) (f := energyPairingDensity D.metric u v)
    (fun p hp => energyPairingDensity_eq_zero_off_tsupport D.metric u v
      (fun hs => hp (tsupport_nativeChartTest_subset D e heI he φ hs))),
    integral_energyPairingDensity_in_coordinates D.metric D.volume D.metric_volume e heI he hes
      u.smooth.contMDiffOn v.smooth.contMDiffOn]
  apply integral_congr_ae
  filter_upwards [hGr,hφGr,ae_restrict_mem e.open_target.measurableSet] with z hz hφz hzT
  have hφeq := chartTest_comp_inverse e (φ : X N → ℝ)
  have hx (i : I N) : coordDeriv i (v ∘ e.symm) z = coordDeriv i (φ : X N → ℝ) z :=
    congrArg (fun L : X N →L[ℝ] ℝ => L (axis i))
      (hφeq.eventuallyEq_of_mem (e.open_target.mem_nhds hzT)).fderiv_eq
  have hy (i : I N) : coordDeriv i (u ∘ e.symm) z = coordDeriv i b z :=
    congrArg (fun L : X N →L[ℝ] ℝ => L (axis i))
      (hbEq.eventuallyEq_of_mem (e.open_target.mem_nhds hzT)).fderiv_eq
  rw [energyIntegrand_apply, jetField_apply, jetField_apply, hz, hφz]
  simp only [driftForm_apply, massForm_apply, Pi.zero_apply, inner_zero_left, zero_mul, add_zero]
  rw [@matrixBilinearForm_apply]
  simp only [dotProduct, Matrix.mulVec, divergenceFlux, chartDivergenceMatrix, hx, hy, gradient_coordinate]

/-- The native weak inverse satisfies the divergence-form equation
with the actual Riemannian volume multiplying the forcing. -/
theorem chartSobolev_weakDirichletInverse_test (D : DirichletData m M)
    (e : OpenPartialHomeomorph M (X N)) (heI : e.source ⊆ (J).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    (F : DirichletHilbert D →L[ℝ] W1p (volume : Measure (X N)) ⟨e.target,e.open_target⟩ 2)
    (hF : ∀ u : DirichletTest D,
      (W1p.value (F (u : DirichletHilbert D)) : X N → ℝ)
        =ᵐ[(volume : Measure (X N)).restrict e.target] u ∘ e.symm)
    (hRepr : ∀ u : DirichletTest D, ∃ v : X N → ℝ,
      ContDiff ℝ ∞ v ∧ EqOn (u ∘ e.symm) v e.target)
    (hCoeff : MemLp (fun z => energyIntegrand (chartDivergenceMatrix D.metric e z) 0 0) ⊤
      ((volume : Measure (X N)).restrict e.target))
    (f : Lp ℝ 2 D.volume) {q : M → ℝ} (hq : Continuous q) (hf : (f : M → ℝ) =ᵐ[D.volume] q)
    (φ : 𝓓(⟨e.target,e.open_target⟩, ℝ)) :
    energyFormH1 (chartDivergenceMatrix D.metric e) 0 0 (F (D.weakDirichletInverse f))
      (W1p.ofTestFunctionₗ volume ⟨e.target,e.open_target⟩ 2 φ) =
      ∫ z in e.target, (q (e.symm z) * chartVolume (coordinateMetric D.metric e) z) * φ z := by
  let v := nativeChartTest D e heI he φ
  let C := nativeInteriorMetricChart D.metric D.volume D.metric_volume e heI he hes
  rw [chartSobolev_energy_eq D e heI he hes F hF hRepr hCoeff, D.weakDirichletInverse_on_test]
  calc
    _ = ∫ p, q p * (v p) ∂D.volume := by
      apply integral_congr_ae
      filter_upwards [hf] with _ hp
      rw [hp]
    _ = ∫ p in e.source, q p * (v p) ∂D.volume := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      change q p * chartTest e φ p = 0
      rw [chartTest, indicator_of_notMem hp, mul_zero]
    _ = ∫ z in e.target, (q (e.symm z) * φ z) * chartVolume (coordinateMetric D.metric e) z := by
      apply integral_interiorChart_of_coordinateRepresentation C
      · exact (hq.continuousOn.comp e.symm.continuousOn (mapsTo_univ _ _)).mul φ.continuous.continuousOn
      · intro z hz
        change q (e.symm z) * chartTest e φ (e.symm z) = _
        exact congrArg (q (e.symm z) * ·) (chartTest_comp_inverse e (φ : X N → ℝ) hz)
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => mul_right_comm _ _ _

/-- The coordinate test equation only reads the forcing on the source
of the interior chart. -/
theorem chartSobolev_weakDirichletInverse_test_of_local
    (D : DirichletData m M) (e : OpenPartialHomeomorph M (X N))
    (heI : e.source ⊆ (J).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    (F : DirichletHilbert D →L[ℝ] W1p (volume : Measure (X N)) ⟨e.target,e.open_target⟩ 2)
    (hF : ∀ u : DirichletTest D,
      (W1p.value (F (u : DirichletHilbert D)) : X N → ℝ)
        =ᵐ[(volume : Measure (X N)).restrict e.target] u ∘ e.symm)
    (hRepr : ∀ u : DirichletTest D, ∃ v : X N → ℝ,
      ContDiff ℝ ∞ v ∧ EqOn (u ∘ e.symm) v e.target)
    (hCoeff : MemLp (fun z => energyIntegrand (chartDivergenceMatrix D.metric e z) 0 0) ⊤
      ((volume : Measure (X N)).restrict e.target))
    (f : Lp ℝ 2 D.volume) {q : M → ℝ} (hq : ContinuousOn q e.source)
    (hf : (f : M → ℝ) =ᵐ[D.volume.restrict e.source] q)
    (φ : 𝓓(⟨e.target,e.open_target⟩, ℝ)) :
    energyFormH1 (chartDivergenceMatrix D.metric e) 0 0 (F (D.weakDirichletInverse f))
      (W1p.ofTestFunctionₗ volume ⟨e.target,e.open_target⟩ 2 φ) =
      ∫ z in e.target, (q (e.symm z) * chartVolume (coordinateMetric D.metric e) z) * φ z := by
  let v := nativeChartTest D e heI he φ
  let C := nativeInteriorMetricChart D.metric D.volume D.metric_volume e heI he hes
  rw [chartSobolev_energy_eq D e heI he hes F hF hRepr hCoeff, D.weakDirichletInverse_on_test]
  calc
    _ = ∫ p in e.source, f p * (v p) ∂D.volume := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      change f p * chartTest e φ p = 0
      rw [chartTest, indicator_of_notMem hp, mul_zero]
    _ = ∫ p in e.source, q p * (v p) ∂D.volume := by
      apply integral_congr_ae
      filter_upwards [hf] with _ hp
      rw [hp]
    _ = ∫ z in e.target, (q (e.symm z) * φ z) * chartVolume (coordinateMetric D.metric e) z := by
      apply integral_interiorChart_of_coordinateRepresentation C
      · exact (hq.comp e.symm.continuousOn (fun z hz => e.map_target hz)).mul φ.continuous.continuousOn
      · intro z hz
        change q (e.symm z) * chartTest e φ (e.symm z) = _
        exact congrArg (q (e.symm z) * ·) (chartTest_comp_inverse e (φ : X N → ℝ) hz)
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => mul_right_comm _ _ _

end CalderonPatch

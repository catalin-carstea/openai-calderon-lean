import Proof.Archive.NativeH2CoefficientFluxGreen
import Proof.Archive.ClmInheritedStructureData
import Proof.Archive.InheritedNormedStructureData

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativePolynomialBulkMoments

theorem memLp_unitBall_of_continuous_normed
    {V : Type*} [NormedAddCommGroup V] (f : R3 → V) (hf : Continuous f) :
    MemLp f ⊤ ((volume : Measure R3).restrict ballOpens) := by
  letI : IsFiniteMeasure ((volume : Measure R3).restrict ballOpens) :=
    ⟨by simpa only [Measure.restrict_apply_univ,coe_ballOpens] using
      ((measure_mono (show B ⊆ Metric.closedBall (0 : R3) 1 from Metric.ball_subset_closedBall)).trans_lt
        (isCompact_closedBall (0 : R3) 1).measure_lt_top)⟩
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : R3) 1).exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  exact hC x (Metric.ball_subset_closedBall hx)

lemma memLp_coefficientMatrixEnergyIntegrand_of_smooth (F : SmoothCoefficientMatrix 2) :
    MemLp (fun x : R3 => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
  have hc : Continuous (fun x : R3 => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F x) 0 0) :=
    TauCeti.PDE.Continuous.energyIntegrand (contDiff_coefficientMatrixField 2 F).continuous
      continuous_const continuous_const
  have hbridge :
      Continuous (fun x : R3 => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F x) 0 0) →
      MemLp (fun x : R3 => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F x) 0 0) ⊤
        ((volume : Measure R3).restrict ballOpens) := by
    have ht := memLp_unitBall_of_continuous_normed
      (fun x : R3 => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F x) 0 0)
    simpa only [real_nontriviallyNormedField_normedField_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,
      normedAddCommGroup_ofSeparation_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] using ht
  exact hbridge hc


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

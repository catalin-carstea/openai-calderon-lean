import Proof.Archive.NativeWeightedDriftFluxGreen

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativePolynomialBulkMoments

lemma memLp_nativeEnergyIntegrand_of_continuous
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    MemLp (fun x : R3 => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
  have ht := memLp_unitBall_of_continuous_normed
    (fun x : R3 => TauCeti.PDE.energyIntegrand (a x) (b x) (c x))
  have hbridge : Continuous (fun x : R3 => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) →
      MemLp (fun x : R3 => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
        ((volume : Measure R3).restrict ballOpens) := by
    simpa only [real_nontriviallyNormedField_normedField_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,normedAddCommGroup_ofSeparation_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] using ht
  exact hbridge (TauCeti.PDE.Continuous.energyIntegrand ha hb hc)


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

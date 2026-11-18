import Proof.CoarseOneBoundaryBundleLinear
import Proof.CoarseBoundaryTaylorBounds
import Proof.CommonSupportBoundaryOperatorRegularity
import Proof.FiniteJetBoundCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

variable {P A B : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]

lemma norm_iteratedFDeriv_prod_fst_at_le (f : P → A × B) (p : P) (hf : ContDiffAt ℝ ∞ f p) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun q => (f q).1) p‖ ≤ ‖iteratedFDeriv ℝ n f p‖ :=
  (norm_iteratedFDeriv_clm_comp_le (ContinuousLinearMap.fst ℝ A B) f p hf n).trans
    ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_fst_le ℝ A B) (norm_nonneg _)).trans_eq (one_mul _))

lemma norm_iteratedFDeriv_prod_snd_at_le (f : P → A × B) (p : P) (hf : ContDiffAt ℝ ∞ f p) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun q => (f q).2) p‖ ≤ ‖iteratedFDeriv ℝ n f p‖ :=
  (norm_iteratedFDeriv_clm_comp_le (ContinuousLinearMap.snd ℝ A B) f p hf n).trans
    ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_snd_le ℝ A B) (norm_nonneg _)).trans_eq (one_mul _))

theorem norm_iteratedFDeriv_coarseOneBoundaryBundle_components_le
    (f : P → CoarseOneBoundaryBundle) (p : P) (hf : ContDiffAt ℝ ∞ f p)
    (n : ℕ) (C : ℝ) (hC : ‖iteratedFDeriv ℝ n f p‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun q => (f q).1) p‖ ≤ C ∧
    ‖iteratedFDeriv ℝ n (fun q => (f q).2.1) p‖ ≤ C ∧
    ‖iteratedFDeriv ℝ n (fun q => (f q).2.2.1) p‖ ≤ C ∧
    ‖iteratedFDeriv ℝ n (fun q => (f q).2.2.2) p‖ ≤ C := by
  have hS := (norm_iteratedFDeriv_prod_snd_at_le f p hf n).trans hC
  have hSS := (norm_iteratedFDeriv_prod_snd_at_le (fun q => (f q).2) p hf.snd n).trans hS
  exact ⟨(norm_iteratedFDeriv_prod_fst_at_le f p hf n).trans hC,
    (norm_iteratedFDeriv_prod_fst_at_le (fun q => (f q).2) p hf.snd n).trans hS,
    (norm_iteratedFDeriv_prod_fst_at_le (fun q => (f q).2.2) p hf.snd.snd n).trans hSS,
    (norm_iteratedFDeriv_prod_snd_at_le (fun q => (f q).2.2) p hf.snd.snd n).trans hSS⟩

variable [FiniteDimensional ℝ P]

theorem contDiff_commonSupport_coarseOneBoundaryBundle
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) :
    ContDiff ℝ ∞ (fun p => coarseOneBoundaryBundle (commonSupportMatrixFamily 2 a ha S hS hz p)) :=
  (contDiff_commonSupport_coarseNormalMul a ha S hS hz).prodMk
    ((contDiff_commonSupport_oneNormalMul a ha S hS hz).prodMk
      ((contDiff_commonSupport_coarseBoundaryTangential a ha S hS hz).prodMk
        (contDiff_commonSupport_adjointBoundaryTangential a ha S hS hz)))

theorem coarseOneBoundaryBundle_flat (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) :
    coarseOneBoundaryBundle F0 = (ContinuousLinearMap.id ℝ (SphereSobolev 0),
      ContinuousLinearMap.id ℝ (SphereSobolev 1),0,0) := by
  have hT := boundaryTangential_scalar_zero F0 (fun _ => 1) (by
    intro w
    simpa only [one_smul] using hF0 w.val (Metric.closedBall_subset_closedBall (by norm_num)
      (Metric.sphere_subset_closedBall w.property)))
  exact Prod.ext (coarseNormalCoefficient_flat F0 hF0)
    (Prod.ext (oneNormalCoefficient_flat F0 hF0) (Prod.ext hT.1 hT.2))

end ShrinkingSpheres

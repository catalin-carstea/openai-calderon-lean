import Proof.Archive.FiniteDimensionalLocalSmoothExtension
import Proof.Archive.CommonSupportMatrixInverse
import Proof.JointMetricCoefficientRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Shared compact representative construction on any genuine open joint
    domain containing the selected parameter and the entire closed spatial ball. -/
theorem exists_local_commonSupport_family_on_open {Y : Set P} (hY : IsOpen Y)
    (a : P × X → F) (L : ℝ) (U : Set (P × X)) (hU : IsOpen U)
    (ha : ContDiffOn ℝ ∞ a U) {y : P} (hy : y ∈ Y)
    (hSub : {y} ×ˢ Metric.closedBall (0:X) L ⊆ U) :
    ∃ A : P × X → F,ContDiff ℝ ∞ A ∧ ∃ K : Set X,IsCompact K ∧
      (∀ p z,z ∉ K → A (p,z) = 0) ∧ ∃ V : Set P,IsOpen V ∧ y ∈ V ∧ V ⊆ Y ∧
      ∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) L,A =ᶠ[𝓝 (p,z)] a := by
  let C : Set (P × X) := {y} ×ˢ Metric.closedBall (0:X) L
  have hCompact : IsCompact C := isCompact_singleton.prod (isCompact_closedBall _ _)
  obtain ⟨A,hA,hSupport,hNear⟩ := exists_contDiff_eq_near_compact_of_contDiffOn C U hCompact hU hSub a ha
  let K := Prod.snd '' tsupport A
  have hK : IsCompact K := hSupport.image continuous_snd
  have hz : ∀ p z,z ∉ K → A (p,z) = 0 := by
    intro p z hz
    by_contra hne
    exact hz ⟨(p,z),subset_closure hne,rfl⟩
  have hEvent : ∀ᶠ p in 𝓝 y,∀ z ∈ Metric.closedBall (0:X) L,A =ᶠ[𝓝 (p,z)] a := by
    apply (isCompact_closedBall (0:X) L).eventually_forall_of_forall_eventually
    intro z hz
    exact (hNear (y,z) ⟨rfl,hz⟩).eventuallyEq_nhds
  have hBoth : {p | p ∈ Y ∧ ∀ z ∈ Metric.closedBall (0:X) L,A =ᶠ[𝓝 (p,z)] a} ∈ 𝓝 y := by
    filter_upwards [hY.mem_nhds hy,hEvent] with p hp he
    exact ⟨hp,he⟩
  obtain ⟨V,hVsub,hV,hyV⟩ := mem_nhds_iff.mp hBoth
  exact ⟨A,hA,K,hK,hz,V,hV,hyV,(fun p hp => (hVsub hp).1),fun p hp => (hVsub hp).2⟩

/-- Matrix specialization used by the original center-family constructor. -/
theorem exists_local_commonSupport_matrix_family_on_open {Y : Set P} (hY : IsOpen Y)
    (a : P × X → Mat) (L : ℝ) (U : Set (P × X)) (hU : IsOpen U)
    (ha : ContDiffOn ℝ ∞ a U) {y : P} (hy : y ∈ Y)
    (hSub : {y} ×ˢ Metric.closedBall (0:X) L ⊆ U) :
    ∃ A : P × X → Mat,ContDiff ℝ ∞ A ∧ ∃ K : Set X,IsCompact K ∧
      (∀ p z,z ∉ K → A (p,z) = 0) ∧ ∃ V : Set P,IsOpen V ∧ y ∈ V ∧ V ⊆ Y ∧
      ∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) L,A =ᶠ[𝓝 (p,z)] a :=
  exists_local_commonSupport_family_on_open hY a L U hU ha hy hSub

end ShrinkingSpheres

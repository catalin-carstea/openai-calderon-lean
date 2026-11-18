import Proof.ComplexSphereDuality
import Proof.FrameCoordinatesLinear
import Proof.Archive.FiniteDimensionalLocalSmoothExtension

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothAngularCasimir
open OAI.AnisotropicCalderon.GreenRadialTrace

/-- Smooth scalar sphere tests separate actual L2 representatives. -/
theorem sphereL2_eq_of_smooth_inner (u v : SphereL2)
    (h : ∀ f : SmoothData,⟪smoothSphereLift f.1 f.2,u⟫_ℝ = ⟪smoothSphereLift f.1 f.2,v⟫_ℝ) : u = v := by
  apply ext_inner_left ℝ
  intro q
  refine polynomialSphereL2_denseRange.induction_on q
    (isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)) ?_
  intro p
  have hHere := h ⟨polynomialEvaluation p,contDiff_polynomialEvaluation p⟩
  change ⟪smoothSphereLift (polynomialEvaluation p) (contDiff_polynomialEvaluation p),u⟫_ℝ =
    ⟪smoothSphereLift (polynomialEvaluation p) (contDiff_polynomialEvaluation p),v⟫_ℝ at hHere
  simpa only [smoothSphereLift_polynomialEvaluation] using hHere

/-- A component of any actual smooth field on one physical sphere has a
    globally smooth standard representative. Only frame values are used. -/
theorem smoothNear.exists_smooth_frame_component {Y : Set X} {g : MetricField} {φ : Field}
    (hφ : smoothNear φ (bundle Y g)) {y : X} (hy : y ∈ Y) (e : Frame)
    (hFrame : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (L : ℂ →L[ℝ] ℝ) :
    ∃ f : SmoothData,∀ w : UnitSphere,f.1 w.val = L (φ (y,frameVector e y w.val)) := by
  have hSlice := (hφ.sphere_slice hy).realComponent L
  obtain ⟨V,hV,hSphere,hSmooth⟩ := hSlice
  let S : Set X := (frameVector e y) ⁻¹' V
  have hOpen : IsOpen S := hV.preimage (contDiff_frameVector_fixed e y).continuous
  have hSubset : Metric.sphere (0:X) 1 ⊆ S := by
    intro z hz
    exact hSphere (frameVector_mem_sphere g e y hFrame ⟨z,hz⟩)
  have hS : ContDiffOn ℝ ∞ (fun z => L (φ (y,frameVector e y z))) S :=
    hSmooth.comp (contDiff_frameVector_fixed e y).contDiffOn (fun _ hz => hz)
  obtain ⟨f,hf,hCompact,hNear⟩ := exists_contDiff_eq_near_compact_of_contDiffOn
    (Metric.sphere (0:X) 1) S (isCompact_sphere _ _) hOpen hSubset _ hS
  exact ⟨⟨f,hf⟩,fun w => (hNear w.val w.property).eq_of_nhds⟩

/-- Every smooth physical input component has an actual H1 representative in
    the same frame and sphere probability measure. -/
theorem smoothNear.exists_one_boundary_component {Y : Set X} {g : MetricField} {φ : Field}
    (hφ : smoothNear φ (bundle Y g)) {y : X} (hy : y ∈ Y) (e : Frame)
    (hFrame : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (L : ℂ →L[ℝ] ℝ) :
    ∃ v : SphereSobolev 1,
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
        (sphereSobolevInclusionL 1 0 (by norm_num) v) =ᵐ[sphereProbability]
          fun w : UnitSphere => L (φ (y,frameVector e y w.val)) := by
  obtain ⟨f,hRep⟩ := hφ.exists_smooth_frame_component hy e hFrame L
  refine ⟨smoothOneBoundaryData f,?_⟩
  filter_upwards [smoothOneBoundaryData_value_ae f] with w hw
  exact hw.trans (hRep w)

end ShrinkingSpheres

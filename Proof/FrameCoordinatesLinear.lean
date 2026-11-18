import Proof.FrameCoordinateCovectors
import Proof.SmoothSphereSobolevData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

def frameCoordinatesLinear (g : MetricField) (e : Frame) (y : X) : X →L[ℝ] X :=
  ∑ j : I,(frameCoordinateLinear g e y j).smulRight (axis j)

lemma frameCoordinatesLinear_apply (g : MetricField) (e : Frame) (y w : X) (j : I) :
    frameCoordinatesLinear g e y w j = frameCoordinateLinear g e y j w := by
  simp [frameCoordinatesLinear,axis,Pi.single_apply]

lemma frameCoordinatesLinear_frameVector (g : MetricField) (e : Frame) (y z : X)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0) :
    frameCoordinatesLinear g e y (frameVector e y z) = z := by
  ext j
  rw [frameCoordinatesLinear_apply,frameCoordinateLinear_apply,frameVector,metricPair_sum_left]
  simp only [metricPair_smul_left,he,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

lemma frameVector_frameCoordinatesLinear (g : MetricField) (e : Frame) (y w : X)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0) :
    frameVector e y (frameCoordinatesLinear g e y w) = w := by
  simpa only [frameVector,frameCoordinatesLinear_apply] using frameCoordinateLinear_reconstruct g e y w he

def physicalBoundarySmoothData (g : MetricField) (e : Frame) (y : X) (f : SmoothData) : SmoothData :=
  ⟨f.1 ∘ frameCoordinatesLinear g e y,f.2.comp (frameCoordinatesLinear g e y).contDiff⟩

/-- Every smooth standard-sphere test is the trace of an admitted physical
    harmonic solution, for the canonical high Sobolev datum of that same test. -/
theorem Admissible.exists_harmonic_smooth_sphere_test {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y) (f : SmoothData) :
    ∃ u : X → ℝ,HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u ∧
      (∀ w : UnitSphere,u (normalChart d.expMap d.frame y (d.radius y) w.val) = f.1 w.val) ∧
      fixedBoundaryValueL (smoothHighBoundaryData f) =ᵐ[sphereProbability]
        fun w : UnitSphere => u (normalChart d.expMap d.frame y (d.radius y) w.val) := by
  let a := physicalBoundarySmoothData d.γ d.frame y f
  have ha : smoothNear a.1 (sphereAt d.γ y) := ⟨univ,isOpen_univ,subset_univ _,a.2.contDiffOn⟩
  obtain ⟨u,hu,hUnique⟩ := hd.2.2.1 y hy a.1 ha
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hValue (w : UnitSphere) : u (normalChart d.expMap d.frame y (d.radius y) w.val) = f.1 w.val := by
    have h := hu.2 (frameVector d.frame y w.val) (frameVector_mem_sphere d.γ d.frame y hFrame w)
    change u (normalChart d.expMap d.frame y (d.radius y) w.val) =
      f.1 (frameCoordinatesLinear d.γ d.frame y (frameVector d.frame y w.val)) at h
    exact h.trans (congrArg f.1 (frameCoordinatesLinear_frameVector d.γ d.frame y w.val hFrame))
  refine ⟨u,hu.1,hValue,?_⟩
  filter_upwards [smoothHighBoundaryData_value_ae f] with w hw
  exact hw.trans (hValue w).symm

end ShrinkingSpheres

import Proof.FlatNormalizedAngularOperators
import Proof.ComplexBesselSections
import Proof.SpherePartialRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

theorem sobolevSq_one_eq_native_pair (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (F : X → ℂ) (u v : SphereSobolev 1)
    (hRe : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (sphereSobolevInclusionL 1 0 (by norm_num) u) =ᵐ[sphereProbability]
        fun w : UnitSphere => (F (frameVector e y w.val)).re)
    (hIm : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (sphereSobolevInclusionL 1 0 (by norm_num) v) =ᵐ[sphereProbability]
        fun w : UnitSphere => (F (frameVector e y w.val)).im) :
    sobolevSq g e 1 y F = ‖u‖^2+‖v‖^2 := by
  have h := sobolevSq_eq_bessel_components g e y hframe F _ _ _ _ hRe hIm 1
    (sphereSobolev_one_physical_besselGraph u) (sphereSobolev_one_physical_besselGraph v)
  simpa only [LinearIsometryEquiv.norm_map] using h

theorem fiberSq_eq_native_pair (e : Frame) (y : X) (F : X → ℂ) (u v : SphereSobolev 0)
    (hRe : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm u =ᵐ[sphereProbability]
      fun w : UnitSphere => (F (frameVector e y w.val)).re)
    (hIm : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm v =ᵐ[sphereProbability]
      fun w : UnitSphere => (F (frameVector e y w.val)).im) :
    fiberSq e y F = ‖u‖^2+‖v‖^2 := by
  rw [fiberSq_integral_norm]
  have h := integral_complex_norm_sq_components (fun w : UnitSphere => F (frameVector e y w.val)) _ _ hRe hIm
  simpa only [LinearIsometryEquiv.norm_map] using h

/-- A real H1 operator acting on both components controls the actual complex
    physical fiber norm by the exact frozen H1 Sobolev square. -/
theorem fiberSq_operator_bound (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (F G : X → ℂ) (u v : SphereSobolev 1) (S : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (C : ℝ) (hC : 0 ≤ C) (hS : ‖S‖ ≤ C)
    (hRe : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (sphereSobolevInclusionL 1 0 (by norm_num) u) =ᵐ[sphereProbability]
        fun w : UnitSphere => (F (frameVector e y w.val)).re)
    (hIm : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (sphereSobolevInclusionL 1 0 (by norm_num) v) =ᵐ[sphereProbability]
        fun w : UnitSphere => (F (frameVector e y w.val)).im)
    (hOutRe : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (S u) =ᵐ[sphereProbability]
      fun w : UnitSphere => (G (frameVector e y w.val)).re)
    (hOutIm : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (S v) =ᵐ[sphereProbability]
      fun w : UnitSphere => (G (frameVector e y w.val)).im) :
    fiberSq e y G ≤ C^2*sobolevSq g e 1 y F := by
  have hEach (w : SphereSobolev 1) : ‖S w‖^2 ≤ C^2*‖w‖^2 := by
    have hNorm := (S.le_opNorm w).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg w))
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg w))).mpr hNorm
  rw [fiberSq_eq_native_pair e y G _ _ hOutRe hOutIm,sobolevSq_one_eq_native_pair g e y hframe F u v hRe hIm,mul_add]
  exact add_le_add (hEach u) (hEach v)

theorem fiberSq_smul_real (e : Frame) (y : X) (r : ℝ) (F : X → ℂ) :
    fiberSq e y (fun w => r • F w) = r^2*fiberSq e y F := by
  rw [fiberSq_integral_norm,fiberSq_integral_norm]
  simp_rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  exact integral_const_mul _ _

end ShrinkingSpheres

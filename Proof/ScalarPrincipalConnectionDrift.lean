import Proof.HighSectionHessianCoordinateContraction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The actual base-connection drift from the scalar Hessian. It is a
metric/profile coefficient and contains no derivatives of the chosen frame. -/
def scalarPrincipalConnectionWeight (d : Data) (k : I) (y : X) : ℝ :=
  ∑ a : I,∑ b : I,scalarPrincipalMatrix d.γ d.g₂ d.radius y a b*christoffel d.γ y k a b

lemma connection_axis_coordinate (g : MetricField) (y : X) (a b k : I) :
    connection g y (axis a) (axis b) k=christoffel g y k a b := by
  simp [connection,axis,PiLp.single_apply]

lemma continuousLinear_connection_axis_expansion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : X →L[ℝ] E) (g : MetricField) (y : X) (a b : I) :
    L (connection g y (axis a) (axis b))=∑ k : I,christoffel g y k a b • L (axis k) := by
  rw [←axis_expansion (connection g y (axis a) (axis b))]
  simp only [map_sum,map_smul,connection_axis_coordinate]

lemma scalarPrincipalConnectionWeight_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : Data) (y : X) (L : X →L[ℝ] E) :
    (∑ a : I,∑ b : I,scalarPrincipalMatrix d.γ d.g₂ d.radius y a b •
      L (connection d.γ y (axis a) (axis b)))=
      ∑ k : I,scalarPrincipalConnectionWeight d k y • L (axis k) := by
  simp_rw [continuousLinear_connection_axis_expansion]
  simp only [scalarPrincipalConnectionWeight,Fin.sum_univ_three]
  module

/-- The scalar Hessian equals its ordered covariant derivatives minus the
SAME explicitly controlled base-connection drift. -/
lemma scalar_principal_covariant_hessian_trace_split (d : Data) (U : X → SphereSobolev 2) (y : X)
    (hL : DifferentiableAt ℝ (highSectionCovariantDerivativeLinear d U) y) :
    (∑ a : I,∑ b : I,scalarPrincipalMatrix d.γ d.g₂ d.radius y a b •
      highSectionCovariantHessianLinear d U y (axis a) (axis b))=
      (∑ a : I,∑ b : I,scalarPrincipalMatrix d.γ d.g₂ d.radius y a b •
        oneSectionCovariantDerivative d (fun x => highSectionCovariantDerivative d U x (axis b)) y (axis a))-
      ∑ k : I,scalarPrincipalConnectionWeight d k y • sphereSobolevInclusionL 1 0 (by norm_num)
        (highSectionCovariantDerivative d U y (axis k)) := by
  simp_rw [highSectionCovariantHessianLinear_apply d U y _ _ hL]
  simp only [smul_sub,Finset.sum_sub_distrib]
  congr 1
  have hh := scalarPrincipalConnectionWeight_apply d y
    ((sphereSobolevInclusionL 1 0 (by norm_num)).comp (highSectionCovariantDerivativeLinear d U y))
  simpa only [ContinuousLinearMap.comp_apply,highSectionCovariantDerivativeLinear_apply] using hh

end ShrinkingSpheres

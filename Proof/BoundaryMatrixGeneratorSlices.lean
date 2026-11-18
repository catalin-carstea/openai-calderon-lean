import Proof.MatrixFieldJetNorms
import Proof.Archive.NativeBoundaryCoefficientFamilies

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies

/-- The scalar normal and tangent generators belong to the same actual
    compact matrix generator. -/
theorem commonSupport_boundary_generator_slices
    (a : ℝ × X → Mat) (b : X → Mat)
    (hAngle : ∀ z,HasDerivAt (fun t => a (t,z)) (b z) 0) :
    (∀ z,HasDerivAt (fun t => normalCoefficientFunction a (t,z))
      (normalCoefficientFunction (fun v : ℝ × X => b v.2) (0,z)) 0) ∧
    ∀ j z,HasDerivAt (fun t => tangentCoefficientFunction a j (t,z))
      (tangentCoefficientFunction (fun v : ℝ × X => b v.2) j (0,z)) 0 := by
  have hEntry (z : X) (i j : I) : HasDerivAt (fun t => a (t,z) i j) (b z i j) 0 := by
    simpa only [Function.comp_def,matrixEntryL_apply] using
      (matrixEntryL i j).hasFDerivAt.comp_hasDerivAt (0:ℝ) (hAngle z)
  have hN (z : X) : HasDerivAt (fun t => normalCoefficientFunction a (t,z))
      (normalCoefficientFunction (fun v : ℝ × X => b v.2) (0,z)) 0 := by
    exact HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) =>
      HasDerivAt.sum (fun j (_ : j ∈ Finset.univ) =>
        ((hEntry z i j).const_mul (z i)).mul_const (z j)))
  refine ⟨hN,?_⟩
  intro j z
  exact (HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) =>
    (hEntry z i j).const_mul (z i))).sub ((hN z).mul_const (z j))

end ShrinkingSpheres

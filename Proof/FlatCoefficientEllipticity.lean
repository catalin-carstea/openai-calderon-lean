import Proof.UniformStrongC1Neighborhood
import Proof.AffineCoefficientJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- Any actual flat coefficient representative has the canonical positive
    scalar ellipticity on the physical ball, independent of its exterior. -/
theorem uniformlyEllipticOn_flat_coefficientMatrix
    (F0 : SmoothCoefficientMatrix 2) (c : ℝ) (hc : 0 < c)
    (hF0 : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1) :
    TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set X) (coefficientMatrixField 2 (c • F0)) c c := by
  have hh := TauCeti.PDE.uniformlyEllipticOn_smul_one (n:=I) (ballOpens:Set X)
    (fun _ : X => c) hc le_rfl (fun _ _ => ⟨le_rfl,le_rfl⟩)
  refine ⟨hc,le_rfl,?_⟩
  intro z hz
  rw [coefficientMatrixField_smul,hF0 z hz]
  exact hh.2.2 hz

end ShrinkingSpheres

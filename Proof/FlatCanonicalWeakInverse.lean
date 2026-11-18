import Proof.FlatNativeWeakData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- The canonical flat weak inverse has the same explicit coercive bound as
    the wrapped native inverse, proved directly from its flat energy lower bound. -/
theorem norm_flat_canonical_weak_inverse_le (c : ℝ) (hc : 0 < c) :
    ‖(TauCeti.PDE.energyFormH1L0 (flatCoefficientBound c)).inverse‖ ≤ 5*c⁻¹ := by
  have hUE := TauCeti.PDE.uniformlyEllipticOn_smul_one (n:=I) (ballOpens:Set X)
    (fun _ : X => c) hc le_rfl (fun _ _ => ⟨le_rfl,le_rfl⟩)
  have hMeas : AEStronglyMeasurable (fun _ : X => c • (1:Mat)) ((volume:Measure X).restrict ballOpens) :=
    aestronglyMeasurable_const
  have hLower (u : BallH1Zero) : (c/5)*‖u‖*‖u‖ ≤ TauCeti.PDE.energyFormH1L0 (flatCoefficientBound c) u u :=
    unitBall_zeroDrift_coercivity hUE hMeas (flatCoefficientBound c) u
  have h := norm_functionalInverse_le (TauCeti.PDE.energyFormH1L0 (flatCoefficientBound c)) (c/5) (by positivity) hLower
  rw [functionalInverse_eq_inverse] at h
  exact h.trans_eq (by field_simp)

end ShrinkingSpheres

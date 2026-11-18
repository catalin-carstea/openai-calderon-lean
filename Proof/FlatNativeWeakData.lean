import Proof.NativeWeakEnergyData
import Proof.UniformWeakConormalComparison

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Quantitative actual weak energy data for every positive flat scalar center. -/
theorem flat_native_weak_energy_data (c : ℝ) (hc : 0 < c) :
    NativeWeakEnergyData (fun _ : X => c • (1:Mat)) (5*c⁻¹) c := by
  have hUE := TauCeti.PDE.uniformlyEllipticOn_smul_one (n:=I) (ballOpens:Set X)
    (fun _ : X => c) hc le_rfl (fun _ _ => ⟨le_rfl,le_rfl⟩)
  have hMeas : AEStronglyMeasurable (fun _ : X => c • (1:Mat)) ((volume:Measure X).restrict ballOpens) :=
    aestronglyMeasurable_const
  obtain ⟨hcoeff,hCoercive,hInv,hEnergy⟩ := exists_native_weak_estimates_of_uniformlyElliptic
    (fun _ : X => c • (1:Mat)) c c hUE hMeas
  exact ⟨hcoeff,hCoercive,hInv,hEnergy⟩

end ShrinkingSpheres

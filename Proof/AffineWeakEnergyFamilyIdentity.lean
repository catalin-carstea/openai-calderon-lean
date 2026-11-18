import Proof.ZeroEnergyAffineIdentity
import Proof.CommonSupportWeakEnergyRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal ContDiff Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL

private lemma affine_two_steps {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A B A0 A1 R : V) (r : ℝ) (hA : A = B+r • A1) (hB : B = A0+(1:ℝ) • R) :
    A = A0+r • A1+R := by
  rw [hA,hB,one_smul]
  module

/-- A true local affine coefficient family has exactly the same three native
    energy family decompositions. The common-support exterior plays no role. -/
theorem commonSupport_weakEnergy_affine_families
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (a a1 aR : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (haR : ContDiff ℝ ∞ aR) (c r : ℝ)
    (hField : ∀ p z,z ∈ (ballOpens:Set X) → a (p,z) = c • (1:Mat)+r • a1 (p,z)+aR (p,z)) :
    (∀ p,commonSupportFullWeakEnergy a ha p = TauCeti.PDE.energyFormH1L (flatCoefficientBound c)+
      r • commonSupportFullWeakEnergy a1 ha1 p+commonSupportFullWeakEnergy aR haR p) ∧
    (∀ p,commonSupportWeakEnergy a ha p = nativeCoefficientWeakEnergyL (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)+
      r • commonSupportWeakEnergy a1 ha1 p+commonSupportWeakEnergy aR haR p) ∧
    (∀ p,commonSupportZeroWeakEnergy a ha p = nativeZeroCoefficientEnergyL (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)+
      r • commonSupportZeroWeakEnergy a1 ha1 p+commonSupportZeroWeakEnergy aR haR p) := by
  let b : P × X → Mat := fun v => c • (1:Mat)+aR v
  have hb : ContDiff ℝ ∞ b := contDiff_const.add haR
  have hMain (p : P) (z : X) (hz : z ∈ (ballOpens:Set X)) :
      a (p,z) = b (p,z)+r • a1 (p,z) := by
    rw [hField p z hz]
    dsimp only [b]
    module
  have hBase (p : P) (z : X) (_ : z ∈ (ballOpens:Set X)) :
      b (p,z) = c • (1:Mat)+(1:ℝ) • aR (p,z) := by simp only [b,one_smul]
  refine ⟨?_,?_,?_⟩
  · intro p
    have hA := fullWeakEnergy_affine_eq (commonSupportEnergyMemLp a ha p)
      (commonSupportEnergyMemLp b hb p) (commonSupportEnergyMemLp a1 ha1 p) r (hMain p)
    have hB := fullWeakEnergy_affine_eq (commonSupportEnergyMemLp b hb p)
      (flatCoefficientBound c) (commonSupportEnergyMemLp aR haR p) 1 (hBase p)
    exact affine_two_steps (V:=BallH1 →L[ℝ] StrongDual ℝ BallH1)
      (commonSupportFullWeakEnergy a ha p) (commonSupportFullWeakEnergy b hb p)
      (TauCeti.PDE.energyFormH1L (flatCoefficientBound c))
      (commonSupportFullWeakEnergy a1 ha1 p) (commonSupportFullWeakEnergy aR haR p) r hA hB
  · intro p
    have hA := nativeWeakEnergy_affine_eq (commonSupportEnergyMemLp a ha p)
      (commonSupportEnergyMemLp b hb p) (commonSupportEnergyMemLp a1 ha1 p) r (hMain p)
    have hB := nativeWeakEnergy_affine_eq (commonSupportEnergyMemLp b hb p)
      (flatCoefficientBound c) (commonSupportEnergyMemLp aR haR p) 1 (hBase p)
    exact affine_two_steps (V:=BallH1 →L[ℝ] StrongDual ℝ BallH1Zero)
      (commonSupportWeakEnergy a ha p) (commonSupportWeakEnergy b hb p)
      (nativeCoefficientWeakEnergyL (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c))
      (commonSupportWeakEnergy a1 ha1 p) (commonSupportWeakEnergy aR haR p) r hA hB
  · intro p
    have hA := nativeZeroEnergy_affine_eq (commonSupportEnergyMemLp a ha p)
      (commonSupportEnergyMemLp b hb p) (commonSupportEnergyMemLp a1 ha1 p) r (hMain p)
    have hB := nativeZeroEnergy_affine_eq (commonSupportEnergyMemLp b hb p)
      (flatCoefficientBound c) (commonSupportEnergyMemLp aR haR p) 1 (hBase p)
    exact affine_two_steps (V:=BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero)
      (commonSupportZeroWeakEnergy a ha p) (commonSupportZeroWeakEnergy b hb p)
      (nativeZeroCoefficientEnergyL (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c))
      (commonSupportZeroWeakEnergy a1 ha1 p) (commonSupportZeroWeakEnergy aR haR p) r hA hB

end ShrinkingSpheres

import Proof.LowFirstRadialDerivative
import Proof.RadialTaylorLeftIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma commonSupport_lowRadial_eq_assembly
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (p : P) :
    commonSupportLowRadialErrorL a ha S hS hz p = radialErrorAssembly
      (commonSupportWeakConormalEndpoint a ha p)
      (negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz p)) fixedLowRadialL
      (fun j => negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz j p)) fixedSphereTangentialL := by
  have hT : (fun j => negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz j p)) =
      fun j => negativeBoundaryCoefficientMulL (tangentCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p) j) :=
    funext (fun j => commonSupport_negative_tangent_multiplier_eq a ha S hS hz j p)
  unfold commonSupportLowRadialErrorL actualLowRadialErrorL commonSupportWeakConormalEndpoint
  rw [commonSupport_negative_normal_multiplier_eq,hT]

/-- The named actual common-support radial Taylor remainder satisfies the
    same exact left identity with its genuine conormal and boundary maps. -/
theorem commonSupport_lowRadial_first_remainder_left_identity
    (a a1 : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (hz1 : ∀ p z,z ∉ S1 → a1 (p,z) = 0)
    (c r : ℝ) (p : P) (hc : c ≠ 0)
    (hM : (negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz p)).IsInvertible) :
    let N := commonSupportWeakConormalEndpoint a ha p
    let N1 := weakFirstConormalVariationL c (fun z => a1 (p,z)) (commonSupportEnergyMemLp a1 ha1 p)
    let M := negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz p)
    let M1 := negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a1 ha1 S1 hS1 hz1 p)
    M.comp (commonSupportLowRadialErrorL a ha S hS hz p-r • commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c p) =
      (N-c • fixedLowRadialL-r • N1)-
      (M-c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))-r • M1).comp fixedLowRadialL-
      ∑ j : I,(negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz j p)).comp (fixedSphereTangentialL j)-
      r • (M-c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))).comp
        (commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c p) := by
  dsimp only
  rw [commonSupport_lowRadial_eq_assembly]
  exact radialErrorAssembly_first_remainder_left_identity
    (commonSupportWeakConormalEndpoint a ha p)
    (weakFirstConormalVariationL c (fun z => a1 (p,z)) (commonSupportEnergyMemLp a1 ha1 p)) fixedLowRadialL
    (negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz p))
    (negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a1 ha1 S1 hS1 hz1 p))
    (fun j => negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz j p)) fixedSphereTangentialL c r hc hM

end ShrinkingSpheres

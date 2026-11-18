import Proof.ParallelScalarFirstForwardPacket
import Proof.ParallelScalarFirstMassIntegral
import Proof.ParallelScalarFirstDecomposition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma scalar_first_jet_mass_algebra {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : I → I → ℝ) (H : I → I → E) (u : E) (B L : I → E →L[ℝ] E)
    (mu : ℝ) (q : I → ℝ) :
    2*(∑ k : I,⟪∑ a : I,∑ b : I,A a b • H a b,
      mu • (L k).adjoint u+q k • (B k).adjoint u⟫_ℝ)=
    2*(∑ a : I,∑ b : I,∑ k : I,∑ t : Fin 2,
      (if t=0 then mu else q k)*A a b*⟪u,(if t=0 then L k else B k) (H a b)⟫_ℝ) := by
  have hPair (T : E →L[ℝ] E) (h : E) : ⟪h,T.adjoint u⟫_ℝ=⟪u,T h⟫_ℝ :=
    (T.adjoint_inner_right h u).trans (real_inner_comm _ _)
  simp only [inner_add_right,inner_sum,real_inner_smul_left,real_inner_smul_right,sum_inner]
  simp_rw [hPair]
  simp only [Fin.sum_univ_three,Fin.sum_univ_two,ite_true,show ¬(1:Fin 2)=0 by decide,ite_false]
  ring

def scalarFirstMassCoefficient {Y : Set X} {d : Data} {CF CT CB CS ε CE : ℝ}
    {P : PhysicalPrincipalData Y d CF CT} {WF : PhysicalFirstCommutatorPacket P CB CS ε}
    (p : EffectiveFirstForwardStrongHalfTwoJets WF CE) (t : Fin 2) (k : I) (x : X) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  if t=0 then p.low k k x else P.firstCovariantCoordinateHalfL k x

def scalarFirstMassHigher {Y : Set X} {d : Data} {CF CT CB CS ε CE : ℝ}
    {P : PhysicalPrincipalData Y d CF CT} {WF : PhysicalFirstCommutatorPacket P CB CS ε}
    (p : EffectiveFirstForwardStrongHalfTwoJets WF CE) (t : Fin 2) (k : I) (x : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  if t=0 then p.higher k k x else P.firstCovariantCoordinateHigherL k x

def scalarFirstMassTerm {Y : Set X} {d : Data} {CF CT CB CS ε CE : ℝ}
    {P : PhysicalPrincipalData Y d CF CT} {WF : PhysicalFirstCommutatorPacket P CB CS ε}
    (p : EffectiveFirstForwardStrongHalfTwoJets WF CE) (t : Fin 2) (a b k : I)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  halfCovariantSecondMassDensity d (scalarFirstMassWeight d t a b k) (scalarFirstMassCoefficient p t k)
    (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x))
    (fiveHalfCovariantDerivative d U (axis b)) (axis a) y

def scalarFirstMassTermComplexDensity {Y : Set X} {d : Data} {CF CT CB CS ε CE : ℝ}
    {P : PhysicalPrincipalData Y d CF CT} {WF : PhysicalFirstCommutatorPacket P CB CS ε}
    (p : EffectiveFirstForwardStrongHalfTwoJets WF CE) (t : Fin 2) (a b k : I)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  scalarFirstMassTerm p t a b k (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
    scalarFirstMassTerm p t a b k (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y

/-- The actual WF adjoint jet is moved by genuine adjunction before the
Green operation; no new adjoint family replaces that fixed packet. -/
theorem scalarFirstJetDensity_eq_mass_terms
    {Y : Set X} {d : Data} {CF CT CB CS ε CE : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (p : EffectiveFirstForwardStrongHalfTwoJets WF CE)
    (U : X → SphereSobolev (5/2:ℝ)) {y : X} (hy : y ∈ Y) :
    scalarFirstJetDensity P WF U y=2*(∑ a : I,∑ b : I,∑ k : I,∑ t : Fin 2,scalarFirstMassTerm p t a b k U y) := by
  let u := sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (U y)
  have hD (k : I) : WF.covariantCoordinateAdjointDerivative k k y
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y))=(p.low k k y).adjoint u := by
    rw [p.adjoint_graph k k y hy,ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply]
  have hAlg := scalar_first_jet_mass_algebra
    (fun a b => scalarPrincipalMatrix d.γ d.g₂ d.radius y a b)
    (fun a b => halfSectionCovariantDerivativeL d (fiveHalfCovariantDerivative d U (axis b)) y (axis a)) u
    (fun k => P.firstCovariantCoordinateHalfL k y) (fun k => p.low k k y)
    (metricDensity d.γ y) (fun k => fderiv ℝ (metricDensity d.γ) y (axis k))
  simpa only [scalarFirstJetDensity,scalarFiveHalfSecondSection,hD,scalarFirstMassTerm,
    halfCovariantSecondMassDensity,scalarFirstMassWeight,scalarFirstMassCoefficient,
    sphereSobolevInclusionL_trans_apply,sphereSobolevDualPairing,u] using hAlg

theorem scalarFirstJetComplexDensity_eq_mass_terms
    {Y : Set X} {d : Data} {CF CT CB CS ε CE : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (p : EffectiveFirstForwardStrongHalfTwoJets WF CE)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) {y : X} (hy : y ∈ Y) :
    scalarFirstJetComplexDensity P WF E y=
      2*(∑ a : I,∑ b : I,∑ k : I,∑ t : Fin 2,scalarFirstMassTermComplexDensity p t a b k E y) := by
  rw [scalarFirstJetComplexDensity,scalarFirstJetDensity_eq_mass_terms P WF p _ hy,
    scalarFirstJetDensity_eq_mass_terms P WF p _ hy]
  simp only [scalarFirstMassTermComplexDensity,Finset.sum_add_distrib,mul_add]

end ShrinkingSpheres.ParallelEnergy

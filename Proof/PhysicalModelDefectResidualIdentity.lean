import Proof.ModelDefectResidualRealIdentity
import Proof.PhysicalPotentialModelDefectIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

private lemma add_two_residual_decompositions (mu r i qr qi : ℝ)
    (sr si : I → I → ℝ) (fr fi : I → ℝ)
    (hr : mu*r=(∑ a : I,∑ b : I,sr a b)+mu*(∑ b : I,fr b)+mu*qr)
    (hi : mu*i=(∑ a : I,∑ b : I,si a b)+mu*(∑ b : I,fi b)+mu*qi) :
    mu*(r+i)=(∑ a : I,∑ b : I,(sr a b+si a b))+(∑ b : I,mu*(fr b+fi b))+mu*(qr+qi) := by
  simp only [Finset.sum_add_distrib,mul_add,←Finset.mul_sum]
  linarith only [hr,hi]

def PhysicalPrincipalData.modelDefectResidualDensity {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {φ : Field}
    (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  metricDensity d.γ y*(
    P.modelDefectResidualRealForm (fun p => (E.representative p).re)
      (Complex.reCLM.contDiff.comp E.representativeSmooth) y+
    P.modelDefectResidualRealForm (fun p => (E.representative p).im)
      (Complex.imCLM.contDiff.comp E.representativeSmooth) y)

theorem PhysicalPrincipalData.modelDefectResidualDensity_decomposition
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) {y : X} (hy : y ∈ Y)
    (W : PhysicalPotentialQuarticData P y CG CK) :
    P.modelDefectResidualDensity E y=
      (∑ a : I,∑ b : I,physicalScalarModelDefectSecondDensity d E
        (scalarPrincipalDensityWeight d.γ d.g₂ d.radius a b) a b y)+
      (∑ b : I,P.firstModelDefectDensity E b y)+P.potentialModelDefectDensity E y W := by
  let Gr := fun p => (E.representative p).re
  let Gi := fun p => (E.representative p).im
  let hGr := Complex.reCLM.contDiff.comp E.representativeSmooth
  let hGi := Complex.imCLM.contDiff.comp E.representativeSmooth
  let sr := fun a b => scalarModelDefectSecondDensity d
    (scalarPrincipalDensityWeight d.γ d.g₂ d.radius a b) (ambientSobolevSection 2 (by norm_num) Gr hGr)
    (ambientHigherSobolevSection 3 (by norm_num) Gr hGr) (axis a) (axis b) y
  let si := fun a b => scalarModelDefectSecondDensity d
    (scalarPrincipalDensityWeight d.γ d.g₂ d.radius a b) (ambientSobolevSection 2 (by norm_num) Gi hGi)
    (ambientHigherSobolevSection 3 (by norm_num) Gi hGi) (axis a) (axis b) y
  let fr := fun b => firstModelDefectRealForm d (P.firstCovariantCoordinateCoarseL b) Gr hGr b y
  let fi := fun b => firstModelDefectRealForm d (P.firstCovariantCoordinateCoarseL b) Gi hGi b y
  have hr := P.modelDefectResidualRealForm_decomposition hY hΩ hd hK Gr hGr hy W
  have hi := P.modelDefectResidualRealForm_decomposition hY hΩ hd hK Gi hGi hy W
  have hh := add_two_residual_decompositions (metricDensity d.γ y)
    (P.modelDefectResidualRealForm Gr hGr y) (P.modelDefectResidualRealForm Gi hGi y)
    (P.potentialModelDefectRealForm W Gr hGr) (P.potentialModelDefectRealForm W Gi hGi) sr si fr fi hr hi
  simpa only [PhysicalPrincipalData.modelDefectResidualDensity,physicalScalarModelDefectSecondDensity,
    PhysicalPrincipalData.firstModelDefectDensity,PhysicalPrincipalData.potentialModelDefectDensity,
    HarmonicTestExpansion.realSobolevSection,HarmonicTestExpansion.imagSobolevSection,
    sr,si,fr,fi,Gr,Gi,hGr,hGi] using hh

end ShrinkingSpheres

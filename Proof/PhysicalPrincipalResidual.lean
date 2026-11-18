import Proof.UniformPhysicalPrincipalData
import Proof.ActualPrincipalResidualCollection
import Proof.CanonicalRaisingSectionOutput
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT : ℝ}

/-- The complete actual principal residual as a genuine balanced section.
The real scalar rQ second-base block is explicit, while the four endpoint
product terms preserve the physical first-adjoint error choices. -/
def residualValue (D : PhysicalPrincipalData Y d CF CT) (U : X → SphereSobolev 2) (y : X) :
    SphereSobolev (-(1/2:ℝ)) :=
  let u := U y
  let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
  sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
    (d.radius y • (∑ i : I,∑ j : I,q i j • modelPlusTensorSection d U y i j)+
      (2:ℝ) • (∑ i : I,∑ j : I,(q i j-(if i=j then 1 else 0)) • flatOneRaisingL i (highSectionModelPlus d U y j))+
      pureAngularPrincipalPerturbationL d y u+
      principalFirstRemainderSection d D.adjoint D.center U y+principalCovariantRemainderSection d D.tensor U y+
      principalRaisingCorrectionPerturbationL d y (sphereSobolevInclusionL 2 1 (by norm_num) u)+
      principalDegreeCorrectionCrossL d y (sphereSobolevInclusionL 2 1 (by norm_num) u)+
      principalCorrectionProductL 0 d y (sphereSobolevInclusionL 2 0 (by norm_num) u))+
  D.first.principalRaisingCrossL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)+
  D.first.principalDegreeCrossL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)+
  D.first.principalCorrectionCrossL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)+
  D.first.radiusPrincipalProductL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)

/-- The uniform coefficient package yields the physical second-trace witness
and the complete residual on the SAME canonical test component. The raising
term is exactly the model output already used by coercivity. -/
theorem canonical_principal_residual (D : PhysicalPrincipalData Y d CF CT)
    {Ω : Set X} (hY : IsOpen Y) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[nhds z] (fun _ => (1:ℝ)))
    {φ : Field} (hφ : Test Y d.γ d.frame φ)
    (E : HarmonicTestExpansion Y d.γ d.frame φ) (L : ℂ →L[ℝ] ℝ)
    (C : AngularComponentData E d.radius L) :
    let F := fun p => L (E.representative p)
    let hF : ContDiff ℝ ∞ F := L.contDiff.comp E.representativeSmooth
    let U := ambientSobolevSection 2 (by norm_num) F hF
    ∃ P : SecondTraceSectionOutput Y d D.adjoint D.center D.tensor φ L F hF,
      ∀ y ∈ Y,sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (expandedPrincipalSection d D.adjoint D.center D.tensor U
          (fun j => ambientSobolevSection 1 (by norm_num) (P.representative j) (P.smooth j)) y-
          (2:ℝ) • sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (C.raisingOutput y)-
          firstCorrectionCrossRemainderL Q d y (sphereSobolevInclusionL 2 1 (by norm_num) (U y)))=
        D.residualValue U y := by
  dsimp only
  let F := fun p => L (E.representative p)
  have hF : ContDiff ℝ ∞ F := L.contDiff.comp E.representativeSmooth
  let U := ambientSobolevSection 2 (by norm_num) F hF
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  have hSource : ∀ x ∈ Y,∀ w : UnitSphere,F (x,w.val)=L (φ (x,frameVector d.frame x w.val)) :=
    fun x hx w => congrArg L (E.representativeEq x hx w)
  obtain ⟨P⟩ := D.physical φ hφ.1 hφ.2.1 L F hF hSource
  refine ⟨P,?_⟩
  intro y hy
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hγ : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he := fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame := fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hT := C.canonical_raising_section_eq hY hγ hK he hFrame hφ.1 Q hQ hy
  have hT' : (∑ i : I,flatOneRaisingL i (highSectionModelPlus d U y i))=Z (C.raisingOutput y) :=
    (Z.apply_symm_apply _).symm.trans (congrArg Z hT)
  have hSym (a b : I) : principal d.γ d.g₂ y a b=principal d.γ d.g₂ y b a := by
    have hs := Matrix.isHermitian_iff_isSymm.mp (hd.principal_properties hK (hSub hy)).1.isHermitian
    exact congrArg (fun Q : Mat => Q b a) hs
  have h := P.principal_residual_balanced Q hQ D.first hy (hd.2.2.2.2.1.2 y hy).1.ne' hSym (hFrame y hy)
  dsimp only at h
  let Inc := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  let Actual := expandedPrincipalSection d D.adjoint D.center D.tensor U
    (fun j => ambientSobolevSection 1 (by norm_num) (P.representative j) (P.smooth j)) y
  let J := firstCorrectionCrossRemainderL Q d y (sphereSobolevInclusionL 2 1 (by norm_num) (U y))
  have hLeft : Inc (Actual-(2:ℝ) • Z (C.raisingOutput y)-J)=
      Inc (Actual-(2:ℝ) • (∑ i : I,flatOneRaisingL i (highSectionModelPlus d U y i))-J) :=
    congrArg (fun t : SphereSobolev 0 => Inc (Actual-(2:ℝ) • t-J)) hT'.symm
  exact hLeft.trans h
end PhysicalPrincipalData
end ShrinkingSpheres

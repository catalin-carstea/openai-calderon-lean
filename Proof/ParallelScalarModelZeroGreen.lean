import Proof.ParallelScalarModelPairedMass
import Proof.ParallelScalarModelDegreeCancel
import Proof.ParallelScalarModelDegreeSections
import Proof.ParallelScalarModelSkew
import Proof.ParallelScalarModelRaising

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

/-- The actual raising degree pair is reduced together. The original
symmetric scalar contraction removes the degree-gradient square. -/
theorem scalar_model_degree_pair_reduction {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hA : ∀ j : I,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A j)=
      (flatHalfRaisingL j).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (q : I → I → X → ℝ) (hq : ∀ a b,ContDiffOn ℝ ∞ (q a b) Y)
    (hSym : ∀ y ∈ Y,∀ a b,q a b y=q b a y) (c : I)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (hU0 : ∀ x ∉ S,U x=0) :
    let C0 := fun x => (framedRaisingHalfL d x (axis c)).adjoint
    let C1 := fun x => framedRaisingHalfL d x (axis c)
    let Ch0 := scalarModelRaisingAdjointHigher A d c
    let Ch1 := fun x => framedRaisingHigherL d x (axis c)
    let U0 := scalarModelDegreeSection U
    let U1 := scalarModelShiftedDegreeSection U
    let H := fun b : I => fiveHalfCovariantDerivative d U (axis b)
    IntegrableOn (pairedHalfMassDensity d q C0 C1 U0 U1 H) Y ∧
    IntegrableOn (pairedHalfMassRemainder d q C0 C1 Ch0 Ch1 U0 U1 H) Y ∧
    (∫ x in Y,pairedHalfMassDensity d q C0 C1 U0 U1 H x)=
      ∫ x in Y,pairedHalfMassRemainder d q C0 C1 Ch0 Ch1 U0 U1 H x := by
  let Dmap : SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) := sphereSobolevShiftedDegreeL (5/2:ℝ)
  have hD0 : ContDiff ℝ ∞ (scalarModelDegreeSection U) := Dmap.contDiff.comp hU
  have hD1 : ContDiff ℝ ∞ (scalarModelShiftedDegreeSection U) :=
    hD0.sub ((sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).contDiff.comp hU)
  have hH (b : I) := contDiff_supported_gradedSphereSectionCovariantDerivative hY (5/2:ℝ) d hg
    hK he U hU S hS.isClosed hSY hU0 (axis b)
  refine paired_half_mass_reduction hY d hg hK he q hq
    (fun x => (framedRaisingHalfL d x (axis c)).adjoint) (fun x => framedRaisingHalfL d x (axis c))
    (scalarModelRaisingAdjointHigher A d c) (fun x => framedRaisingHigherL d x (axis c))
    (scalarModelRaisingAdjoint_smooth hd c) (hd.framedRaisingHalf_smooth (axis c)).1
    (fun x _ => scalarModelRaisingAdjointHigher_balanced A d c x hA)
    (fun x _ => framedRaisingHalf_balanced d x (axis c))
    (scalarModelDegreeSection U) (scalarModelShiftedDegreeSection U)
    (fun b : I => fiveHalfCovariantDerivative d U (axis b)) hD0 hD1 (fun b => (hH b).1)
    S hS hSY (fun x hx => by simp only [scalarModelDegreeSection,hU0 x hx,map_zero])
    (fun x hx => by simp only [scalarModelShiftedDegreeSection,scalarModelDegreeSection,hU0 x hx,map_zero,sub_self])
    (fun b => (hH b).2) ?_
  intro x hx
  exact scalar_model_degree_section_gradient_cancel Q hQ d U x
    (hU.differentiable (by simp) x) (fun a b => q a b x) (hSym x hx) c

end ShrinkingSpheres.ParallelEnergy

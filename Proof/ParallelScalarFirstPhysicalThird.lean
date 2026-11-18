import Proof.ParallelScalarFirstTripleIntegral
import Proof.ParallelScalarFirstCurvature
import Proof.EffectiveFirstScalarDriftCommutator
import Proof.ParallelScalarFirstPairAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The SAME scalar-weighted symmetric complete-first coefficient. -/
def scalarFirstSymmetricCoefficient {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (w : X → ℝ) (b : I) (y : X) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  w y • (P.firstCovariantCoordinateHalfL b y+(P.firstCovariantCoordinateHalfL b y).adjoint)

def scalarFirstSymmetricHigher {Y : Set X} {d : Data} {CF CT CB CS ε : ℝ}
    {P : PhysicalPrincipalData Y d CF CT} (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (w : X → ℝ) (b : I) (y : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  w y • (P.firstCovariantCoordinateHigherL b y+WF.covariantCoordinateAdjointHigher b y)

/-- Integrated leading scalar/first reduction for the actual complete
coefficient and actual physical curvature. Its endpoint premise is the
checked genuine balanced forward graph, available uniformly in the
original frozen hypotheses. The adjoint is the caller's fixed WF. -/
theorem physical_scalar_first_symmetric_third_reduction
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (hForward : ∀ y ∈ Y,∀ b : I,
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        (P.firstCovariantCoordinateHigherL b y)=
      (P.firstCovariantCoordinateHalfL b y).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (w : X → ℝ) (hw : ContDiffOn ℝ ∞ w Y) (k : I)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (hU0 : ∀ x ∉ S,U x=0) (a b c : X) :
    let C := scalarFirstSymmetricCoefficient P w k
    let Ch := scalarFirstSymmetricHigher WF w k
    let H := fiveHalfCovariantDerivative d U
    let R := fun a b y => frameCurvatureSobolevL (3/2:ℝ) d.γ d.frame y a b
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y))
    IntegrableOn (halfCovariantThirdDensity d (metricDensity d.γ) C H a b c) Y ∧
      IntegrableOn (halfCovariantThirdRemainder d (metricDensity d.γ) C Ch H R a b c) Y ∧
      2*(∫ x in Y,halfCovariantThirdDensity d (metricDensity d.γ) C H a b c x)=
        ∫ x in Y,halfCovariantThirdRemainder d (metricDensity d.γ) C Ch H R a b c x := by
  let C := scalarFirstSymmetricCoefficient P w k
  let Ch := scalarFirstSymmetricHigher WF w k
  let H := fiveHalfCovariantDerivative d U
  let R := fun a b y => frameCurvatureSobolevL (3/2:ℝ) d.γ d.frame y a b
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y))
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hDrift := hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK k
  have hCL : ContDiffOn ℝ ∞ C Y := hw.smul
    ((P.firstCovariantCoordinateHalfL_smooth hd hY hΩ hK k hDrift).add
      (P.firstCovariantCoordinateAdjoint_smooth hd hY hΩ hK k hDrift))
  have hCompatible (y : X) (hy : y ∈ Y) :
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Ch y)=
      (C y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
    exact balanced_symmetric_scalar_graph _ _ _ _ _ (w y) (hForward y hy k)
      (WF.covariantCoordinateAdjointHigher_balanced k hy)
  have hSym (y : X) (hy : y ∈ Y) : (C y).adjoint=C y := by
    exact symmetric_scalar_adjoint _ _
  have hHS (v : X) : ContDiff ℝ ∞ (H v) :=
    (contDiff_supported_gradedSphereSectionCovariantDerivative hY (5/2:ℝ) d hg hK he U hU
      S hS.isClosed hSY hU0 v).1
  have hH0 (v x : X) (hx : x ∉ S) : H v x=0 :=
    (contDiff_supported_gradedSphereSectionCovariantDerivative hY (5/2:ℝ) d hg hK he U hU
      S hS.isClosed hSY hU0 v).2 x hx
  exact symmetric_half_covariant_third_reduction hY d hg hK he (metricDensity d.γ)
    (hg.contDiffOn_density hK) C Ch hCL hCompatible hSym H hHS S hS hSY hH0 R
    (fun y hy v z => fiveHalfCovariantDerivative_commutator hY d hg hK he hFrame U hU hy v z) a b c

end ShrinkingSpheres.ParallelEnergy

import Proof.ParallelFirstSelfBalancedWeakCurvature
import Proof.ParallelFirstSelfCompleteAdjointJet
import Proof.ParallelFirstSelfCoreSplit
import Proof.HalfCovariantOperatorSourceProduct
import Proof.EffectiveFirstAdjointFiveHalfMeasurability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

def firstSelfAdjointSourceDerivative (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (b i : I) (y : X) : SphereSobolev (1/2:ℝ) :=
  balancedPositiveHalfDerivative d (WF.covariantAdjointLowSection U b)
    (P.firstCovariantAdjointFiveHalfSection W U b) y (axis i)

lemma firstSelfAdjointSource_higher_graph (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (b : I) {y : X} (hy : y ∈ Y) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
      (P.firstCovariantAdjointFiveHalfSection W U b y)=WF.covariantAdjointLowSection U b y := by
  have h := DFunLike.congr_fun (P.firstCovariantCoordinateAdjointFiveHalfL_inclusion hy (W y hy) b
    (WF.covariantCoordinateAdjointHigher b y) (WF.covariantCoordinateAdjointHigher_balanced b hy)) (U y)
  simpa only [PhysicalPrincipalData.firstCovariantAdjointFiveHalfSection,dif_pos hy,
    PhysicalFirstCommutatorPacket.covariantAdjointLowSection,ContinuousLinearMap.comp_apply] using h

lemma firstSelfAdjointSourceDerivative_weak_graph (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (b i : I) {y : X} (hy : y ∈ Y) :
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (firstSelfAdjointSourceDerivative P WF W U b i y)=
        weakHalfSourceCovariantDerivative d (WF.covariantAdjointLowSection U b) y (axis i) :=
  balanced_positive_half_derivative_weak_graph d _ _ y (axis i)
    (firstSelfAdjointSource_higher_graph P WF W U b hy)

lemma first_self_adjoint_low_source_weak_product
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y) (b i : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) {y : X} (hy : y ∈ Y) :
    weakHalfSourceCovariantDerivative d (WF.covariantAdjointLowSection U b) y (axis i)=
      (P.firstCovariantCoordinateHalfL b y).adjoint
        (halfSectionCovariantDerivativeL d
          (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y (axis i))+
      WF.effectiveAdjointCovariantDerivative b i y
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)) := by
  let V := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
  let A := WF.covariantCoordinateAdjointHigher b
  let C := fun x => (P.firstCovariantCoordinateHalfL b x).adjoint
  let Z := WF.covariantAdjointLowSection U b
  let I0 := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hV : ContDiffOn ℝ ∞ V Y := (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).contDiff.comp_contDiffOn hU
  have hA := WF.covariantCoordinateAdjointHigher_smooth hd b hw
  have hZ : ContDiffOn ℝ ∞ Z Y := hA.clm_apply hV
  have hNear : (fun x => I0 (Z x))=ᶠ[𝓝 y]
      (fun x => C x (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V x))) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact DFunLike.congr_fun (WF.covariantCoordinateAdjointHigher_balanced b hx) (V x)
  have hZD := ((hZ.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  have hDer := (I0.hasFDerivAt.comp y hZD).congr_of_eventuallyEq hNear.symm
  have hFD := DFunLike.congr_fun hDer.fderiv (axis i)
  have hRaw := half_covariant_operator_source_product d C A V y (axis i)
    ((P.firstCovariantCoordinateAdjoint_smooth hd hY hΩ hK b hw).contDiffAt (hY.mem_nhds hy))
    (hV.contDiffAt (hY.mem_nhds hy))
  rw [hFD] at hRaw
  exact hRaw

/-- The canonical balanced source derivative differs from the selected
leading row by the genuine complete adjoint coefficient jet. -/
lemma firstSelfAdjointSourceDerivative_eq_leading_add_jet
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y) (b i : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) {y : X} (hy : y ∈ Y)
    (H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hH : WF.effectiveAdjointCovariantDerivative b i y=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H) :
    firstSelfAdjointSourceDerivative P WF W U b i y=
      WF.covariantCoordinateAdjointHigher b y (firstSelfSourceDerivative d U y (axis i))+
      H (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)) := by
  apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  rw [firstSelfAdjointSourceDerivative_weak_graph P WF W U b i hy,
    first_self_adjoint_low_source_weak_product hY hΩ hd hK P WF U hU b i hw hy,hH,map_add]
  have hA := DFunLike.congr_fun (WF.covariantCoordinateAdjointHigher_balanced b hy)
    (firstSelfSourceDerivative d U y (axis i))
  simp only [ContinuousLinearMap.comp_apply,firstSelfSourceDerivative_inclusion d U
    ((hU.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))] at hA
  simp only [ContinuousLinearMap.comp_apply,hA]

end ShrinkingSpheres.ParallelEnergy

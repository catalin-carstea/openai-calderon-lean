import Proof.UniformPrincipalModelCoordinateData
import Proof.FramedRaisingSecondCovariantGraph

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

def principalModelCoordinateCoarseL (d : Data) (b : I) (x : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  principalModelDegreeCoordinateWeight d b x • sphereSobolevDegreeL+
    ∑ a : I,principalModelRaisingCoordinateWeight d a b x •
      framedFlatRaisingSobolevL 1 d.γ d.frame x (axis a)

def principalModelCoordinateFirstCoarseJet (d : Data) (b i : I) (x : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  fderiv ℝ (principalModelDegreeCoordinateWeight d b) x (axis i) • sphereSobolevDegreeL+
    ∑ a : I,(principalModelRaisingCoordinateWeight d a b x • framedRaisingFirstCoarseJet d i a x+
      fderiv ℝ (principalModelRaisingCoordinateWeight d a b) x (axis i) •
        framedFlatRaisingSobolevL 1 d.γ d.frame x (axis a))

def principalModelCoordinateSecondCoarseJet (d : Data) (b i j : I) (x : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  fderiv ℝ (fun y => fderiv ℝ (principalModelDegreeCoordinateWeight d b) y (axis i)) x (axis j) •
      sphereSobolevDegreeL+
    ∑ a : I,((principalModelRaisingCoordinateWeight d a b x • framedRaisingSecondCoarseJet d i j a x+
      fderiv ℝ (principalModelRaisingCoordinateWeight d a b) x (axis j) • framedRaisingFirstCoarseJet d i a x)+
      (fderiv ℝ (principalModelRaisingCoordinateWeight d a b) x (axis i) • framedRaisingFirstCoarseJet d j a x+
        fderiv ℝ (fun y => fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i)) x (axis j) •
          framedFlatRaisingSobolevL 1 d.γ d.frame x (axis a)))

lemma Admissible.principalModelCoordinateCoarse_smooth {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (b i : I) :
    ContDiffOn ℝ ∞ (principalModelCoordinateCoarseL d b) Y ∧
      ContDiffOn ℝ ∞ (principalModelCoordinateFirstCoarseJet d b i) Y := by
  have hD := hd.contDiffOn_principalModelDegreeCoordinateWeight hY hK b
  have hDD := contDiffOn_coordDeriv hY hD i
  have hR (a : I) := hd.contDiffOn_principalModelRaisingCoordinateWeight hK a b
  have hRD (a : I) := contDiffOn_coordDeriv hY (hR a) i
  have hF (a : I) := (hd.framedRaisingHalf_smooth (axis a)).2.2
  have hS (a : I) := hd.framedRaisingFirstCoarseJet_smooth hΩ hK i a
  constructor
  · exact (hD.smul contDiffOn_const).add (ContDiffOn.sum (fun a _ => (hR a).smul (hF a)))
  · exact (hDD.smul contDiffOn_const).add (ContDiffOn.sum (fun a _ =>
      ((hR a).smul (hS a)).add ((hRD a).smul (hF a))))

/-- This coarse family has the SAME actual physical model half endpoint. -/
lemma Admissible.principalModelCoordinate_coarse_low_compatible {Y Ω : Set X}
    (hY : IsOpen Y) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {x : X} (hx : x ∈ Y) (b : I) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (principalModelCoordinateCoarseL d b x)=
      (principalModelCoordinateHalfL d x b).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  change _ = (∑ j : I,d.frame x j b • principalModelFirstDerivativeHalfL d x j).comp _
  rw [hd.principalModelFirstDerivative_coordinate_eq hY hx b]
  apply ContinuousLinearMap.ext
  intro u
  have hD := DFunLike.congr_fun degreeHalfL_coarse u
  have hR (a : I) := DFunLike.congr_fun (framedRaisingHalfL_coarse d x (axis a)) u
  simp only [ContinuousLinearMap.comp_apply] at hD hR
  simp only [principalModelCoordinateCoarseL,ContinuousLinearMap.comp_apply,
    _root_.add_apply,_root_.smul_apply,_root_.sum_apply,map_add,map_smul,map_sum,hD,hR]

lemma principalModelCoordinate_coarse_high_compatible (d : Data) (x : X) (b : I) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (principalModelCoordinateHigherL d x b)=
      (principalModelCoordinateCoarseL d b x).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hD := DFunLike.congr_fun degreeHigherL_coarse u
  have hR (a : I) := DFunLike.congr_fun (framedRaisingHigherL_coarse d x (axis a)) u
  simp only [ContinuousLinearMap.comp_apply] at hD hR
  simp only [principalModelCoordinateHigherL,principalModelCoordinateCoarseL,ContinuousLinearMap.comp_apply,
    _root_.add_apply,_root_.smul_apply,_root_.sum_apply,map_add,map_smul,map_sum,hD,hR]

end ShrinkingSpheres

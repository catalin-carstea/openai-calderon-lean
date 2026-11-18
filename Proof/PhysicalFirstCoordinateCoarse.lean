import Proof.PrincipalModelCoordinateCoarse
import Proof.PrincipalFirstCorrectionCoordinateCoarse
import Proof.PrincipalFirstErrorCoordinateCoarse
import Proof.PrincipalFirstCorrectionCoordinateContraction
import Proof.ActualFrameFirstAdjointError

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def PhysicalPrincipalData.firstDerivativeCoordinateCoarseL
    {Y : Set X} {d : Data} {CF CT : ℝ} (P : PhysicalPrincipalData Y d CF CT) (b : I) (x : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  principalModelCoordinateCoarseL d b x+principalFirstCorrectionCoordinateCoarseL d b x+
    principalFirstErrorCoordinateCoarseL d P.adjoint P.center b x

lemma PhysicalPrincipalData.firstDerivativeCoordinate_coarse_low_compatible
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hY : IsOpen Y) {x : X} (hx : x ∈ Y) (b : I) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (P.firstDerivativeCoordinateCoarseL b x)=
      (P.firstDerivativeCoordinateHalfL x b).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  have hFrame := hd.1.2.2.2.2.2.2.2 x (hd.2.1.center_mem hx)
  rw [P.firstDerivativeCoordinateHalfL_correction_split]
  change _ = (principalModelCoordinateHalfL d x b+principalFirstCorrectionCoordinateHalfL d x b+
    P.first.principalFirstErrorCoordinateHalfL x b).comp _
  unfold PhysicalPrincipalData.firstDerivativeCoordinateCoarseL
  rw [ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_add,
    ContinuousLinearMap.add_comp,ContinuousLinearMap.add_comp,
    hd.principalModelCoordinate_coarse_low_compatible hY hx b,
    principalFirstCorrectionCoordinate_coarse_low_compatible d x hFrame b,
    P.first_error_coordinate_coarse_compatible hx hFrame b]

lemma Admissible.principalFirstCorrectionCoordinateCoarse_smooth
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hK : 0 < K) (b : I) :
    ContDiffOn ℝ ∞ (principalFirstCorrectionCoordinateCoarseL d b) Y := by
  apply ContDiffOn.sum
  intro a _
  have hPrimitive : ContDiffOn ℝ ∞ (physicalFirstCorrectionCoarseFamily d (axis a)) Y :=
    (hd.contDiffOn_physicalFirstCorrectionAtL hY hΩ hK 0 (axis a)).clm_comp contDiffOn_const
  exact (hd.contDiffOn_principalFirstErrorCoordinateWeight hK a b).smul hPrimitive

lemma PhysicalPrincipalData.firstErrorCoordinateCoarse_smooth
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) (hK : 0 < K) (b : I) :
    ContDiffOn ℝ ∞ (principalFirstErrorCoordinateCoarseL d P.adjoint P.center b) Y := by
  apply ContDiffOn.sum
  intro a _
  exact (hd.contDiffOn_principalFirstErrorCoordinateWeight hK a b).smul
    (contDiffOn_actualFirstAdjointErrorFamily (axis a) hY hΩ hSub hd.1 hK
      hd.2.2.2.2.1.1 (fun x hx => (hd.2.2.2.2.1.2 x hx).1) P.adjoint (P.center a)
      P.adjoint_smooth (P.center_smooth a))

lemma PhysicalPrincipalData.firstDerivativeCoordinateCoarse_smooth
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) (hK : 0 < K) (b : I) :
    ContDiffOn ℝ ∞ (P.firstDerivativeCoordinateCoarseL b) Y :=
  (((hd.principalModelCoordinateCoarse_smooth hY hΩ hK b 0).1).add
    (hd.principalFirstCorrectionCoordinateCoarse_smooth hY hΩ hK b)).add
      (P.firstErrorCoordinateCoarse_smooth hd hY hΩ hSub hK b)

end ShrinkingSpheres

import Proof.UniformPhysicalFirstCommutatorPacket
import Proof.FrameAdjointEndpointCombination
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
namespace PhysicalFirstCommutatorPacket
variable {Y : Set X} {d : Data} {CF CT CB CS ε : ℝ}
  {P : PhysicalPrincipalData Y d CF CT}

def coordinateAdjointHigher (W : PhysicalFirstCommutatorPacket P CB CS ε) (b : I) (x : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  ∑ j : I,d.frame x j b • W.adjointHigh j x

lemma coordinateAdjointHigher_balanced (W : PhysicalFirstCommutatorPacket P CB CS ε)
    (b : I) {x : X} (hx : x ∈ Y) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (W.coordinateAdjointHigher b x)=
      (P.firstDerivativeCoordinateHalfL x b).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  finite_real_adjoint_balanced_combination _ _ (fun j => P.firstDerivativeHalfL x j)
    (fun j => W.adjointHigh j x) (fun j => W.adjoint_graph j x hx) (fun j => d.frame x j b)

lemma coordinateAdjointHigher_smooth {Ω : Set X} (W : PhysicalFirstCommutatorPacket P CB CS ε)
    {m : ℕ} {K ρ c₀ floor : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (b : I) :
    ContDiffOn ℝ ∞ (W.coordinateAdjointHigher b) Y := by
  apply ContDiffOn.sum
  intro j _
  exact ((EuclideanSpace.proj (𝕜:=ℝ) b).contDiff.comp_contDiffOn
    ((hd.1.2.2.2.2.2.2.1 j).mono (fun x hx => hd.2.1.center_mem hx))).smul (W.adjoint_smooth j)

lemma norm_coordinateAdjointHigher_le {Ω : Set X} (W : PhysicalFirstCommutatorPacket P CB CS ε)
    {m : ℕ} {K ρ c₀ floor : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (b : I) {x : X} (hx : x ∈ Y) :
    ‖W.coordinateAdjointHigher b x‖ ≤ (3*K*CB)*ε/beta d.γ d.radius x := by
  have hFrame := hd.1.2.2.2.2.2.2.2 x (hd.2.1.center_mem hx)
  exact (norm_weighted_sum_three_le (fun j => d.frame x j b) (fun j => W.adjointHigh j x)
    K (CB*ε/beta d.γ d.radius x) (zero_le_one.trans hK)
    (fun j => hd.1.1.frame_component_abs_le hK d.frame (hd.2.1.center_mem hx) hFrame j b)
    (fun j => W.adjoint_bound j x hx)).trans_eq (by ring)
end PhysicalFirstCommutatorPacket

lemma PhysicalPrincipalData.firstDerivativeCoordinateAdjoint_smooth {Y Ω : Set X} {d : Data} {CF CT : ℝ}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} (P : PhysicalPrincipalData Y d CF CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (b : I) :
    ContDiffOn ℝ ∞ (fun x => (P.firstDerivativeCoordinateHalfL x b).adjoint) Y := by
  let Adj : (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) →L[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  exact Adj.contDiff.comp_contDiffOn (P.firstDerivativeCoordinateHalfL_smooth hY hΩ hd hK b)
end ShrinkingSpheres

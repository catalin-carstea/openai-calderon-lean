import Proof.FullFirstBalancedEndpoints
import Proof.CoordinateTensors
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT : ℝ}

def firstDerivativeCoordinateHalfL (D : PhysicalPrincipalData Y d CF CT) (y : X) (i : I) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ j : I,d.frame y j i • D.firstDerivativeHalfL y j

def firstDerivativeCoordinateHigherL (D : PhysicalPrincipalData Y d CF CT) (y : X) (i : I) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  ∑ j : I,d.frame y j i • D.firstDerivativeHigherL y j

/-- The coordinate coefficients are the SAME physical first-base contraction. -/
lemma first_derivative_coordinate_contraction (D : PhysicalPrincipalData Y d CF CT) (y : X)
    (V : X →L[ℝ] SphereSobolev (1/2:ℝ)) :
    (∑ j : I,D.firstDerivativeHalfL y j (V (d.frame y j)))=
      ∑ i : I,D.firstDerivativeCoordinateHalfL y i (V (axis i)) := by
  have hV (j : I) : V (d.frame y j)=∑ i : I,d.frame y j i • V (axis i) := by
    calc
      V (d.frame y j)=V (∑ i : I,d.frame y j i • axis i) := congrArg V (axis_expansion (d.frame y j)).symm
      _=∑ i : I,d.frame y j i • V (axis i) := by simp only [map_sum,map_smul]
  simp only [hV,firstDerivativeCoordinateHalfL,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  exact Finset.sum_comm

lemma firstDerivativeCoordinateHalfL_smooth {Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (D : PhysicalPrincipalData Y d CF CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (i : I) :
    ContDiffOn ℝ ∞ (fun y => D.firstDerivativeCoordinateHalfL y i) Y := by
  apply ContDiffOn.sum
  intro j _
  exact ((EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.comp_contDiffOn
    ((hd.1.2.2.2.2.2.2.1 j).mono (fun x hx => hd.2.1.center_mem hx))).smul
      (D.firstDerivativeHalfL_smooth hY hΩ hd hK j)

lemma firstDerivativeCoordinate_balanced (D : PhysicalPrincipalData Y d CF CT) (y : X)
    (hPair : ∀ j,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (D.firstDerivativeHigherL y j)=
      (D.firstDerivativeHalfL y j).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) (i : I) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (D.firstDerivativeCoordinateHigherL y i)=
      (D.firstDerivativeCoordinateHalfL y i).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [firstDerivativeCoordinateHalfL,firstDerivativeCoordinateHigherL,ContinuousLinearMap.comp_apply,
    _root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  exact Finset.sum_congr rfl (fun j _ => congrArg (fun v => d.frame y j i • v) (DFunLike.congr_fun (hPair j) u))

lemma norm_firstDerivativeCoordinateHalfL_small {Ω : Set X} (hΩ : IsOpen Ω) {m : ℕ}
    (hm : 2 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (D : PhysicalPrincipalData Y d CF CT) (hCF : 0 ≤ CF)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (i : I) :
    let CB := 108*(K+1)*K^2+540*K^2*radialDriftSobolevBound (-(1/2:ℝ))+
      54*(K+1)*K^2*(firstCorrectionGradeBound (-(1/2:ℝ)) K (M ⟨1,by omega⟩)+CF)
    ‖D.firstDerivativeCoordinateHalfL y i‖ ≤ (3*K*CB)*ε/beta d.γ d.radius y := by
  let CB := 108*(K+1)*K^2+540*K^2*radialDriftSobolevBound (-(1/2:ℝ))+
    54*(K+1)*K^2*(firstCorrectionGradeBound (-(1/2:ℝ)) K (M ⟨1,by omega⟩)+CF)
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hN := norm_weighted_sum_three_le (fun j : I => d.frame y j i)
    (fun j => D.firstDerivativeHalfL y j) K (CB*ε/beta d.γ d.radius y) (zero_le_one.trans hK)
    (fun j => hd.1.1.frame_component_abs_le hK d.frame (hd.2.1.center_mem hy) hFrame j i)
    (fun j => D.norm_firstDerivativeHalfL_small hΩ hm hCF hd hK hf hε hε1 hy j)
  exact hN.trans_eq (by dsimp only [CB];ring)
end PhysicalPrincipalData
end ShrinkingSpheres

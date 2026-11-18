import Proof.PhysicalFirstCoordinateAdjointFamily
import Proof.PhysicalFirstCommutatorGraph
import Proof.GradedWeightedCombinationAlgebra
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Contracting the SAME frame coefficient rows and the corresponding
covariant derivatives gives exactly the fixed-coordinate contraction. -/
lemma firstCommutatorForm_frame_change
    (S : I → I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (e : Frame) (y : X) (V : X →L[ℝ] SphereSobolev (1/2:ℝ)) :
    firstCommutatorForm S (fun i => V (e y i))=
      firstCommutatorForm (fun b c => ∑ i : I,e y i b • (∑ j : I,e y j c • S i j))
        (fun b => V (axis b)) := by
  have hV (i : I) : V (e y i)=∑ b : I,e y i b • V (axis b) := by
    calc
      _ = V (∑ b : I,e y i b • axis b) := congrArg V (axis_expansion (e y i)).symm
      _ = _ := by simp only [map_sum,map_smul]
  simp only [firstCommutatorForm,hV,Fin.sum_univ_three,sphereSobolevDualPairing,
    map_add,map_smul,_root_.add_apply,_root_.smul_apply,inner_add_left,inner_add_right,
    real_inner_smul_left,real_inner_smul_right]
  ring

namespace PhysicalFirstCommutatorPacket
variable {Y : Set X} {d : Data} {CF CT CB CS ε : ℝ}
  {P : PhysicalPrincipalData Y d CF CT}

def coordinateCommLow (W : PhysicalFirstCommutatorPacket P CB CS ε) (b c : I) (x : X) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ i : I,d.frame x i b • (∑ j : I,d.frame x j c • W.commLow i j x)

lemma coordinateCommLow_graph (W : PhysicalFirstCommutatorPacket P CB CS ε)
    (b c : I) {x : X} (hx : x ∈ Y) :
    (P.firstDerivativeCoordinateHalfL x b).adjoint.comp (P.firstDerivativeCoordinateHigherL x c)-
      (P.firstDerivativeCoordinateHalfL x c).comp (W.coordinateAdjointHigher b x)=
        (W.coordinateCommLow b c x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hAdj : (P.firstDerivativeCoordinateHalfL x b).adjoint=
      ∑ i : I,d.frame x i b • (P.firstDerivativeHalfL x i).adjoint := by
    simp only [PhysicalPrincipalData.firstDerivativeCoordinateHalfL,Fin.sum_univ_three,
      LinearIsometryEquiv.map_add,LinearIsometryEquiv.map_smulₛₗ,starRingEnd_apply,star_trivial]
  rw [hAdj]
  change (∑ i : I,d.frame x i b • (P.firstDerivativeHalfL x i).adjoint).comp
      (∑ j : I,d.frame x j c • P.firstDerivativeHigherL x j)-
    (∑ j : I,d.frame x j c • P.firstDerivativeHalfL x j).comp
      (∑ i : I,d.frame x i b • W.adjointHigh i x)=_
  rw [finite_real_combination_commutator_expansion]
  simp only [W.comm_graph _ _ x hx]
  apply ContinuousLinearMap.ext
  intro u
  simp only [coordinateCommLow,ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,
    Finset.smul_sum,smul_smul]

lemma norm_coordinateCommLow_le {Ω : Set X} (W : PhysicalFirstCommutatorPacket P CB CS ε)
    {m : ℕ} {K ρ c₀ floor : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (b c : I) {x : X} (hx : x ∈ Y) :
    ‖W.coordinateCommLow b c x‖ ≤ (9*K^2*CS)*(ε/beta d.γ d.radius x)^2 := by
  have hFrame := hd.1.2.2.2.2.2.2.2 x (hd.2.1.center_mem hx)
  have he (i k : I) : |d.frame x i k| ≤ K :=
    hd.1.1.frame_component_abs_le hK d.frame (hd.2.1.center_mem hx) hFrame i k
  have hRow (i : I) : ‖∑ j : I,d.frame x j c • W.commLow i j x‖ ≤ 3*K*(CS*(ε/beta d.γ d.radius x)^2) :=
    norm_weighted_sum_three_le _ _ K _ (zero_le_one.trans hK) (fun j => he j c) (fun j => W.comm_bound i j x hx)
  exact (norm_weighted_sum_three_le _ _ K _ (zero_le_one.trans hK) (fun i => he i b) hRow).trans_eq (by ring)
end PhysicalFirstCommutatorPacket
end ShrinkingSpheres

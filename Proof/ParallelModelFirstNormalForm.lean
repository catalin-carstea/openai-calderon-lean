import Proof.ParallelModelFirstCoreAlgebra
import Proof.ParallelModelFirstRaisingBudget
import Proof.ParallelModelFirstDefectPoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

def modelFirstLeadingDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε) (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  let Z := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num);
  metricDensity d.γ y*∑ k : I,∑ c : I,∑ b : I,(d.γ y)⁻¹ k c*(
    ⟪Z (framedRaisingHigherL d y (axis c) (fiveHalfCovariantDerivative d U (axis k) y)),
      Z (P.firstCovariantCoordinateHigherL b y (fiveHalfCovariantDerivative d U (axis b) y))⟫_ℝ-
    ⟪Z (scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c y (fiveHalfCovariantDerivative d U (axis k) y)),
      Z (WF.covariantCoordinateAdjointHigher b y (fiveHalfCovariantDerivative d U (axis b) y))⟫_ℝ)

def modelFirstZeroDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε) (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  let Z := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num);
  metricDensity d.γ y*∑ k : I,∑ c : I,∑ b : I,((d.γ y)⁻¹ k c*coordDeriv k (fun x => Real.log (d.radius x)) y)*(
    ⟪Z (framedRaisingHigherL d y (axis c) (scalarModelDegreeSection U y)),
      Z (P.firstCovariantCoordinateHigherL b y (fiveHalfCovariantDerivative d U (axis b) y))⟫_ℝ+
    ⟪Z (scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c y (scalarModelShiftedDegreeSection U y)),
      Z (WF.covariantCoordinateAdjointHigher b y (fiveHalfCovariantDerivative d U (axis b) y))⟫_ℝ)

lemma model_first_forward_core_half_graph
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (P : PhysicalPrincipalData Y d CF CT) (U : X → SphereSobolev (5/2:ℝ))
    {y : X} (hy : y ∈ Y) (hU : DifferentiableAt ℝ U y)
    (hP : ∀ b,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (P.firstCovariantCoordinateHigherL b y)=
      (P.firstCovariantCoordinateHalfL b y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    P.firstCovariantCoreSection (fiveHalfToTwoSection U) y=
      ∑ b : I,sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
        (P.firstCovariantCoordinateHigherL b y (fiveHalfCovariantDerivative d U (axis b) y)) := by
  apply Finset.sum_congr rfl
  intro b _
  have h := model_first_coarse_high_pair_of_graph (P.firstCovariantCoordinateCoarseL b y)
    (P.firstCovariantCoordinateHalfL b y) (P.firstCovariantCoordinateHigherL b y)
    (P.firstCovariantCoordinate_coarse_half_compatible hd hY hy b) (hP b)
    (fiveHalfCovariantDerivative d U (axis b) y)
  rw [fiveHalfCovariantDerivative_inclusion d U y (axis b) hU] at h
  exact h.symm

/-- Exact split of the literal complete paired component. The model's
lowering correction and the physical first-adjoint defect are both kept. -/
theorem modelFirstCorrectedDensity_split
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) {y : X} (hy : y ∈ Y) (hU : DifferentiableAt ℝ U y)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (hP : ∀ b,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (P.firstCovariantCoordinateHigherL b y)=
      (P.firstCovariantCoordinateHalfL b y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    modelFirstCorrectedDensity P WF W U y=4*(modelFirstLeadingDensity P WF U y+
      modelFirstZeroDensity P WF U y-modelFirstDefectDensity P WF W U y) := by
  obtain ⟨Q,hQ⟩ := exists_unit_boundary_coefficient
  let Z := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  let H := fun b : I => fiveHalfCovariantDerivative d U (axis b) y
  let RH := fun c : I => framedRaisingHigherL d y (axis c)
  let RA := fun c : I => scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c y
  let B := fun b : I => Z (P.firstCovariantCoordinateHigherL b y (H b))
  let T := fun b : I => Z (WF.covariantCoordinateAdjointHigher b y (H b))
  let δ := firstAdjointDefectCoreSection P WF W U y
  have hF := model_first_forward_core_half_graph hY hd P U hy hU hP
  have hD : P.firstFormalAdjointCore WF W U y=-(∑ b : I,T b)+δ := by
    change P.firstFormalAdjointCore WF W U y=-(∑ b : I,T b)+
      (P.firstFormalAdjointCore WF W U y-firstAdjointLeadingCoreSection WF U y)
    have hL : firstAdjointLeadingCoreSection WF U y=-(∑ b : I,T b) := by
      simp only [firstAdjointLeadingCoreSection,firstAdjointLeadingCoreRow,T,H,Z,
        firstSelfSourceDerivative,fiveHalfCovariantDerivative,←Finset.sum_neg_distrib]
    rw [hL]
    abel
  have hMF := modelFirstModelForwardHalf_coarse d U y hU hFrame
  have hMA := modelFirstModelAdjointHalf_coarse Q hQ modelFirstFlatAdjointHigher d U y hU hFrame modelFirstFlatAdjointHigher_graph
  have hCore := model_first_core_pair_split (fun k c => (d.γ y)⁻¹ k c)
    (fun k => coordDeriv k (fun x => Real.log (d.radius x)) y)
    (fun k c => Z (RH c (H k))) (fun k c => Z (RA c (H k)))
    (fun _k c => Z (RH c (scalarModelDegreeSection U y)))
    (fun _k c => Z (RA c (scalarModelShiftedDegreeSection U y))) B T δ
  have hSumF : ∑ k : I,∑ c : I,(d.γ y)⁻¹ k c •
      (Z (RH c (H k))+coordDeriv k (fun x => Real.log (d.radius x)) y • Z (RH c (scalarModelDegreeSection U y)))=
      modelRaisingSection d (fiveHalfToTwoSection U) y := by
    rw [←hMF]
    simp only [modelFirstModelForwardHalf,map_sum,map_smul,map_add,RH,H,Z]
  have hSumA : ∑ k : I,∑ c : I,(d.γ y)⁻¹ k c •
      (-Z (RA c (H k))+coordDeriv k (fun x => Real.log (d.radius x)) y • Z (RA c (scalarModelShiftedDegreeSection U y)))=
      modelLoweringSection d (fiveHalfToTwoSection U) y-modelAdjointDefectSection d (fiveHalfToTwoSection U) y := by
    rw [←hMA]
    simp only [modelFirstModelAdjointHalf,map_sum,map_smul,map_add,map_neg,RA,H,Z]
  rw [hSumF,hSumA,←hF,←hD] at hCore
  have hh := congrArg (fun t : ℝ => 4*metricDensity d.γ y*t) hCore
  simpa only [modelFirstCorrectedDensity,modelFirstLeadingDensity,modelFirstZeroDensity,modelFirstDefectDensity,
    Z,H,RH,RA,B,T,δ,mul_add,mul_sub,mul_assoc] using hh

end ShrinkingSpheres.ParallelEnergy

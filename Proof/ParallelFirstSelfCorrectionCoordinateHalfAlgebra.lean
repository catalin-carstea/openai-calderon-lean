import Proof.ParallelFirstSelfCorrectionHalfGraph
import Proof.PrincipalFirstErrorCoordinateSharpWeights
import Proof.PrincipalFirstCorrectionCoordinateCoarse
import Proof.ScaledTwoJetProductBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

section SquareAlgebra
variable {V0 V1 W0 W1 : Type*}
  [NormedAddCommGroup V0] [NormedSpace ℝ V0] [NormedAddCommGroup V1] [NormedSpace ℝ V1]
  [NormedAddCommGroup W0] [NormedSpace ℝ W0] [NormedAddCommGroup W1] [NormedSpace ℝ W1]
  (J : W0 →L[ℝ] W1) (Iin : V0 →L[ℝ] V1)
private lemma correction_square_add (A B : V0 →L[ℝ] W0) (L M : V1 →L[ℝ] W1)
    (hA : J.comp A=L.comp Iin) (hB : J.comp B=M.comp Iin) :
    J.comp (A+B)=(L+M).comp Iin := by
  ext u
  have ha := congrArg (fun T : V0 →L[ℝ] W1 => T u) hA
  have hb := congrArg (fun T : V0 →L[ℝ] W1 => T u) hB
  simpa only [ContinuousLinearMap.comp_apply,_root_.add_apply,map_add] using congrArg₂ (fun x y : W1 => x+y) ha hb
private lemma correction_square_smul (c : ℝ) (A : V0 →L[ℝ] W0) (L : V1 →L[ℝ] W1)
    (hA : J.comp A=L.comp Iin) : J.comp (c • A)=(c • L).comp Iin := by
  ext u
  have ha := congrArg (fun T : V0 →L[ℝ] W1 => T u) hA
  simpa only [ContinuousLinearMap.comp_apply,_root_.smul_apply,map_smul] using congrArg (fun x : W1 => c • x) ha
private lemma correction_square_sum {κ : Type*} [Fintype κ]
    (A : κ → V0 →L[ℝ] W0) (L : κ → V1 →L[ℝ] W1)
    (h : ∀ k,J.comp (A k)=(L k).comp Iin) : J.comp (∑ k,A k)=(∑ k,L k).comp Iin := by
  ext u
  simp only [ContinuousLinearMap.comp_apply,_root_.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact congrArg (fun T : V0 →L[ℝ] W1 => T u) (h k)
end SquareAlgebra

/-- One fixed first family for the complete weighted coordinate correction. -/
def correctionCoordinateCoarseFirstJet (d : Data) (b i : I) (x : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ∑ a : I,(principalFirstErrorCoordinateWeight d a b x •
      physicalFirstCorrectionCovariantFamily d (axis a) x (axis i)+
    fderiv ℝ (principalFirstErrorCoordinateWeight d a b) x (axis i) •
      physicalFirstCorrectionCoarseFamily d (axis a) x)

def correctionCoordinateHalfFirstJet (d : Data) (b i : I) (x : X) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ a : I,(principalFirstErrorCoordinateWeight d a b x •
      correctionHalfCovariantFamily d (axis a) (axis i) x+
    fderiv ℝ (principalFirstErrorCoordinateWeight d a b) x (axis i) •
      physicalFirstCorrectionHalfL d x (axis a))

lemma correctionCoordinateHalfFirstJet_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (b i : I) :
    ContDiffOn ℝ ∞ (correctionCoordinateCoarseFirstJet d b i) Y ∧
    ContDiffOn ℝ ∞ (correctionCoordinateHalfFirstJet d b i) Y ∧ ∀ y ∈ Y,
    CoarseCovariantRotationGraph d y (axis i) (principalFirstCorrectionCoordinateCoarseL d b)
      (correctionCoordinateCoarseFirstJet d b i y) ∧
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (correctionCoordinateCoarseFirstJet d b i y)=
      (correctionCoordinateHalfFirstJet d b i y).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  let E := fun a : I => physicalFirstCorrectionCoarseFamily d (axis a)
  let S := fun (a : I) (x : X) => physicalFirstCorrectionCovariantFamily d (axis a) x (axis i)
  let w := fun a : I => principalFirstErrorCoordinateWeight d a b
  have hES (a : I) : ContDiffOn ℝ ∞ (E a) Y :=
    (hd.contDiffOn_physicalFirstCorrectionAtL hY hΩ hK 0 (axis a)).clm_comp contDiffOn_const
  have hSS (a : I) : ContDiffOn ℝ ∞ (S a) Y :=
    (hd.physicalFirstCorrectionCovariantFamily_data hY hΩ hSub hK (axis a)).1.clm_apply contDiffOn_const
  have hHS (a : I) : ContDiffOn ℝ ∞ (fun x => physicalFirstCorrectionHalfL d x (axis a)) Y :=
    (hd.contDiffOn_physicalFirstCorrectionAtL hY hΩ hK (-(1/2:ℝ)) (axis a)).clm_comp contDiffOn_const
  have hLS (a : I) := correctionHalfCovariantFamily_smooth hY hΩ hSub hd hK (axis i) (axis a)
  have hWS (a : I) : ContDiffOn ℝ ∞ (w a) Y :=
    hd.contDiffOn_principalFirstErrorCoordinateWeight hK a b
  have hWDS (a : I) : ContDiffOn ℝ ∞ (fun x => fderiv ℝ (w a) x (axis i)) Y :=
    contDiffOn_coordDeriv hY (hWS a) i
  refine ⟨ContDiffOn.sum (fun a _ => ((hWS a).smul (hSS a)).add ((hWDS a).smul (hES a))),
    ContDiffOn.sum (fun a _ => ((hWS a).smul (hLS a)).add ((hWDS a).smul (hHS a))),?_⟩
  intro y hy
  refine ⟨?_,?_⟩
  · exact CoarseCovariantRotationGraph.sum_three (fun a x => w a x • E a x)
      (fun a => w a y • S a y+fderiv ℝ (w a) y (axis i) • E a y)
      (fun a => ((hd.physicalFirstCorrectionCovariantFamily_data hY hΩ hSub hK (axis a)).2 y hy (axis i)).smul (w a)
        (((hWS a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        (((hES a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)))
      (fun a => (((hWS a).smul (hES a)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
  · exact correction_square_sum _ _ _ _ (fun a => correction_square_add _ _ _ _ _ _
      (correction_square_smul _ _ _ _ _
        (correctionHalfCovariantFamily_coarse hY hΩ hSub hd hK hy (axis i) (axis a)))
      (correction_square_smul _ _ _ _ _ (physicalFirstCorrectionHalfL_coarse d y (axis a))))

/-- The four actual product-rule terms retain their SAME second half graph. -/
lemma correctionCoordinateHalfFirstJet_second_graph {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (b i j : I) {y : X} (hy : y ∈ Y)
    (T : I → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (N : I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hT : ∀ a,CoarseCovariantRotationGraph d y (axis j)
      (fun x => physicalFirstCorrectionCovariantFamily d (axis a) x (axis i)) (T a))
    (hN : ∀ a,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (T a)=
      (N a).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) :
    let w := fun a : I => principalFirstErrorCoordinateWeight d a b
    let Tc := ∑ a : I,((w a y • T a+fderiv ℝ (w a) y (axis j) •
      physicalFirstCorrectionCovariantFamily d (axis a) y (axis i))+
      (fderiv ℝ (w a) y (axis i) • physicalFirstCorrectionCovariantFamily d (axis a) y (axis j)+
        fderiv ℝ (fun x => fderiv ℝ (w a) x (axis i)) y (axis j) • physicalFirstCorrectionCoarseFamily d (axis a) y))
    let Nc := ∑ a : I,((w a y • N a+fderiv ℝ (w a) y (axis j) •
      correctionHalfCovariantFamily d (axis a) (axis i) y)+
      (fderiv ℝ (w a) y (axis i) • correctionHalfCovariantFamily d (axis a) (axis j) y+
        fderiv ℝ (fun x => fderiv ℝ (w a) x (axis i)) y (axis j) • physicalFirstCorrectionHalfL d y (axis a)))
    CoarseCovariantRotationGraph d y (axis j) (correctionCoordinateCoarseFirstJet d b i) Tc ∧
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp Tc=
        Nc.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  let E := fun a : I => physicalFirstCorrectionCoarseFamily d (axis a)
  let S := fun (a : I) (x v : X) => physicalFirstCorrectionCovariantFamily d (axis a) x v
  let w := fun a : I => principalFirstErrorCoordinateWeight d a b
  have hES (a : I) : ContDiffOn ℝ ∞ (E a) Y :=
    (hd.contDiffOn_physicalFirstCorrectionAtL hY hΩ hK 0 (axis a)).clm_comp contDiffOn_const
  have hSS (a k : I) : ContDiffOn ℝ ∞ (fun x => S a x (axis k)) Y :=
    (hd.physicalFirstCorrectionCovariantFamily_data hY hΩ hSub hK (axis a)).1.clm_apply contDiffOn_const
  have hWS (a : I) : ContDiffOn ℝ ∞ (w a) Y := hd.contDiffOn_principalFirstErrorCoordinateWeight hK a b
  have hWDS (a : I) : ContDiffOn ℝ ∞ (fun x => fderiv ℝ (w a) x (axis i)) Y :=
    contDiffOn_coordDeriv hY (hWS a) i
  refine ⟨?_,?_⟩
  · exact CoarseCovariantRotationGraph.sum_three
      (fun a x => w a x • S a x (axis i)+fderiv ℝ (w a) x (axis i) • E a x) _
      (fun a => coarse_covariant_second_weighted_graph (w a) (E a) (fun x => S a x (axis i))
        (S a y (axis j)) (T a) ((hWS a).contDiffAt (hY.mem_nhds hy))
        (((hES a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        (((hSS a i).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        ((hd.physicalFirstCorrectionCovariantFamily_data hY hΩ hSub hK (axis a)).2 y hy (axis j)) (hT a))
      (fun a => ((((hWS a).smul (hSS a i)).add ((hWDS a).smul (hES a))).contDiffAt
        (hY.mem_nhds hy)).differentiableAt (by simp))
  · exact correction_square_sum _ _ _ _ (fun a => correction_square_add _ _ _ _ _ _
      (correction_square_add _ _ _ _ _ _
        (correction_square_smul _ _ _ _ _ (hN a))
        (correction_square_smul _ _ _ _ _
          (correctionHalfCovariantFamily_coarse hY hΩ hSub hd hK hy (axis i) (axis a))))
      (correction_square_add _ _ _ _ _ _
        (correction_square_smul _ _ _ _ _
          (correctionHalfCovariantFamily_coarse hY hΩ hSub hd hK hy (axis j) (axis a)))
        (correction_square_smul _ _ _ _ _ (physicalFirstCorrectionHalfL_coarse d y (axis a)))))

end ShrinkingSpheres.ParallelEnergy

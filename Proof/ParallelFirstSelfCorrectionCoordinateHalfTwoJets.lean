import Proof.ParallelFirstSelfCorrectionHalfTwoJets
import Proof.ParallelFirstSelfCorrectionCoordinateHalfAlgebra

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

/-- Complete geometric correction in fixed physical coordinates: ONE smooth
first strong-half family, its genuine coarse inclusion graph, and a genuine
second graph with the original epsilon beta bound. Constants precede all
profiles, arbitrary smooth frames, centers, and source tests. -/
theorem uniform_correction_coordinate_strong_half_two_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 8 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∃ S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ∃ L : I → I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ∀ b i : I,ContDiffOn ℝ ∞ (S b i) Y ∧ ContDiffOn ℝ ∞ (L b i) Y ∧ ∀ y ∈ Y,
      CoarseCovariantRotationGraph d y (axis i) (principalFirstCorrectionCoordinateCoarseL d b) (S b i y) ∧
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (S b i y)=
        (L b i y).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
      ‖L b i y‖ ≤ C*ε ∧
      ∀ j : I,∃ T : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ∃ N : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
        CoarseCovariantRotationGraph d y (axis j) (S b i) T ∧
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T=
          N.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
        ‖N‖ ≤ C*ε*beta d.γ d.radius y := by
  classical
  obtain ⟨η,CP,hη,hη1,hCP,hTwo⟩ :=
    uniform_correction_strong_half_two_jets hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let B := principalFirstErrorCoordinateTwoJetBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
  let C := 12*B*CP
  have hB : 0 ≤ B := principalFirstErrorCoordinateTwoJetBudget_nonneg _ _ _ _
    (zero_le_one.trans hK) (abs_nonneg _) (abs_nonneg _)
  have hC : 0 ≤ C := by dsimp only [C];positivity
  have h6C : 6*B*CP ≤ C := by dsimp only [C];nlinarith only [mul_nonneg hB hCP]
  refine ⟨η,C,hη,hη1,hC,?_⟩
  intro floor hf ε hε hSmall d hd
  have hε1 : ε ≤ 1 := hSmall.trans hη1
  have hKpos := zero_lt_one.trans_le hK
  let S := correctionCoordinateCoarseFirstJet d
  let L := correctionCoordinateHalfFirstJet d
  have hData (a k : I) := hTwo floor hf ε hε hSmall d hd a k
  refine ⟨S,L,?_⟩
  intro b i
  have hCoordinate := correctionCoordinateHalfFirstJet_data hY hΩ hSub hd hKpos b i
  refine ⟨hCoordinate.1,hCoordinate.2.1,?_⟩
  intro y hy
  let β := beta d.γ d.radius y
  have hβ1 : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβ : 0 < β := zero_lt_one.trans_le hβ1
  let w := fun a : I => principalFirstErrorCoordinateWeight d a b
  have hw (a k l : I) := hd.principalFirstErrorCoordinateWeight_small_two_jet_bounds hY (by omega)
    hK hf hε hε1 hy a b k l
  have hAt (a k : I) := (hData a k).2.2 y hy
  have hEN (a : I) : ‖physicalFirstCorrectionHalfL d y (axis a)‖ ≤ CP := (hAt a i).2.2.1
  have hLN (a k : I) : ‖correctionHalfCovariantFamily d (axis a) (axis k) y‖ ≤ CP*β :=
    (hAt a k).2.2.2.1
  have h01 (a : I) := scaled_two_jet_product_bounds
    (physicalFirstCorrectionHalfL d y (axis a))
    (correctionHalfCovariantFamily d (axis a) (axis i) y)
    (correctionHalfCovariantFamily d (axis a) (axis i) y) 0
    (w a y) (fderiv ℝ (w a) y (axis i)) (fderiv ℝ (w a) y (axis i))
    (fderiv ℝ (fun x => fderiv ℝ (w a) x (axis i)) y (axis i)) B CP ε β hB hε hβ
    (hw a i i).1 (hw a i i).2.1 (hw a i i).2.1 (hw a i i).2.2
    (hEN a) (hLN a i) (hLN a i) (by simpa only [norm_zero] using mul_nonneg hCP (sq_nonneg β))
  have hFirstN : ‖L b i y‖ ≤ C*ε := by
    calc
      _ ≤ ∑ a : I,‖w a y • correctionHalfCovariantFamily d (axis a) (axis i) y+
          fderiv ℝ (w a) y (axis i) • physicalFirstCorrectionHalfL d y (axis a)‖ := norm_sum_le _ _
      _ ≤ ∑ _a : I,2*B*CP*ε/β := Finset.sum_le_sum (fun a _ => (h01 a).2.1)
      _ = (6*B*CP)*ε/β := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring
      _ ≤ (6*B*CP)*ε := div_le_self (by positivity) hβ1
      _ ≤ C*ε := mul_le_mul_of_nonneg_right h6C hε
  refine ⟨(hCoordinate.2.2 y hy).1,(hCoordinate.2.2 y hy).2,hFirstN,?_⟩
  intro j
  have hSecond (a : I) := (hAt a i).2.2.2.2 j
  choose Ta Na hTa hNa hNaN using hSecond
  have hGraph := correctionCoordinateHalfFirstJet_second_graph hY hΩ hSub hd hKpos b i j hy Ta Na hTa hNa
  let terms := fun a : I =>
    (w a y • Na a+fderiv ℝ (w a) y (axis j) • correctionHalfCovariantFamily d (axis a) (axis i) y)+
      (fderiv ℝ (w a) y (axis i) • correctionHalfCovariantFamily d (axis a) (axis j) y+
        fderiv ℝ (fun x => fderiv ℝ (w a) x (axis i)) y (axis j) • physicalFirstCorrectionHalfL d y (axis a))
  refine ⟨_,_,hGraph.1,hGraph.2,?_⟩
  change ‖∑ a : I,terms a‖ ≤ C*ε*β
  have hOne (a : I) : ‖terms a‖ ≤ 4*B*CP*ε :=
    (scaled_two_jet_product_bounds (physicalFirstCorrectionHalfL d y (axis a))
      (correctionHalfCovariantFamily d (axis a) (axis i) y)
      (correctionHalfCovariantFamily d (axis a) (axis j) y) (Na a)
      (w a y) (fderiv ℝ (w a) y (axis i)) (fderiv ℝ (w a) y (axis j))
      (fderiv ℝ (fun x => fderiv ℝ (w a) x (axis i)) y (axis j)) B CP ε β hB hε hβ
      (hw a i j).1 (hw a i j).2.1 (hw a j i).2.1 (hw a i j).2.2
      (hEN a) (hLN a i) (hLN a j) (hNaN a)).2.2
  calc
    _ ≤ ∑ a : I,‖terms a‖ := norm_sum_le _ _
    _ ≤ ∑ _a : I,4*B*CP*ε := Finset.sum_le_sum (fun a _ => hOne a)
    _ = C*ε := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,C];ring
    _ ≤ C*ε*β := le_mul_of_one_le_right (mul_nonneg hC hε) hβ1

end ShrinkingSpheres.ParallelEnergy

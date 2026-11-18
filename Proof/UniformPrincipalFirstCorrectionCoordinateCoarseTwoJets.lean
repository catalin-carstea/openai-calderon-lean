import Proof.UniformPhysicalFirstCorrectionCoarseTwoJets
import Proof.PrincipalFirstErrorCoordinateSharpWeights
import Proof.CoarseCovariantScaledTwoJetProduct
import Proof.PrincipalFirstCorrectionCoordinateCoarse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The actual coordinate geometric correction has genuine coarse
covariant jets and the sharp epsilon/beta squared, epsilon/beta, epsilon
bounds. Its smooth first families are fixed before all centers and tests. -/
theorem uniform_principal_first_correction_coordinate_coarse_two_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 8 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∃ S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ∀ b i : I,ContDiffOn ℝ ∞ (S b i) Y ∧ ∀ y ∈ Y,
          CoarseCovariantRotationGraph d y (axis i) (principalFirstCorrectionCoordinateCoarseL d b) (S b i y) ∧
          ‖principalFirstCorrectionCoordinateCoarseL d b y‖ ≤ C*ε/(beta d.γ d.radius y)^2 ∧
          ‖S b i y‖ ≤ C*ε/beta d.γ d.radius y ∧
          ∀ j : I,∃ T : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
            CoarseCovariantRotationGraph d y (axis j) (S b i) T ∧ ‖T‖ ≤ C*ε := by
  classical
  obtain ⟨η,CP,hη,hη1,hCP,hTwo⟩ :=
    uniform_physical_first_correction_coarse_two_jets hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let B := principalFirstErrorCoordinateTwoJetBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
  let C := 12*B*CP
  have hB : 0 ≤ B := principalFirstErrorCoordinateTwoJetBudget_nonneg _ _ _ _
    (zero_le_one.trans hK) (abs_nonneg _) (abs_nonneg _)
  have h3C : 3*B*CP ≤ C := by dsimp only [C];nlinarith only [mul_nonneg hB hCP]
  have h6C : 6*B*CP ≤ C := by dsimp only [C];nlinarith only [mul_nonneg hB hCP]
  refine ⟨η,C,hη,hη1,by dsimp only [C];positivity,?_⟩
  intro floor hf ε hε hSmall d hd
  have hε1 : ε ≤ 1 := hSmall.trans hη1
  let E := fun a : I => physicalFirstCorrectionCoarseFamily d (axis a)
  let Sa := fun (a : I) (x v : X) => physicalFirstCorrectionCovariantFamily d (axis a) x v
  let w := fun (a b : I) => principalFirstErrorCoordinateWeight d a b
  let S := fun (b i : I) (x : X) => ∑ a : I,
    (w a b x • Sa a x (axis i)+fderiv ℝ (w a b) x (axis i) • E a x)
  have hData (a : I) := hTwo floor hf ε hε hSmall d hd (axis a)
  have hES (a : I) : ContDiffOn ℝ ∞ (E a) Y := (hData a).1
  have hSSa (a i : I) : ContDiffOn ℝ ∞ (fun x => Sa a x (axis i)) Y :=
    (hData a).2.1.clm_apply contDiffOn_const
  have hWS (a b : I) : ContDiffOn ℝ ∞ (w a b) Y :=
    hd.contDiffOn_principalFirstErrorCoordinateWeight (zero_lt_one.trans_le hK) a b
  have hWDS (a b i : I) : ContDiffOn ℝ ∞ (fun x => fderiv ℝ (w a b) x (axis i)) Y :=
    contDiffOn_coordDeriv hY (hWS a b) i
  have hTermS (a b i : I) : ContDiffOn ℝ ∞ (fun x =>
      w a b x • Sa a x (axis i)+fderiv ℝ (w a b) x (axis i) • E a x) Y :=
    ((hWS a b).smul (hSSa a i)).add ((hWDS a b i).smul (hES a))
  refine ⟨S,?_⟩
  intro b i
  refine ⟨ContDiffOn.sum (fun a _ => hTermS a b i),?_⟩
  intro y hy
  let β := beta d.γ d.radius y
  have hβ : 0 < β := zero_lt_one.trans_le (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  have hw (a i j : I) := hd.principalFirstErrorCoordinateWeight_small_two_jet_bounds hY (by omega)
    hK hf hε hε1 hy a b i j
  have hEN (a : I) : ‖E a y‖ ≤ CP := by
    simpa only [norm_axis,mul_one] using ((hData a).2.2 y hy).2.1
  have hSN (a k : I) : ‖Sa a y (axis k)‖ ≤ CP*β := by
    simpa only [norm_axis,mul_one] using ((hData a).2.2 y hy).2.2.1 (axis k) (by simp only [norm_axis,le_refl])
  have hFirstGraph : CoarseCovariantRotationGraph d y (axis i)
      (principalFirstCorrectionCoordinateCoarseL d b) (S b i y) :=
    CoarseCovariantRotationGraph.sum_three (fun a x => w a b x • E a x)
      (fun a => w a b y • Sa a y (axis i)+fderiv ℝ (w a b) y (axis i) • E a y)
      (fun a => (((hData a).2.2 y hy).1 (axis i)).smul (w a b)
        (((hWS a b).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        (((hES a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)))
      (fun a => (((hWS a b).smul (hES a)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
  have h01 (a : I) := coarse_scaled_two_jet_product_bounds
    (E a y) (Sa a y (axis i)) (Sa a y (axis i)) 0
    (w a b y) (fderiv ℝ (w a b) y (axis i)) (fderiv ℝ (w a b) y (axis i))
    (fderiv ℝ (fun x => fderiv ℝ (w a b) x (axis i)) y (axis i)) B CP ε β hB hε hβ
    (hw a i i).1 (hw a i i).2.1 (hw a i i).2.1 (hw a i i).2.2
    (hEN a) (hSN a i) (hSN a i) (by simpa only [norm_zero] using mul_nonneg hCP (sq_nonneg β))
  have hZeroN : ‖principalFirstCorrectionCoordinateCoarseL d b y‖ ≤ C*ε/β^2 := by
    calc
      _ ≤ ∑ a : I,‖w a b y • E a y‖ := norm_sum_le _ _
      _ ≤ ∑ _a : I,B*CP*ε/β^2 := Finset.sum_le_sum (fun a _ => (h01 a).1)
      _ = (3*B*CP)*ε/β^2 := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring
      _ ≤ C*ε/β^2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h3C hε) (sq_nonneg β)
  have hFirstN : ‖S b i y‖ ≤ C*ε/β := by
    calc
      _ ≤ ∑ a : I,‖w a b y • Sa a y (axis i)+fderiv ℝ (w a b) y (axis i) • E a y‖ := norm_sum_le _ _
      _ ≤ ∑ _a : I,2*B*CP*ε/β := Finset.sum_le_sum (fun a _ => (h01 a).2.1)
      _ = (6*B*CP)*ε/β := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring
      _ ≤ C*ε/β := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h6C hε) hβ.le
  refine ⟨hFirstGraph,hZeroN,hFirstN,?_⟩
  intro j
  have hSecond (a : I) : ∃ T : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      CoarseCovariantRotationGraph d y (axis j) (fun x => Sa a x (axis i)) T ∧ ‖T‖ ≤ CP*β^2 := by
    simpa only [norm_axis,mul_one] using ((hData a).2.2 y hy).2.2.2 (axis i) (axis j)
      (by simp only [norm_axis,le_refl]) (by simp only [norm_axis,le_refl])
  choose Ta hTa hTaN using hSecond
  let terms := fun a : I =>
    (w a b y • Ta a+fderiv ℝ (w a b) y (axis j) • Sa a y (axis i))+
      (fderiv ℝ (w a b) y (axis i) • Sa a y (axis j)+
        fderiv ℝ (fun x => fderiv ℝ (w a b) x (axis i)) y (axis j) • E a y)
  refine ⟨∑ a : I,terms a,?_,?_⟩
  · exact CoarseCovariantRotationGraph.sum_three
      (fun a x => w a b x • Sa a x (axis i)+fderiv ℝ (w a b) x (axis i) • E a x) terms
      (fun a => coarse_covariant_second_weighted_graph (w a b) (E a) (fun x => Sa a x (axis i))
        (Sa a y (axis j)) (Ta a) ((hWS a b).contDiffAt (hY.mem_nhds hy))
        (((hES a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        (((hSSa a i).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        (((hData a).2.2 y hy).1 (axis j)) (hTa a))
      (fun a => ((hTermS a b i).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
  · have hOne (a : I) : ‖terms a‖ ≤ 4*B*CP*ε :=
      (coarse_scaled_two_jet_product_bounds (E a y) (Sa a y (axis i)) (Sa a y (axis j)) (Ta a)
        (w a b y) (fderiv ℝ (w a b) y (axis i)) (fderiv ℝ (w a b) y (axis j))
        (fderiv ℝ (fun x => fderiv ℝ (w a b) x (axis i)) y (axis j)) B CP ε β hB hε hβ
        (hw a i j).1 (hw a i j).2.1 (hw a j i).2.1 (hw a i j).2.2
        (hEN a) (hSN a i) (hSN a j) (hTaN a)).2.2
    calc
      _ ≤ ∑ a : I,‖terms a‖ := norm_sum_le _ _
      _ ≤ ∑ _a : I,4*B*CP*ε := Finset.sum_le_sum (fun a _ => hOne a)
      _ = C*ε := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,C];ring

end ShrinkingSpheres

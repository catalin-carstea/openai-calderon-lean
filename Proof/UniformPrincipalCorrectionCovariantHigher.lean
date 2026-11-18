import Proof.PhysicalCorrectionCovariantHigherData
import Proof.UniformPrincipalFirstCorrectionCoordinateCoarseTwoJets
import Proof.PrincipalFirstCorrectionCoordinateWeights

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The same smooth coordinate geometric-correction jets have true higher
endpoints, with constants uniform before every admitted profile and test. -/
theorem uniform_principal_first_correction_coordinate_covariant_higher
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 8 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∃ S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ∀ b i : I,ContDiffOn ℝ ∞ (S b i) Y ∧ ∀ y ∈ Y,
          CoarseCovariantRotationGraph d y (axis i) (principalFirstCorrectionCoordinateCoarseL d b) (S b i y) ∧
          ∃ H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
            (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp H=
              (S b i y).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) ∧ ‖H‖ ≤ CE*ε := by
  classical
  obtain ⟨QJ,hQJ,hHigher⟩ := uniform_physical_first_correction_covariant_higher_data
    hY hΩ (by omega) K ρ c₀ M Cj hK
  obtain ⟨η,CS,hη,hη1,hCS,hJets⟩ := uniform_principal_first_correction_coordinate_coarse_two_jets
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let QB := physicalFirstCorrectionHalfBudget K (M 0) (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2)
  let Q := QB+QJ
  let B := principalFirstErrorCoordinateWeightBudget K |M ⟨1,by omega⟩|
  let CE := 6*B*Q
  have hQB : 0 ≤ QB := physicalFirstCorrectionHalfBudget_nonneg _ _ _ _ _ (zero_le_one.trans hK)
  have hQ : 0 ≤ Q := add_nonneg hQB hQJ
  have hB : 0 ≤ B := principalFirstErrorCoordinateWeightBudget_nonneg _ _ (zero_le_one.trans hK) (abs_nonneg _)
  have hQBQ : QB ≤ Q := le_add_of_nonneg_right hQJ
  have hQJQ : QJ ≤ Q := le_add_of_nonneg_left hQB
  refine ⟨η,CE,hη,hη1,by dsimp only [CE];positivity,?_⟩
  intro floor hf ε hε hSmall d hd
  have hε1 := hSmall.trans hη1
  have hKpos := zero_lt_one.trans_le hK
  obtain ⟨S,hS⟩ := hJets floor hf ε hε hSmall d hd
  let E := fun a : I => physicalFirstCorrectionCoarseFamily d (axis a)
  let Sa := fun (a : I) (x : X) => physicalFirstCorrectionCovariantFamily d (axis a) x
  let H0 := fun (a : I) (x : X) => physicalFirstCorrectionHigherL d x (axis a)
  let w := fun a b : I => principalFirstErrorCoordinateWeight d a b
  have hData (a : I) := hd.physicalFirstCorrection_half_data hY hΩ (by omega) hK hf hε hε1 a
  have hES (a : I) : ContDiffOn ℝ ∞ (E a) Y :=
    (hd.contDiffOn_physicalFirstCorrectionAtL hY hΩ hKpos 0 (axis a)).clm_comp contDiffOn_const
  have hWS (a b : I) : ContDiffOn ℝ ∞ (w a b) Y :=
    hd.contDiffOn_principalFirstErrorCoordinateWeight hKpos a b
  have hGraph (a : I) := (hd.physicalFirstCorrectionCovariantFamily_data hY hΩ hSub hKpos (axis a)).2
  refine ⟨S,?_⟩
  intro b i
  refine ⟨(hS b i).1,?_⟩
  intro y hy
  choose H1 hH1 hH1N using fun a : I => hHigher floor hf ε hε hε1 d hd y hy a i
  let S0 := ∑ a : I,(w a b y • Sa a y (axis i)+fderiv ℝ (w a b) y (axis i) • E a y)
  let H := ∑ a : I,(w a b y • H1 a+fderiv ℝ (w a b) y (axis i) • H0 a y)
  have hGraph0 : CoarseCovariantRotationGraph d y (axis i)
      (principalFirstCorrectionCoordinateCoarseL d b) S0 :=
    CoarseCovariantRotationGraph.sum_three (fun a x => w a b x • E a x)
      (fun a => w a b y • Sa a y (axis i)+fderiv ℝ (w a b) y (axis i) • E a y)
      (fun a => (hGraph a y hy (axis i)).smul (w a b)
        (((hWS a b).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        (((hES a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)))
      (fun a => (((hWS a b).smul (hES a)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
  have hSame : S b i y=S0 := coarseCovariantRotationGraph_unique ((hS b i).2 y hy).1 hGraph0
  have hCompat : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp H=
      (S b i y).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
    rw [hSame]
    apply ContinuousLinearMap.ext
    intro u
    have hBaseU (a : I) := DFunLike.congr_fun (physicalFirstCorrectionHigherL_coarse d y (axis a)) u
    have hJetU (a : I) := DFunLike.congr_fun (hH1 a) u
    simp only [ContinuousLinearMap.comp_apply] at hBaseU hJetU
    simp only [S0,H,H0,E,Sa,ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.add_apply,
      _root_.smul_apply,map_sum,map_add,map_smul,hBaseU,hJetU]
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hOne (a : I) : ‖w a b y • H1 a+fderiv ℝ (w a b) y (axis i) • H0 a y‖ ≤ 2*B*Q*ε := by
    have hw := hd.principalFirstErrorCoordinateWeight_small_bounds hY (by omega) hK hf hε hε1 hy a b i
    have hW : |w a b y| ≤ B*ε := hw.1.trans (div_le_self (mul_nonneg hB hε) hβ)
    have hN0 : ‖H0 a y‖ ≤ Q := ((hData a).2.2 y hy).2.1.trans hQBQ
    have hN1 : ‖H1 a‖ ≤ Q := (hH1N a).trans hQJQ
    have h0 : ‖w a b y • H1 a‖ ≤ (B*ε)*Q := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul hW hN1 (norm_nonneg _) (mul_nonneg hB hε)
    have h1 : ‖fderiv ℝ (w a b) y (axis i) • H0 a y‖ ≤ (B*ε)*Q := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul hw.2 hN0 (norm_nonneg _) (mul_nonneg hB hε)
    exact ((norm_add_le _ _).trans (add_le_add h0 h1)).trans_eq (by ring)
  refine ⟨((hS b i).2 y hy).1,H,hCompat,?_⟩
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun a _ => hOne a)).trans_eq
    (by simp only [Fin.sum_univ_three,CE];ring))

end ShrinkingSpheres

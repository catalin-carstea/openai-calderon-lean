import Proof.NativeCovariantHigherJet
import Proof.UniformPhysicalFirstErrorCoordinateCoarseTwoJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The SAME actual coordinate first-error covariant jets retain a genuine
genuine higher endpoint. The smooth coarse families are fixed before
all tests, and the original uniform radius-beta/epsilon scales survive. -/
theorem uniform_physical_first_error_coordinate_covariant_higher
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ∀ b i : I,ContDiffOn ℝ ∞ (S b i) Y ∧ ∀ y ∈ Y,
          CoarseCovariantRotationGraph d y (axis i)
            (principalFirstErrorCoordinateCoarseL d P.adjoint P.center b) (S b i y) ∧
          ∃ L : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
            (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp L=
              (S b i y).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) ∧
            ‖L‖ ≤ CE*d.radius y*beta d.γ d.radius y ∧ ‖L‖ ≤ CE*ε := by
  classical
  obtain ⟨ηH,C0,C1,hηH,hηH1,hC0,hC1,hHalf⟩ :=
    uniform_actual_first_error_covariant_higher_graph hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηS,CS,hηS,hηS1,hCS,hJets⟩ :=
    uniform_physical_first_error_coordinate_coarse_two_jets hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let B := principalFirstErrorCoordinateWeightBudget K |M ⟨1,by omega⟩|
  let CE := 3*B*(C0+C1)
  have hB : 0 ≤ B := principalFirstErrorCoordinateWeightBudget_nonneg _ _ (zero_le_one.trans hK) (abs_nonneg _)
  have hCE : 0 ≤ CE := by dsimp only [CE];positivity
  refine ⟨min ηH ηS,CE,lt_min hηH hηS,(min_le_left _ _).trans hηH1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  obtain ⟨S,hS⟩ := hJets floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CF CT P
  let E := fun a : I => actualFirstAdjointErrorFamily d (axis a) P.adjoint (P.center a)
  let w := fun a b : I => principalFirstErrorCoordinateWeight d a b
  have hES (a : I) : ContDiffOn ℝ ∞ (E a) Y :=
    contDiffOn_actualFirstAdjointErrorFamily (axis a) hY hΩ hSub hd.1 (zero_lt_one.trans_le hK)
      hd.2.2.2.2.1.1 (fun x hx => (hd.2.2.2.2.1.2 x hx).1) P.adjoint (P.center a)
      P.adjoint_smooth (P.center_smooth a)
  have hWS (a b : I) : ContDiffOn ℝ ∞ (w a b) Y :=
    hd.contDiffOn_principalFirstErrorCoordinateWeight (zero_lt_one.trans_le hK) a b
  refine ⟨S,?_⟩
  intro b i
  refine ⟨(hS b i).1,?_⟩
  intro y hy
  choose L0 L1 Sa hBase hGraph hJet hL0 hL1 hLε using fun a : I =>
    hHalf floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd
      P.radial P.adjoint P.adjoint_smooth P.radial_actual P.adjoint_pair (axis a)
      (P.center a) (P.center_smooth a) (P.center_actual a) y hy (axis i) (by simpa only [norm_axis] using (le_refl (1:ℝ)))
  let S0 := ∑ a : I,(w a b y • Sa a+fderiv ℝ (w a b) y (axis i) • E a y)
  let L := ∑ a : I,(w a b y • L1 a+fderiv ℝ (w a b) y (axis i) • L0 a)
  have hGraph0 : CoarseCovariantRotationGraph d y (axis i)
      (principalFirstErrorCoordinateCoarseL d P.adjoint P.center b) S0 := by
    exact CoarseCovariantRotationGraph.sum_three (fun a x => w a b x • E a x)
      (fun a => w a b y • Sa a+fderiv ℝ (w a b) y (axis i) • E a y)
      (fun a => (hGraph a).smul (w a b)
        (((hWS a b).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        (((hES a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)))
      (fun a => (((hWS a b).smul (hES a)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
  have hSame : S b i y=S0 := coarseCovariantRotationGraph_unique ((hS b i).2 y hy).1 hGraph0
  have hCompat : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp L=
      (S b i y).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
    rw [hSame]
    apply ContinuousLinearMap.ext
    intro u
    have hBaseU (a : I) := DFunLike.congr_fun (hBase a) u
    have hJetU (a : I) := DFunLike.congr_fun (hJet a) u
    simp only [ContinuousLinearMap.comp_apply] at hBaseU hJetU
    simp only [S0,L,ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.add_apply,_root_.smul_apply,
      map_sum,map_add,map_smul,E,hBaseU,hJetU]
  let r := d.radius y
  let β := beta d.γ d.radius y
  have hr : 0 ≤ r := (hd.2.2.2.2.1.2 y hy).1.le
  have hβ : 0 ≤ β := zero_le_one.trans (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  have hε1 : ε ≤ 1 := hSmall.trans ((min_le_left _ _).trans hηH1)
  have hw (a : I) := hd.principalFirstErrorCoordinateWeight_bounds hY (by omega) hK hf hε hε1 hy a b i
  have hL0N (a : I) : ‖L0 a‖ ≤ C0*r := by simpa only [norm_axis,mul_one] using hL0 a
  have hL1N (a : I) : ‖L1 a‖ ≤ C1*r*β := by simpa only [norm_axis,mul_one] using hL1 a
  have hOne (a : I) : ‖w a b y • L1 a+fderiv ℝ (w a b) y (axis i) • L0 a‖ ≤ B*(C0+C1)*r*β := by
    have h0 : ‖w a b y • L1 a‖ ≤ B*(C1*r*β) := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hw a).1 (hL1N a) (norm_nonneg _) hB
    have h1 : ‖fderiv ℝ (w a b) y (axis i) • L0 a‖ ≤ (B*β)*(C0*r) := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hw a).2 (hL0N a) (norm_nonneg _) (mul_nonneg hB hβ)
    exact ((norm_add_le _ _).trans (add_le_add h0 h1)).trans_eq (by ring)
  have hNorm : ‖L‖ ≤ CE*r*β := by
    calc
      _ ≤ ∑ a : I,‖w a b y • L1 a+fderiv ℝ (w a b) y (axis i) • L0 a‖ := norm_sum_le _ _
      _ ≤ ∑ _a : I,B*(C0+C1)*r*β := Finset.sum_le_sum (fun a _ => hOne a)
      _ = CE*r*β := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,CE]
        ring
  have hRadius := radius_bounds r β floor ε hr hf (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2
  have hrβ : r*β ≤ ε := hRadius.2.1.trans (div_le_self hε hf)
  refine ⟨((hS b i).2 y hy).1,L,hCompat,hNorm,hNorm.trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrβ hCE

end ShrinkingSpheres

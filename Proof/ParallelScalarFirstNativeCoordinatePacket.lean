import Proof.ParallelScalarFirstNativeStrongPacket
import Proof.ParallelScalarFirstHalfProductNorm
import Proof.UniformActualFirstAdjointEndpoints
import Proof.UniformPhysicalFirstErrorCoordinateCoarseTwoJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Actual coordinate weights preserve the SAME smooth first strong-half
family and the original second strong-half radius-beta-squared estimate. -/
theorem uniform_first_error_coordinate_strong_half_two_jets
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ∃ L : I → I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ∀ b i : I,ContDiffOn ℝ ∞ (S b i) Y ∧ ContDiffOn ℝ ∞ (L b i) Y ∧ ∀ y ∈ Y,
        CoarseCovariantRotationGraph d y (axis i)
          (principalFirstErrorCoordinateCoarseL d P.adjoint P.center b) (S b i y) ∧
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (S b i y)=
          (L b i y).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
        ‖L b i y‖ ≤ CE*d.radius y*beta d.γ d.radius y ∧
        ∀ j : I,∃ T : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ∃ N : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
          CoarseCovariantRotationGraph d y (axis j) (S b i) T ∧
          (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T=
            N.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
          ‖N‖ ≤ CE*d.radius y*(beta d.γ d.radius y)^2 := by
  classical
  obtain ⟨η0,C0,hη0,hη01,hC0,hBase⟩ :=
    uniform_actual_first_adjoint_error_endpoints hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨η2,C1,C2,hη2,hη21,hC1,hC2,hTwo⟩ :=
    uniform_actual_first_error_strong_half_two_jets hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let B := principalFirstErrorCoordinateTwoJetBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
  let A := C0+2*C1+C2
  let CE := 3*B*A
  have hB : 0 ≤ B := principalFirstErrorCoordinateTwoJetBudget_nonneg _ _ _ _
    (zero_le_one.trans hK) (abs_nonneg _) (abs_nonneg _)
  have hA : 0 ≤ A := by dsimp only [A];positivity
  have h1A : C0+C1 ≤ A := by dsimp only [A];linarith only [hC1,hC2]
  refine ⟨min η0 η2,CE,lt_min hη0 hη2,(min_le_left _ _).trans hη01,
    by dsimp only [CE];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  have hε1 : ε ≤ 1 := hSmall.trans ((min_le_left _ _).trans hη01)
  choose L0 H0 hL0S hH0S hEnd using fun a : I =>
    hBase floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd (axis a)
      P.radial P.adjoint (P.center a) P.radial_actual P.adjoint_pair (P.center_actual a)
  choose Sa La hSa using fun a : I => hTwo floor hf ε hε (hSmall.trans (min_le_right _ _))
    d hd P.radial P.adjoint P.adjoint_smooth P.radial_actual P.adjoint_pair (axis a)
      (P.center a) (P.center_smooth a) (P.center_actual a)
  let E := fun a : I => actualFirstAdjointErrorFamily d (axis a) P.adjoint (P.center a)
  let w := fun a b : I => principalFirstErrorCoordinateWeight d a b
  let S := fun (b i : I) (x : X) => ∑ a : I,
    (w a b x • Sa a i x+fderiv ℝ (w a b) x (axis i) • E a x)
  let L := fun (b i : I) (x : X) => ∑ a : I,
    (w a b x • La a i x+fderiv ℝ (w a b) x (axis i) • L0 a x)
  have hES (a : I) : ContDiffOn ℝ ∞ (E a) Y :=
    contDiffOn_actualFirstAdjointErrorFamily (axis a) hY hΩ hSub hd.1 (zero_lt_one.trans_le hK)
      hd.2.2.2.2.1.1 (fun x hx => (hd.2.2.2.2.1.2 x hx).1) P.adjoint (P.center a)
      P.adjoint_smooth (P.center_smooth a)
  have hWS (a b : I) : ContDiffOn ℝ ∞ (w a b) Y :=
    hd.contDiffOn_principalFirstErrorCoordinateWeight (zero_lt_one.trans_le hK) a b
  have hWDS (a b i : I) : ContDiffOn ℝ ∞ (fun x => fderiv ℝ (w a b) x (axis i)) Y :=
    contDiffOn_coordDeriv hY (hWS a b) i
  have hSTerm (a b i : I) : ContDiffOn ℝ ∞ (fun x =>
      w a b x • Sa a i x+fderiv ℝ (w a b) x (axis i) • E a x) Y :=
    ((hWS a b).smul (hSa a i).1).add ((hWDS a b i).smul (hES a))
  have hLTerm (a b i : I) : ContDiffOn ℝ ∞ (fun x =>
      w a b x • La a i x+fderiv ℝ (w a b) x (axis i) • L0 a x) Y :=
    ((hWS a b).smul (hSa a i).2.1).add ((hWDS a b i).smul (hL0S a))
  refine ⟨S,L,?_⟩
  intro b i
  refine ⟨ContDiffOn.sum (fun a _ => hSTerm a b i),
    ContDiffOn.sum (fun a _ => hLTerm a b i),?_⟩
  intro y hy
  let r := d.radius y
  let β := beta d.γ d.radius y
  have hr : 0 ≤ r := (hd.2.2.2.2.1.2 y hy).1.le
  have hβ : 0 ≤ β := zero_le_one.trans (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  have hw (a i j : I) := hd.principalFirstErrorCoordinateWeight_two_jet_bounds hY (by omega)
    hK hf hε hε1 hy a b i j
  have hL0N (a : I) : ‖L0 a y‖ ≤ C0*r := by
    simpa only [norm_axis,mul_one] using (hEnd a y hy).2.2.1
  have hLN (a k : I) : ‖La a k y‖ ≤ C1*r*β := by
    simpa only [norm_axis,mul_one] using ((hSa a k).2.2 y hy).2.2.1
  have hFirstGraph : CoarseCovariantRotationGraph d y (axis i)
      (principalFirstErrorCoordinateCoarseL d P.adjoint P.center b) (S b i y) :=
    CoarseCovariantRotationGraph.sum_three (fun a x => w a b x • E a x)
      (fun a => w a b y • Sa a i y+fderiv ℝ (w a b) y (axis i) • E a y)
      (fun a => (((hSa a i).2.2 y hy).1).smul (w a b)
        (((hWS a b).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        (((hES a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)))
      (fun a => (((hWS a b).smul (hES a)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
  have hCompat : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (S b i y)=
      (L b i y).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    apply ContinuousLinearMap.ext
    intro u
    have h0 (a : I) := DFunLike.congr_fun (hEnd a y hy).1 u
    have h1 (a : I) := DFunLike.congr_fun (((hSa a i).2.2 y hy).2.1) u
    simp only [ContinuousLinearMap.comp_apply] at h0 h1
    simp only [S,L,ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.add_apply,_root_.smul_apply,
      map_sum,map_add,map_smul,E,h0,h1]
  have hFirstN : ‖L b i y‖ ≤ CE*r*β := by
    have hOne (a : I) : ‖w a b y • La a i y+fderiv ℝ (w a b) y (axis i) • L0 a y‖ ≤
        B*(C0+C1)*r*β := by
      have h0 : ‖w a b y • La a i y‖ ≤ B*(C1*r*β) := by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul (hw a i i).1 (hLN a i) (norm_nonneg _) hB
      have h1 : ‖fderiv ℝ (w a b) y (axis i) • L0 a y‖ ≤ (B*β)*(C0*r) := by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul (hw a i i).2.1 (hL0N a) (norm_nonneg _) (mul_nonneg hB hβ)
      exact ((norm_add_le _ _).trans (add_le_add h0 h1)).trans_eq (by ring)
    calc
      _ ≤ ∑ a : I,‖w a b y • La a i y+fderiv ℝ (w a b) y (axis i) • L0 a y‖ := norm_sum_le _ _
      _ ≤ ∑ _a : I,B*(C0+C1)*r*β := Finset.sum_le_sum (fun a _ => hOne a)
      _ = 3*B*(C0+C1)*r*β := by simp only [Fin.sum_univ_three];ring
      _ ≤ CE*r*β := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h1A (mul_nonneg (by norm_num) hB)) hr) hβ
  refine ⟨hFirstGraph,hCompat,hFirstN,?_⟩
  intro j
  choose Ta Na hTa hNa hNaN using fun a : I => ((hSa a i).2.2 y hy).2.2.2 j
  let terms := fun a : I =>
    (w a b y • Ta a+fderiv ℝ (w a b) y (axis j) • Sa a i y)+
      (fderiv ℝ (w a b) y (axis i) • Sa a j y+
        fderiv ℝ (fun x => fderiv ℝ (w a b) x (axis i)) y (axis j) • E a y)
  let halfTerms := fun a : I =>
    (w a b y • Na a+fderiv ℝ (w a b) y (axis j) • La a i y)+
      (fderiv ℝ (w a b) y (axis i) • La a j y+
        fderiv ℝ (fun x => fderiv ℝ (w a b) x (axis i)) y (axis j) • L0 a y)
  refine ⟨∑ a : I,terms a,∑ a : I,halfTerms a,?_,?_,?_⟩
  · exact CoarseCovariantRotationGraph.sum_three
      (fun a x => w a b x • Sa a i x+fderiv ℝ (w a b) x (axis i) • E a x) terms
      (fun a => coarse_covariant_second_weighted_graph (w a b) (E a) (Sa a i)
        (Sa a j y) (Ta a) ((hWS a b).contDiffAt (hY.mem_nhds hy))
        (((hES a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        (((hSa a i).1.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        (((hSa a j).2.2 y hy).1) (hTa a))
      (fun a => ((hSTerm a b i).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
  · apply ContinuousLinearMap.ext
    intro u
    have h0 (a : I) := DFunLike.congr_fun (hEnd a y hy).1 u
    have h1 (a k : I) := DFunLike.congr_fun (((hSa a k).2.2 y hy).2.1) u
    have h2 (a : I) := DFunLike.congr_fun (hNa a) u
    simp only [ContinuousLinearMap.comp_apply] at h0 h1 h2
    simp only [terms,halfTerms,ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.add_apply,_root_.smul_apply,
      map_sum,map_add,map_smul,E,h0,h1,h2]
  · have hOne (a : I) : ‖halfTerms a‖ ≤ B*(C2+2*C1+C0)*r*β^2 := by
      apply norm_second_weighted_jet_le (L0 a y) (La a i y) (La a j y) (Na a)
        _ _ _ _ B C0 C1 C2 r β hB hβ (hw a i j).1 (hw a i j).2.1 (hw a j i).2.1
        (hw a i j).2.2 (hL0N a) (hLN a i) (hLN a j)
      simpa only [norm_axis,mul_one] using hNaN a
    calc
      _ ≤ ∑ a : I,‖halfTerms a‖ := norm_sum_le _ _
      _ ≤ ∑ _a : I,B*(C2+2*C1+C0)*r*β^2 := Finset.sum_le_sum (fun a _ => hOne a)
      _ = CE*r*β^2 := by simp only [Fin.sum_univ_three,CE,A];ring

end ShrinkingSpheres.ParallelEnergy

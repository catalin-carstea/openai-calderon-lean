import Proof.UniformPhysicalCoarseAxisFirstErrorBound
import Proof.UniformActualFirstErrorCovariantTwoJets
import Proof.PrincipalFirstErrorCoordinateCoarse
import Proof.PrincipalFirstErrorCoordinateTwoJetWeights
import Proof.CoarseCovariantSecondProduct
import Proof.ActualFrameFirstAdjointError

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The SAME actual coordinate first-error coefficient has genuine coarse
covariant jets through two, with one common r, r beta, r beta squared
budget. The first derivative families are smooth and fixed before tests. -/
theorem uniform_physical_first_error_coordinate_coarse_two_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ CF CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ∀ b i : I,ContDiffOn ℝ ∞ (S b i) Y ∧ ∀ y ∈ Y,
          CoarseCovariantRotationGraph d y (axis i)
            (principalFirstErrorCoordinateCoarseL d P.adjoint P.center b) (S b i y) ∧
          ‖principalFirstErrorCoordinateCoarseL d P.adjoint P.center b y‖ ≤ C*d.radius y ∧
          ‖S b i y‖ ≤ C*d.radius y*beta d.γ d.radius y ∧
          ∀ j : I,∃ T : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
            CoarseCovariantRotationGraph d y (axis j) (S b i) T ∧
            ‖T‖ ≤ C*d.radius y*(beta d.γ d.radius y)^2 := by
  classical
  obtain ⟨η0,C0,hη0,hη01,hC0,hZero⟩ :=
    uniform_physical_coarse_axis_first_error_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨η2,C1,C2,hη2,hη21,hC1,hC2,hTwo⟩ :=
    uniform_actual_first_error_covariant_two_jets hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let B := principalFirstErrorCoordinateTwoJetBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
  let A := C0+2*C1+C2
  let C := 3*B*A
  have hB : 0 ≤ B := principalFirstErrorCoordinateTwoJetBudget_nonneg _ _ _ _
    (zero_le_one.trans hK) (abs_nonneg _) (abs_nonneg _)
  have hA : 0 ≤ A := by dsimp only [A];positivity
  have h0A : C0 ≤ A := by dsimp only [A];linarith only [hC1,hC2]
  have h1A : C0+C1 ≤ A := by dsimp only [A];linarith only [hC1,hC2]
  refine ⟨min η0 η2,C,lt_min hη0 hη2,(min_le_left _ _).trans hη01,by dsimp only [C];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  have hε1 : ε ≤ 1 := hSmall.trans ((min_le_left _ _).trans hη01)
  have hE0 := hZero floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CF CT P
  choose Sa hSaS hSa using fun a : I => hTwo floor hf ε hε (hSmall.trans (min_le_right _ _))
    d hd P.radial P.adjoint P.adjoint_smooth P.radial_actual P.adjoint_pair (axis a)
      (P.center a) (P.center_smooth a) (P.center_actual a)
  let E := fun (a : I) => actualFirstAdjointErrorFamily d (axis a) P.adjoint (P.center a)
  let w := fun (a b : I) => principalFirstErrorCoordinateWeight d a b
  let S := fun (b i : I) (x : X) => ∑ a : I,
    (w a b x • Sa a x (axis i)+fderiv ℝ (w a b) x (axis i) • E a x)
  have hES (a : I) : ContDiffOn ℝ ∞ (E a) Y :=
    contDiffOn_actualFirstAdjointErrorFamily (axis a) hY hΩ hSub hd.1 (zero_lt_one.trans_le hK)
      hd.2.2.2.2.1.1 (fun x hx => (hd.2.2.2.2.1.2 x hx).1) P.adjoint (P.center a)
      P.adjoint_smooth (P.center_smooth a)
  have hWS (a b : I) : ContDiffOn ℝ ∞ (w a b) Y :=
    hd.contDiffOn_principalFirstErrorCoordinateWeight (zero_lt_one.trans_le hK) a b
  have hWDS (a b i : I) : ContDiffOn ℝ ∞ (fun x => fderiv ℝ (w a b) x (axis i)) Y :=
    contDiffOn_coordDeriv hY (hWS a b) i
  have hSSa (a i : I) : ContDiffOn ℝ ∞ (fun x => Sa a x (axis i)) Y :=
    (hSaS a).clm_apply contDiffOn_const
  have hTermS (a b i : I) : ContDiffOn ℝ ∞ (fun x =>
      w a b x • Sa a x (axis i)+fderiv ℝ (w a b) x (axis i) • E a x) Y :=
    ((hWS a b).smul (hSSa a i)).add ((hWDS a b i).smul (hES a))
  have hSS (b i : I) : ContDiffOn ℝ ∞ (S b i) Y := ContDiffOn.sum (fun a _ => hTermS a b i)
  refine ⟨S,?_⟩
  intro b i
  refine ⟨hSS b i,?_⟩
  intro y hy
  let r := d.radius y
  let β := beta d.γ d.radius y
  have hr : 0 ≤ r := (hd.2.2.2.2.1.2 y hy).1.le
  have hβ : 0 ≤ β := zero_le_one.trans (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  have hw (a i j : I) := hd.principalFirstErrorCoordinateWeight_two_jet_bounds hY (by omega)
    hK hf hε hε1 hy a b i j
  have hSN (a k : I) : ‖Sa a y (axis k)‖ ≤ C1*r*β := by
    have hDir := (Sa a y).le_opNorm (axis k)
    rw [norm_axis,mul_one] at hDir
    exact hDir.trans (by simpa only [norm_axis,mul_one] using (hSa a y hy).2.1)
  have hFirstGraph : CoarseCovariantRotationGraph d y (axis i)
      (principalFirstErrorCoordinateCoarseL d P.adjoint P.center b) (S b i y) := by
    exact CoarseCovariantRotationGraph.sum_three (fun a x => w a b x • E a x)
      (fun a => w a b y • Sa a y (axis i)+fderiv ℝ (w a b) y (axis i) • E a y)
      (fun a => ((hSa a y hy).1 (axis i)).smul (w a b)
        (((hWS a b).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        (((hES a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)))
      (fun a => (((hWS a b).smul (hES a)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
  have hZeroN : ‖principalFirstErrorCoordinateCoarseL d P.adjoint P.center b y‖ ≤ C*r := by
    have hh := norm_weighted_sum_three_le (fun a => w a b y) (fun a => E a y) B (C0*r) hB
      (fun a => (hw a i i).1) (fun a => hE0 a y hy)
    exact hh.trans (by
      calc
        3*B*(C0*r) = (3*B*C0)*r := by ring
        _ ≤ (3*B*A)*r := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h0A (mul_nonneg (by norm_num) hB)) hr
        _ = C*r := rfl)
  have hFirstN : ‖S b i y‖ ≤ C*r*β := by
    have hOne (a : I) : ‖w a b y • Sa a y (axis i)+fderiv ℝ (w a b) y (axis i) • E a y‖ ≤
        B*(C0+C1)*r*β := by
      have h0 : ‖w a b y • Sa a y (axis i)‖ ≤ B*(C1*r*β) := by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul (hw a i i).1 (hSN a i) (norm_nonneg _) hB
      have h1 : ‖fderiv ℝ (w a b) y (axis i) • E a y‖ ≤ (B*β)*(C0*r) := by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul (hw a i i).2.1 (hE0 a y hy) (norm_nonneg _) (mul_nonneg hB hβ)
      exact ((norm_add_le _ _).trans (add_le_add h0 h1)).trans_eq (by ring)
    calc
      _ ≤ ∑ a : I,‖w a b y • Sa a y (axis i)+fderiv ℝ (w a b) y (axis i) • E a y‖ := norm_sum_le _ _
      _ ≤ ∑ _a : I,B*(C0+C1)*r*β := Finset.sum_le_sum (fun a _ => hOne a)
      _ = 3*B*(C0+C1)*r*β := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring
      _ ≤ C*r*β := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h1A (mul_nonneg (by norm_num) hB)) hr) hβ
  refine ⟨hFirstGraph,hZeroN,hFirstN,?_⟩
  intro j
  have hSecond (a : I) : ∃ T : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      CoarseCovariantRotationGraph d y (axis j) (fun x => Sa a x (axis i)) T ∧
      ‖T‖ ≤ C2*r*β^2 := by
    have hh := (hSa a y hy).2.2 (axis i) (axis j)
      (by simpa only [norm_axis] using (le_refl (1:ℝ)))
      (by simpa only [norm_axis] using (le_refl (1:ℝ)))
    simpa only [norm_axis,mul_one] using hh
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
        ((hSa a y hy).1 (axis j)) (hTa a))
      (fun a => ((hTermS a b i).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
  · have hOne (a : I) : ‖terms a‖ ≤ B*(C2+2*C1+C0)*r*β^2 := by
      exact norm_coarse_second_weighted_jet_le (E a y) (Sa a y (axis i)) (Sa a y (axis j)) (Ta a)
        (w a b y) (fderiv ℝ (w a b) y (axis i)) (fderiv ℝ (w a b) y (axis j))
        (fderiv ℝ (fun x => fderiv ℝ (w a b) x (axis i)) y (axis j))
        B C0 C1 C2 r β hB hβ (hw a i j).1 (hw a i j).2.1 (hw a j i).2.1
        (hw a i j).2.2 (hE0 a y hy) (hSN a i) (hSN a j)
        (hTaN a)
    calc
      _ ≤ ∑ a : I,‖terms a‖ := norm_sum_le _ _
      _ ≤ ∑ _a : I,B*(C2+2*C1+C0)*r*β^2 := Finset.sum_le_sum (fun a _ => hOne a)
      _ = C*r*β^2 := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,C,A]
        ring

/-- The original r beta squared smallness makes the SAME coordinate
error's first and second covariant graphs O(epsilon). -/
theorem uniform_physical_first_error_coordinate_second_covariant_small {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ CF CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ∀ b i : I,ContDiffOn ℝ ∞ (S b i) Y ∧ ∀ y ∈ Y,
          CoarseCovariantRotationGraph d y (axis i)
            (principalFirstErrorCoordinateCoarseL d P.adjoint P.center b) (S b i y) ∧
          ‖S b i y‖ ≤ C*ε ∧
          ∀ j : I,∃ T : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
            CoarseCovariantRotationGraph d y (axis j) (S b i) T ∧ ‖T‖ ≤ C*ε := by
  obtain ⟨η,C,hη,hη1,hC,hTwo⟩ :=
    uniform_physical_first_error_coordinate_coarse_two_jets hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,C,hη,hη1,hC,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  obtain ⟨S,hS⟩ := hTwo floor hf ε hε hSmall d hd CF CT P
  refine ⟨S,?_⟩
  intro b i
  refine ⟨(hS b i).1,?_⟩
  intro y hy
  have hData := (hS b i).2 y hy
  have hr : 0 ≤ d.radius y := (hd.2.2.2.2.1.2 y hy).1.le
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hrβ2 := (hd.2.2.2.2.2 y hy).2
  have hrβ : d.radius y*beta d.γ d.radius y ≤ ε := by
    have hPow : beta d.γ d.radius y ≤ (beta d.γ d.radius y)^2 := by
      nlinarith only [mul_le_mul_of_nonneg_left hβ (zero_le_one.trans hβ)]
    exact (mul_le_mul_of_nonneg_left hPow hr).trans hrβ2
  refine ⟨hData.1,?_,?_⟩
  · exact hData.2.2.1.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrβ hC)
  · intro j
    obtain ⟨T,hT,hTN⟩ := hData.2.2.2 j
    refine ⟨T,hT,hTN.trans ?_⟩
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrβ2 hC

end ShrinkingSpheres

module

public import Proof.CalderonN.NormalizedCoefficientThirdJet
public import Proof.CalderonN.ActualAngularCoefficientJets

import Proof.CalderonN.CenterJetCalculus
import Mathlib.Tactic

/-! Two rotations of the actual normalized coefficient retain a scalar
linear term and a quadratic first-jet error. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4700000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private def angularCoefficientMatrixCommute (i j : Fin dim) : Mat dim →L[ℝ] Mat dim := by
  let B := coordinateMatrix (ballRotationGeneratorL i j)
  exact (⟨⟨fun A => A*B-B*A,fun A C => by rw [add_mul,mul_add]; abel⟩,
    fun c A => by
      change (c • A)*B-B*(c • A) = c • (A*B-B*A)
      rw [smul_mul_assoc,mul_smul_comm,smul_sub]⟩ : Mat dim →ₗ[ℝ] Mat dim).toContinuousLinearMap

theorem norm_iteratedFDeriv_ballRotationCoefficient_two_le (dim : ℕ) [NeZero dim] [Nontrivial (Fin dim)] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i j : Fin dim) {a : X dim → Mat dim}, ContDiff ℝ ∞ a →
      ∀ z : X dim, ‖z‖ ≤ 2 → ∀ q ≥ 0,
      (∀ k, k ≤ 3 → ‖iteratedFDeriv ℝ k a z‖ ≤ q) →
      ∀ k, k ≤ 2 → ‖iteratedFDeriv ℝ k (ballRotationCoefficient i j a) z‖ ≤ C*q := by
  let F : (X dim →L[ℝ] Mat dim) →L[ℝ] X dim →L[ℝ] Mat dim :=
    (ContinuousLinearMap.apply ℝ (Mat dim)).flip
  let S := ∑ i : Fin dim,∑ j : Fin dim,‖angularCoefficientMatrixCommute i j‖
  let C := 16*‖F‖+S
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro i j a ha z hz q hq hJets k hk
  let J := ballRotationGeneratorL i j
  let A := angularCoefficientMatrixCommute i j
  have hA : ‖A‖ ≤ S :=
    (Finset.single_le_sum (fun l _ => norm_nonneg (angularCoefficientMatrixCommute i l)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun p _ => norm_nonneg (angularCoefficientMatrixCommute l p))
        (Finset.mem_univ i))
  have hJ : ‖J‖ ≤ 2 := norm_ballRotationGeneratorL_le i j
  have hJz : ‖J z‖ ≤ 4 :=
    (J.le_opNorm z).trans ((mul_le_mul hJ hz (norm_nonneg _) (by norm_num)).trans_eq (by norm_num))
  have hJk (l : ℕ) (hl : l ≤ k) : ‖iteratedFDeriv ℝ l (⇑J) z‖ ≤ 4 := by
    have hl₂ := hl.trans hk
    interval_cases l
    · simpa only [norm_iteratedFDeriv_zero] using hJz
    · rw [norm_iteratedFDeriv_one,ContinuousLinearMap.fderiv]
      exact hJ.trans (by norm_num)
    · rw [← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one]
      have hDer : fderiv ℝ (⇑J) = fun _ => J := funext fun _ => J.fderiv
      rw [hDer,fderiv_fun_const,Pi.zero_apply,norm_zero]
      norm_num
  have ha' : ContDiff ℝ ∞ (fderiv ℝ a) := ha.fderiv_right (m:=∞) (by simp)
  have hDk (l : ℕ) (hl : l ≤ k) : ‖iteratedFDeriv ℝ l (fderiv ℝ a) z‖ ≤ q := by
    rw [norm_iteratedFDeriv_fderiv]
    exact hJets _ (by omega)
  have hRot : ballRotationCoefficient i j a =
      (fun w => F (fderiv ℝ a w) (J w))+(A ∘ a) := by
    funext w
    change fderiv ℝ a w (J w)+a w*coordinateMatrix J-coordinateMatrix J*a w =
      fderiv ℝ a w (J w)+(a w*coordinateMatrix J-coordinateMatrix J*a w)
    abel
  have h1 := norm_iteratedFDeriv_bilinear_envelope_at F (fderiv ℝ a) J z k ha'.contDiffAt
    J.contDiff.contDiffAt q 4 hq (by norm_num) hDk hJk
  have hPow : (2:ℝ)^k ≤ 4 := by interval_cases k <;> norm_num
  have h₁ : ‖iteratedFDeriv ℝ k (fun w => F (fderiv ℝ a w) (J w)) z‖ ≤ (16*‖F‖)*q := by
    exact h1.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPow (norm_nonneg F)) hq) (by norm_num)).trans_eq
        (by ring))
  have h₂ : ‖iteratedFDeriv ℝ k (A ∘ a) z‖ ≤ S*q :=
    (A.norm_iteratedFDeriv_comp_left (n:=k) ha.contDiffAt (by simp)).trans
      (mul_le_mul hA (hJets k (by omega)) (norm_nonneg _) hS)
  have hDir : ContDiffAt ℝ (k:ℕ∞ω) (fun w => F (fderiv ℝ a w) (J w)) z := by
    have h : ContDiff ℝ ∞ (fun w => F (fderiv ℝ a w) (J w)) := (F.contDiff.comp ha').clm_apply J.contDiff
    exact h.contDiffAt.of_le (by simp)
  have hComm : ContDiffAt ℝ (k:ℕ∞ω) (A ∘ a) z := (A.contDiff.comp ha).contDiffAt.of_le (by simp)
  rw [hRot,iteratedFDeriv_add_apply hDir hComm]
  exact ((norm_add_le _ _).trans (add_le_add h₁ h₂)).trans_eq (by dsimp [C]; ring)

private theorem ballRotationCoefficient_add_identity (i j : Fin dim)
    {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a) :
    ballRotationCoefficient i j (fun z => 1+a z) = ballRotationCoefficient i j a := by
  funext z
  let J := ballRotationGeneratorL i j
  let C := coordinateMatrix J
  have hD := ((ha.differentiable (by simp) z).hasFDerivAt.const_add (1 : Mat dim)).fderiv
  change fderiv ℝ (fun w => 1+a w) z (J z)+(1+a z)*C-C*(1+a z) =
    fderiv ℝ a z (J z)+a z*C-C*a z
  rw [hD,add_mul,mul_add,one_mul,mul_one]
  abel

private theorem affine_rotate_once (i j : Fin dim) (ell : X dim →L[ℝ] ℝ)
    (r : ℝ) {R : X dim → Mat dim} (hR : ContDiff ℝ ∞ R) :
    ballRotationCoefficient i j (fun z => r • (ell z • (1 : Mat dim))+R z) =
      fun z => r • ((ell.comp (ballRotationGeneratorL i j)) z • (1 : Mat dim))+
        ballRotationCoefficient i j R z := by
  have ha : ContDiff ℝ ∞ (fun z => r • (ell z • (1 : Mat dim))+R z) :=
    ((ell.contDiff.smul contDiff_const).const_smul r).add hR
  rw [← ballRotationCoefficient_add_identity i j ha]
  have hEq : (fun z => 1+(r • (ell z • (1 : Mat dim))+R z)) =
      fun z => (1+r*ell z) • (1 : Mat dim)+R z := by
    funext z
    rw [add_smul,one_smul,mul_smul,add_assoc]
  rw [hEq,ballRotationCoefficient_affine i j ell r R hR]

theorem uniform_actual_double_angular_coefficient_jets (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 5 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η P Q : ℝ, 0 < η ∧ 0 ≤ P ∧ 0 ≤ Q ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let r := d.radius y
      let ell := firstDensityCenterLinear d y
      ‖ell‖ ≤ P ∧ ∀ A : X dim → Mat dim, ContDiff ℝ ∞ A →
        EqOn A (fun z => firstNormalVelocityCoefficient d y (r • frameVector d.frame y z))
          (ball (0 : X dim) (5/4)) →
        ∀ (i j k l : Fin dim), let ell₂ := (ell.comp (ballRotationGeneratorL i j)).comp (ballRotationGeneratorL k l)
          let R₂ := fun z => ballRotationCoefficient k l (ballRotationCoefficient i j A) z -
            r • (ell₂ z • (1 : Mat dim))
          ‖ell₂‖ ≤ 4*P ∧ ∀ z ∈ closedBall (0 : X dim) 1,
            ‖R₂ z‖ ≤ Q*r^2 ∧ ‖fderiv ℝ R₂ z‖ ≤ Q*r^2 := by
  obtain ⟨η₂,Q₂,hη₂,hQ₂,hC₂⟩ := uniform_normalized_coefficient_remainder_C2 (Y:=Y)
    hn hΩ (by omega) K ρ c₀ M Cj hK hρ 1 zero_le_one
  obtain ⟨η₃,Q₃,hη₃,hQ₃,hC₃⟩ := uniform_actual_normalized_coefficient_third_jet (Y:=Y)
    hn hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η_P,P,hη_P,hP,hEll⟩ := uniform_actual_radial_weight_remainder (Y:=Y)
    hn hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨C,hC,hRot⟩ := norm_iteratedFDeriv_ballRotationCoefficient_two_le dim
  let Q := (6+4*(dim:ℝ))*C*(Q₂+Q₃)
  refine ⟨min η_P (min η₂ η₃),P,Q,lt_min hη_P (lt_min hη₂ hη₃),hP,by dsimp [Q]; positivity,?_⟩
  intro floor hf ε he hs d hd y hy
  dsimp only
  let r := d.radius y
  let ell := firstDensityCenterLinear d y
  have hℓ := (hEll floor hf ε he (hs.trans (min_le_left _ _)) d hd y hy).1
  refine ⟨hℓ,?_⟩
  intro A hA hEq i j k l
  let J₁ := ballRotationGeneratorL i j
  let J₂ := ballRotationGeneratorL k l
  let ell₁ := ell.comp J₁
  let ell₂ := ell₁.comp J₂
  let R := fun z => A z-(1+r*ell z) • (1 : Mat dim)
  let R₁ := ballRotationCoefficient i j R
  let R₂ := ballRotationCoefficient k l R₁
  have hR : ContDiff ℝ ∞ R := hA.sub ((contDiff_const.add (contDiff_const.mul ell.contDiff)).smul contDiff_const)
  have hR₁ : ContDiff ℝ ∞ R₁ := contDiff_ballRotationCoefficient i j hR
  have hA₁ : ballRotationCoefficient i j A = fun z => r • (ell₁ z • (1 : Mat dim))+R₁ z := by
    have he' : A = fun z => (1+r*ell z) • (1 : Mat dim)+R z := by funext z; dsimp [R]; abel
    rw [he',ballRotationCoefficient_affine]
    exact hR
  have hA₂ : (fun z => ballRotationCoefficient k l (ballRotationCoefficient i j A) z-
      r • (ell₂ z • (1 : Mat dim))) = R₂ := by
    rw [hA₁,affine_rotate_once k l ell₁ r hR₁]
    funext z
    change r • (ell₂ z • (1 : Mat dim))+R₂ z-r • (ell₂ z • (1 : Mat dim)) = R₂ z
    abel
  have hn₁ := (ell.opNorm_comp_le J₁).trans (mul_le_mul hℓ (norm_ballRotationGeneratorL_le i j)
    (norm_nonneg _) hP)
  refine ⟨((ell₁.opNorm_comp_le J₂).trans (mul_le_mul hn₁ (norm_ballRotationGeneratorL_le k l)
    (norm_nonneg _) (by positivity))).trans_eq (by ring),?_⟩
  intro z hz
  change ‖(fun w => ballRotationCoefficient k l (ballRotationCoefficient i j A) w-
      r • (ell₂ w • (1 : Mat dim))) z‖ ≤ Q*r^2 ∧
      ‖fderiv ℝ (fun w => ballRotationCoefficient k l (ballRotationCoefficient i j A) w-
        r • (ell₂ w • (1 : Mat dim))) z‖ ≤ Q*r^2
  rw [hA₂]
  have hB := hC₂ floor hf ε he (hs.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy z hz
  have h₃ := hC₃ floor hf ε he (hs.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd y hy z hz
  have hG : R =ᶠ[𝓝 z] normalizedFirstCoefficientRemainder d y := by
    filter_upwards [isOpen_ball.mem_nhds (closedBall_subset_ball (by norm_num : (1:ℝ) < 5/4) hz)]
      with w hw
    change A w-(1+r*ell w) • (1 : Mat dim) = _
    rw [hEq hw]
    rfl
  have hRbound (a : ℕ) (ha : a ≤ 3) : ‖iteratedFDeriv ℝ a R z‖ ≤ (Q₂+Q₃)*r^2 := by
    rw [(hG.iteratedFDeriv ℝ a).eq_of_nhds]
    have hQ : Q₂*r^2 ≤ (Q₂+Q₃)*r^2 := by gcongr; exact le_add_of_nonneg_right hQ₃
    interval_cases a
    · rw [norm_iteratedFDeriv_zero]; exact hB.2.1.trans hQ
    · rw [norm_iteratedFDeriv_one]; exact hB.2.2.1.trans hQ
    · rw [← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one]
      exact hB.2.2.2.1.trans hQ
    · exact h₃.trans (by gcongr; exact le_add_of_nonneg_left hQ₂)
  have hz₂ := (mem_closedBall_zero_iff.mp hz).trans (by norm_num : (1:ℝ) ≤ 2)
  have hRot₁ (n : ℕ) (hn : n ≤ 2) : ‖iteratedFDeriv ℝ n R₁ z‖ ≤ C*((Q₂+Q₃)*r^2) :=
    hRot i j hR z hz₂ _ (by positivity) hRbound n hn
  have h0 := hRot₁ 0 (by omega)
  have h1 := hRot₁ 1 (by omega)
  have h2 := hRot₁ 2 (by omega)
  rw [norm_iteratedFDeriv_zero] at h0
  rw [norm_iteratedFDeriv_one] at h1
  rw [← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one] at h2
  obtain ⟨h0',h1'⟩ := norm_ballRotationCoefficient_jets_le k l hR₁ z hz₂
    _ (by positivity) h0 h1 h2
  exact ⟨h0'.trans_eq (by dsimp [Q]; ring),h1'.trans_eq (by dsimp [Q]; ring)⟩

end CalderonN

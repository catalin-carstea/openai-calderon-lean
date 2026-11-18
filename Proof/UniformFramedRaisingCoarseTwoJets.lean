import Proof.FramedRaisingSecondCovariantGraph
import Proof.ConnectionOperatorBounds
import Proof.BackgroundBudgets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The genuine coframe raising operator and its two covariant jets have
common background bounds, independent of derivatives of the chosen frame. -/
theorem uniform_framed_raising_coarse_two_jet_bound {Y Ω : Set X}
    (hΩ : IsOpen Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ Q : ℝ,0 ≤ Q ∧ ∀ floor ε : ℝ,∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i j b : I,
      ‖framedFlatRaisingSobolevL 1 d.γ d.frame y (axis b)‖ ≤ Q ∧
      ‖framedRaisingFirstCoarseJet d i b y‖ ≤ Q ∧
      ‖framedRaisingSecondCoarseJet d i j b y‖ ≤ Q := by
  let M1 := |M ⟨1,by omega⟩|
  let M2 := |M ⟨2,by omega⟩|
  let R := 6*(9*|M 0| *K)
  let G := 27*(9*K*M1)
  let D := 81*K^2*M1^2+9*K*M2
  let T := 3*(G*(R*G)+D*R)
  let Q := R+R*G+T
  have hK0 := zero_le_one.trans hK
  have hKP := zero_lt_one.trans_le hK
  have hM1 : 0 ≤ M1 := abs_nonneg _
  have hM2 : 0 ≤ M2 := abs_nonneg _
  have hR : 0 ≤ R := by dsimp only [R];positivity
  have hG : 0 ≤ G := by dsimp only [G];positivity
  have hD : 0 ≤ D := by dsimp only [D];positivity
  have hRG : 0 ≤ R*G := mul_nonneg hR hG
  have hT : 0 ≤ T := by dsimp only [T];positivity
  have hRQ : R ≤ Q := by dsimp only [Q];linarith only [hRG,hT]
  have hRGQ : R*G ≤ Q := by dsimp only [Q];linarith only [hR,hT]
  have hTQ : T ≤ Q := by dsimp only [Q];linarith only [hR,hRG]
  refine ⟨Q,by dsimp only [Q];positivity,?_⟩
  intro floor ε d hd y hy i j b
  have hyΩ := hd.2.1.center_mem hy
  have hMetric1 (a c : I) : ‖fderiv ℝ (fun x => d.γ x a c) y‖ ≤ M1 :=
    (hd.1.reference_fderiv_bound (by omega) hyΩ a c).trans (le_abs_self _)
  have hMetric2 (a c : I) : ‖fderiv ℝ (fderiv ℝ (fun x => d.γ x a c)) y‖ ≤ M2 :=
    (hd.1.reference_second_fderiv_bound hm hyΩ a c).trans (le_abs_self _)
  have hConn : ‖connectionBilinear d.γ y‖ ≤ G :=
    (hd.1.1.connection_operator_bounds hΩ hKP hyΩ M1 M2 hM1 hM2 hMetric1 hMetric2).1
  have hConnApply (a c : I) : ‖connection d.γ y (axis a) (axis c)‖ ≤ G := by
    rw [← connectionBilinear_apply]
    exact (ContinuousLinearMap.le_opNorm₂ _ _ _).trans
      (by simpa only [norm_axis,mul_one] using hConn)
  have hRaise (v : X) : ‖framedFlatRaisingSobolevL 1 d.γ d.frame y v‖ ≤ R*‖v‖ :=
    (hd.framedFlatRaisingSobolevL_norms hK hy v).1
  have hRaiseAxis (a : I) : ‖framedFlatRaisingSobolevL 1 d.γ d.frame y (axis a)‖ ≤ R := by
    simpa only [norm_axis,mul_one] using hRaise (axis a)
  have hRaiseConn (a c : I) :
      ‖framedFlatRaisingSobolevL 1 d.γ d.frame y (connection d.γ y (axis a) (axis c))‖ ≤ R*G :=
    (hRaise _).trans (mul_le_mul_of_nonneg_left (hConnApply a c) hR)
  have hGamma (a : I) : |christoffel d.γ y a i b| ≤ G := by
    exact (hd.1.1.christoffel_entry_bound hKP hyΩ M1 hM1 hMetric1 a i b).trans
      (by
        change 9*K*M1 ≤ 27*(9*K*M1)
        have hNonneg : 0 ≤ 9*K*M1 := by positivity
        nlinarith only [hNonneg])
  have hGammaD (a : I) : |fderiv ℝ (fun x => christoffel d.γ x a i b) y (axis j)| ≤ D := by
    simpa only [norm_axis,mul_one] using
      hd.1.1.christoffel_derivative_entry_bound hΩ hKP hyΩ M1 M2 hM1 hM2 hMetric1 hMetric2 (axis j) a i b
  have hSecond : ‖framedRaisingSecondCoarseJet d i j b y‖ ≤ T := by
    have hOne (a : I) : ‖christoffel d.γ y a i b •
          framedFlatRaisingSobolevL 1 d.γ d.frame y (connection d.γ y (axis j) (axis a))+
        fderiv ℝ (fun x => christoffel d.γ x a i b) y (axis j) •
          framedFlatRaisingSobolevL 1 d.γ d.frame y (axis a)‖ ≤ G*(R*G)+D*R := by
      have h0 : ‖christoffel d.γ y a i b •
          framedFlatRaisingSobolevL 1 d.γ d.frame y (connection d.γ y (axis j) (axis a))‖ ≤ G*(R*G) := by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul (hGamma a) (hRaiseConn j a) (norm_nonneg _) hG
      have h1 : ‖fderiv ℝ (fun x => christoffel d.γ x a i b) y (axis j) •
          framedFlatRaisingSobolevL 1 d.γ d.frame y (axis a)‖ ≤ D*R := by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul (hGammaD a) (hRaiseAxis a) (norm_nonneg _) hD
      exact (norm_add_le _ _).trans (add_le_add h0 h1)
    calc
      _ ≤ ∑ a : I,‖christoffel d.γ y a i b •
          framedFlatRaisingSobolevL 1 d.γ d.frame y (connection d.γ y (axis j) (axis a))+
        fderiv ℝ (fun x => christoffel d.γ x a i b) y (axis j) •
          framedFlatRaisingSobolevL 1 d.γ d.frame y (axis a)‖ := norm_sum_le _ _
      _ ≤ ∑ _a : I,(G*(R*G)+D*R) := Finset.sum_le_sum (fun a _ => hOne a)
      _ = T := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,T]
        norm_num
  refine ⟨(hRaiseAxis b).trans hRQ,?_,hSecond.trans hTQ⟩
  rw [framedRaisingFirstCoarseJet_eq]
  exact (hRaiseConn i b).trans hRGQ

end ShrinkingSpheres

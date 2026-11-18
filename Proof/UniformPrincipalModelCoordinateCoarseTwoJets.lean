import Proof.PrincipalModelCoordinateCoarseGraphs
import Proof.PrincipalModelDegreeCoordinateTwoJets
import Proof.PrincipalModelRaisingCoordinateTwoJets
import Proof.UniformFramedRaisingCoarseTwoJets
import Proof.CoarseCovariantSmallTwoJetProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The SAME complete physical model first-coordinate coefficient has
genuine first/second covariant graphs with epsilon/beta, epsilon and
epsilon beta coarse bounds, under exactly the original hypotheses. -/
theorem uniform_principal_model_coordinate_coarse_two_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ b i j : I,∀ y ∈ Y,
      CoarseCovariantRotationGraph d y (axis i) (principalModelCoordinateCoarseL d b)
        (principalModelCoordinateFirstCoarseJet d b i y) ∧
      CoarseCovariantRotationGraph d y (axis j) (principalModelCoordinateFirstCoarseJet d b i)
        (principalModelCoordinateSecondCoarseJet d b i j y) ∧
      ‖principalModelCoordinateCoarseL d b y‖ ≤ C*ε/beta d.γ d.radius y ∧
      ‖principalModelCoordinateFirstCoarseJet d b i y‖ ≤ C*ε ∧
      ‖principalModelCoordinateSecondCoarseJet d b i j y‖ ≤ C*ε*beta d.γ d.radius y := by
  obtain ⟨Q0,hQ0,hRaising⟩ := uniform_framed_raising_coarse_two_jet_bound hΩ hm K ρ c₀ M Cj hK
  let BD := principalModelDegreeCoordinateTwoJetBudget K (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2) (Cj 3)
  let B := BD+2
  let Q := Q0+2
  let C := 16*B*Q
  have hBD : 0 ≤ BD := principalModelDegreeCoordinateTwoJetBudget_nonneg _ _ _ _ _ (zero_le_one.trans hK)
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hQ : 0 ≤ Q := by dsimp only [Q];positivity
  have hBDB : BD ≤ B := by exact le_add_of_nonneg_right (by norm_num)
  have h2B : 2 ≤ B := by dsimp only [B];linarith only [hBD]
  have hQ0Q : Q0 ≤ Q := le_add_of_nonneg_right (by norm_num)
  have h2Q : 2 ≤ Q := by dsimp only [Q];linarith only [hQ0]
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  intro floor hf ε hε hε1 d hd b i j y hy
  let β := beta d.γ d.radius y
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβ0 : 0 ≤ β := zero_le_one.trans hβ
  have hBε : 0 ≤ B*ε := mul_nonneg hB hε
  have hBεGrow : B*ε ≤ B*ε*β := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ hBε
  have hD (k l : I) := hd.principalModelDegreeCoordinateWeight_two_jet_bounds hY hm hK hf hε hε1 hy b k l
  have hD0 : |principalModelDegreeCoordinateWeight d b y| ≤ B*ε/β :=
    (hD i j).2.1.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBDB hε) hβ0)
  have hD1 (k : I) : |fderiv ℝ (principalModelDegreeCoordinateWeight d b) y (axis k)| ≤ B*ε :=
    (hD k k).2.2.1.trans (mul_le_mul_of_nonneg_right hBDB hε)
  have hD2 : |fderiv ℝ (fun x => fderiv ℝ (principalModelDegreeCoordinateWeight d b) x (axis i)) y (axis j)| ≤
      B*ε*β := (hD i j).2.2.2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBDB hε) hβ0)
  have hDegree := coarse_small_two_jet_product_bounds sphereSobolevDegreeL 0 0 0
    (principalModelDegreeCoordinateWeight d b y)
    (fderiv ℝ (principalModelDegreeCoordinateWeight d b) y (axis i))
    (fderiv ℝ (principalModelDegreeCoordinateWeight d b) y (axis j))
    (fderiv ℝ (fun x => fderiv ℝ (principalModelDegreeCoordinateWeight d b) x (axis i)) y (axis j))
    B Q ε β hB hε hβ hD0 (hD1 i) (hD1 j) hD2
    (norm_sphereSobolevDegreeL_le_two.trans h2Q)
    (by simpa only [norm_zero] using hQ) (by simpa only [norm_zero] using hQ)
    (by simpa only [norm_zero] using hQ)
  simp only [smul_zero,zero_add,add_zero] at hDegree
  have hRaise (a : I) :
      ‖principalModelRaisingCoordinateWeight d a b y • framedFlatRaisingSobolevL 1 d.γ d.frame y (axis a)‖ ≤ B*Q*ε/β ∧
      ‖principalModelRaisingCoordinateWeight d a b y • framedRaisingFirstCoarseJet d i a y+
        fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i) •
          framedFlatRaisingSobolevL 1 d.γ d.frame y (axis a)‖ ≤ 2*B*Q*ε ∧
      ‖(principalModelRaisingCoordinateWeight d a b y • framedRaisingSecondCoarseJet d i j a y+
        fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis j) • framedRaisingFirstCoarseJet d i a y)+
        (fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i) • framedRaisingFirstCoarseJet d j a y+
          fderiv ℝ (fun x => fderiv ℝ (principalModelRaisingCoordinateWeight d a b) x (axis i)) y (axis j) •
            framedFlatRaisingSobolevL 1 d.γ d.frame y (axis a))‖ ≤ 4*B*Q*ε*β := by
    have hw (k l : I) := hd.principalModelRaisingCoordinateWeight_two_jet_bounds hY hK hf hε hε1 hy a b k l
    have hN := hRaising floor ε d hd y hy i j a
    have hNj := hRaising floor ε d hd y hy j j a
    exact coarse_small_two_jet_product_bounds
      (framedFlatRaisingSobolevL 1 d.γ d.frame y (axis a)) (framedRaisingFirstCoarseJet d i a y)
      (framedRaisingFirstCoarseJet d j a y) (framedRaisingSecondCoarseJet d i j a y)
      (principalModelRaisingCoordinateWeight d a b y)
      (fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i))
      (fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis j))
      (fderiv ℝ (fun x => fderiv ℝ (principalModelRaisingCoordinateWeight d a b) x (axis i)) y (axis j))
      B Q ε β hB hε hβ
      ((hw i j).1.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2B hε) hβ0))
      ((hw i j).2.1.trans (mul_le_mul_of_nonneg_right h2B hε))
      ((hw j i).2.1.trans (mul_le_mul_of_nonneg_right h2B hε))
      ((hw i j).2.2.trans ((mul_le_mul_of_nonneg_right h2B hε).trans hBεGrow))
      (hN.1.trans hQ0Q) (hN.2.1.trans hQ0Q) (hNj.2.1.trans hQ0Q) (hN.2.2.trans hQ0Q)
  have hSum (F : I → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (A : ℝ)
      (hF : ∀ a,‖F a‖ ≤ A) : ‖∑ a : I,F a‖ ≤ 3*A := by
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun a _ => hF a)).trans_eq
      (by simp only [Fin.sum_univ_three];ring))
  have hGraphs := hd.principalModelCoordinate_coarse_covariant_graphs hY hΩ (zero_lt_one.trans_le hK) hy b i j
  refine ⟨hGraphs.1,hGraphs.2,?_,?_,?_⟩
  · have hh : ‖principalModelCoordinateCoarseL d b y‖ ≤ B*Q*ε/β+3*(B*Q*ε/β) :=
      (norm_add_le _ _).trans (add_le_add hDegree.1 (hSum _ _ (fun a => (hRaise a).1)))
    exact hh.trans (by
      calc
        _ = 4*(B*Q*ε/β) := by ring
        _ ≤ 16*(B*Q*ε/β) := mul_le_mul_of_nonneg_right (by norm_num)
          (div_nonneg (mul_nonneg (mul_nonneg hB hQ) hε) hβ0)
        _ = C*ε/β := by dsimp only [C];ring)
  · have hh : ‖principalModelCoordinateFirstCoarseJet d b i y‖ ≤ 2*B*Q*ε+3*(2*B*Q*ε) :=
      (norm_add_le _ _).trans (add_le_add hDegree.2.1 (hSum _ _ (fun a => (hRaise a).2.1)))
    exact hh.trans (by
      calc
        _ = 8*(B*Q*ε) := by ring
        _ ≤ 16*(B*Q*ε) := mul_le_mul_of_nonneg_right (by norm_num)
          (mul_nonneg (mul_nonneg hB hQ) hε)
        _ = C*ε := by dsimp only [C];ring)
  · have hh : ‖principalModelCoordinateSecondCoarseJet d b i j y‖ ≤ 4*B*Q*ε*β+3*(4*B*Q*ε*β) :=
      (norm_add_le _ _).trans (add_le_add hDegree.2.2 (hSum _ _ (fun a => (hRaise a).2.2)))
    exact hh.trans_eq (by dsimp only [C];ring)

end ShrinkingSpheres

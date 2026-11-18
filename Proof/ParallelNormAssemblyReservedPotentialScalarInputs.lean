import Proof.ParallelNormAssemblyReservedScalarJetAlgebra
import Proof.ParallelNormAssemblyReservedPurePotentialJets
import Proof.ProfileLogThirdJet
import Proof.ScalarPrincipalSharpTwoJets
import Proof.BackgroundBudgets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy

/-- Original profile and small-tensor assumptions control all scalar
inputs of the complete radius-normalized potential through two jets.
Every constant is chosen before the radius and frame. -/
theorem uniform_potential_scalar_inputs_two_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ Cr Cl Cp Ce : ℝ,0 ≤ Cr ∧ 0 ≤ Cl ∧ 0 ≤ Cp ∧ 0 ≤ Ce ∧
    ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
    let β := beta d.γ d.radius y
    ScalarTwoJetBound d.radius y β (Cr/β) ∧
    (∀ a : I,ScalarTwoJetBound (coordDeriv a (fun x => Real.log (d.radius x))) y β (Cl*β)) ∧
    (∀ a b : I,ScalarTwoJetBound (fun x => scalarPrincipalMatrix d.γ d.g₂ d.radius x a b) y β (Cp*ε/β^2)) ∧
    (∀ a b : I,ScalarTwoJetBound
      (fun x => potentialCoordinateWordCoefficient d x (.inr (.inl a)) (.inr (.inl b))) y β (Ce*ε)) := by
  obtain ⟨Ce,hCe,hPure⟩ := uniform_pure_raising_potential_two_jet_weights hY hSub (by omega) K ρ c₀ M Cj hK
  let M1 := |M ⟨1,by omega⟩|
  let M2 := |M ⟨2,by omega⟩|
  let G := 9*K*M1
  let DG := 81*K^2*M1^2+9*K*M2
  let R2 := K^2+9*K^2*|Cj 2|+3*G*K
  let Cr := 1+K+R2
  let L2 := 9*K^2*|Cj 2|+3*G*K
  let L3 := profileLogThirdBudget K G DG (Cj 2) (Cj 3)
  let Cl := K+L2+L3
  let P0 := principalZeroBudget K
  let P1 := principalFirstBudget K M1
  let P2 := principalSecondBudget K M1 M2 (Cj 2)
  let Cp := P0+P1+P2
  have hK0 := zero_le_one.trans hK
  have hG : 0 ≤ G := by dsimp only [G,M1];positivity
  have hDG : 0 ≤ DG := by dsimp only [DG,M1,M2];positivity
  have hR2 : 0 ≤ R2 := by dsimp only [R2];positivity
  have hL2 : 0 ≤ L2 := by dsimp only [L2];positivity
  have hL3 : 0 ≤ L3 := profileLogThirdBudget_nonneg _ _ _ _ _ hK0 hG hDG
  have hP0 : 0 ≤ P0 := by dsimp only [P0,principalZeroBudget];positivity
  have hP1 : 0 ≤ P1 := by dsimp only [P1,principalFirstBudget,M1];positivity
  have hP2 : 0 ≤ P2 := by dsimp only [P2,principalSecondBudget,M1,M2];positivity
  have hCr : 0 ≤ Cr := by dsimp only [Cr];positivity
  have hCl : 0 ≤ Cl := by dsimp only [Cl];positivity
  have hCp : 0 ≤ Cp := by dsimp only [Cp];positivity
  refine ⟨Cr,Cl,Cp,Ce,hCr,hCl,hCp,hCe,?_⟩
  intro floor hf ε hε hε1 d hd y hy
  dsimp only
  let β := beta d.γ d.radius y
  have hβ1 : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβ : 0 < β := zero_lt_one.trans_le hβ1
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hRβ : d.radius y*β ≤ 1 :=
    ((radius_bounds (d.radius y) β floor ε hr.le hf (hd.2.2.2.2.1.2 y hy).2.1
      (hd.2.2.2.2.2 y hy).2).2.1.trans (div_le_self hε hf)).trans hε1
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ :=
    ⟨fun a b => (hd.1.2.2.1.1 a b).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have he (x : X) (hx : x ∈ Y) := hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hMetric1 (a b : I) : ‖fderiv ℝ (fun x => d.γ x a b) y‖ ≤ M1 :=
    (hd.1.reference_fderiv_bound (by omega) (hSub hy) a b).trans (le_abs_self _)
  have hMetric2 (a b : I) : ‖fderiv ℝ (fderiv ℝ (fun x => d.γ x a b)) y‖ ≤ M2 :=
    (hd.1.reference_second_fderiv_bound hm (hSub hy) a b).trans (le_abs_self _)
  have hΓ (a b c : I) : |christoffel d.γ y a b c| ≤ G :=
    hg.christoffel_entry_bound (zero_lt_one.trans_le hK) hy M1 (abs_nonneg _) hMetric1 a b c
  have hDΓ (a b c e : I) : |coordDeriv a (fun x => christoffel d.γ x b c e) y| ≤ DG := by
    have hh := hd.1.1.christoffel_derivative_entry_bound hΩ (zero_lt_one.trans_le hK) (hSub hy)
      M1 M2 (abs_nonneg _) (abs_nonneg _) hMetric1 hMetric2 (axis a) b c e
    simpa only [norm_axis,mul_one,coordDeriv,DG] using hh
  have hKCr : K ≤ Cr := by dsimp only [Cr];linarith only [hR2]
  have hR2Cr : R2 ≤ Cr := by dsimp only [Cr];linarith only [hK0]
  have hOneCr : 1 ≤ Cr := by dsimp only [Cr];linarith only [hK0,hR2]
  have hRad : ScalarTwoJetBound d.radius y β (Cr/β) := by
    constructor
    · rw [abs_of_pos hr]
      exact (le_div_iff₀ hβ).mpr (hRβ.trans hOneCr)
    · intro i
      have hh := hd.2.2.2.2.1.coordinate_radius_first_bound hY hg hK d.frame he hy i
      calc
        _ ≤ K*(d.radius y*β) := hh.trans_eq (by ring)
        _ ≤ Cr := (mul_le_mul_of_nonneg_left hRβ hK0).trans_eq (mul_one K) |>.trans hKCr
        _ = Cr/β*β := by field_simp
    · intro i j
      have hh := hd.2.2.2.2.1.coordinate_radius_second_bound hY hg hK d.frame he hf hG hy hΓ j i
      calc
        _ ≤ R2*(d.radius y*β^2) := hh.trans_eq (by ring)
        _ = R2*(d.radius y*β)*β := by ring
        _ ≤ Cr*β := mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_left hRβ hR2).trans_eq (mul_one R2) |>.trans hR2Cr) hβ.le
        _ = Cr/β*β^2 := by field_simp <;> ring
  refine ⟨hRad,?_,?_,?_⟩
  · intro a
    constructor
    · exact (hg.coord_logRadius_bound hK d.frame d.radius hy (he y hy) a).trans
        (mul_le_mul_of_nonneg_right (by dsimp only [Cl];linarith only [hL2,hL3]) hβ.le)
    · intro i
      exact (hd.2.2.2.2.1.coordinate_log_second_bound hg hK d.frame he hf hG hy hΓ i a).trans
        ((mul_le_mul_of_nonneg_right (show L2 ≤ Cl by dsimp only [Cl];linarith only [hK0,hL3])
          (sq_nonneg β)).trans_eq (by ring))
    · intro i j
      exact (hd.2.2.2.2.1.coordinate_log_third_bound hY hg hK d.frame he hf G DG hG hDG hy hΓ hDΓ j i a).trans
        ((mul_le_mul_of_nonneg_right (show L3 ≤ Cl by dsimp only [Cl];linarith only [hK0,hL2])
          (by positivity : 0 ≤ β^3)).trans_eq (by ring))
  · intro a b
    have hP (i j : I) := scalar_principal_sharp_two_jet_weights hY hg hg2 hK d.frame he
      hd.2.2.2.2.1 hf hε hε1 hd.2.2.2.2.2 hy M1 M2 (abs_nonneg _) (abs_nonneg _) hMetric1 hMetric2 a b i j
    have hP0Cp : P0 ≤ Cp := by dsimp only [Cp];linarith only [hP1,hP2]
    have hP1Cp : P1 ≤ Cp := by dsimp only [Cp];linarith only [hP0,hP2]
    have hP2Cp : P2 ≤ Cp := by dsimp only [Cp];linarith only [hP0,hP1]
    constructor
    · exact ((hP 0 0).1).trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hP0Cp hε) (sq_nonneg β))
    · intro i
      exact ((hP i 0).2.1).trans ((div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hP1Cp hε) hβ.le).trans_eq (by
          change Cp*ε/β=Cp*ε/β^2*β
          field_simp [hβ.ne'] <;> ring))
    · intro i j
      exact ((hP i j).2.2).trans ((mul_le_mul_of_nonneg_right hP2Cp hε).trans_eq (by
        change Cp*ε=Cp*ε/β^2*β^2
        field_simp [hβ.ne']))
  · intro a b
    constructor
    · exact (hPure floor hf ε hε d hd a b 0 0 y hy).1
    · intro i
      exact (hPure floor hf ε hε d hd a b i 0 y hy).2.1
    · intro i j
      exact (hPure floor hf ε hε d hd a b i j y hy).2.2

end ShrinkingSpheres.ParallelEnergy

import Proof.UniformBackgroundChristoffelJets
import Proof.ScalarPrincipalSharpTwoJets
import Proof.SmallScalarTwoJetProduct
import Proof.CoordinateFiniteSumCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- The SAME scalar base-connection drift is smooth and retains the
epsilon/beta squared, epsilon/beta, epsilon scalar two-jet weights.
Constants depend only on the original finite reference/profile budgets. -/
theorem uniform_scalar_principal_connection_two_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 3 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ k : I,
      ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d k) Y ∧ ∀ y ∈ Y,∀ i j : I,
        |scalarPrincipalConnectionWeight d k y| ≤ C*ε/(beta d.γ d.radius y)^2 ∧
        |coordDeriv i (scalarPrincipalConnectionWeight d k) y| ≤ C*ε/beta d.γ d.radius y ∧
        |coordDeriv j (coordDeriv i (scalarPrincipalConnectionWeight d k)) y| ≤ C*ε := by
  obtain ⟨CG,hCG,hConnection⟩ := uniform_background_christoffel_higher_jet_bounds hΩ 2 (by omega)
    K M (zero_lt_one.trans_le hK)
  let A0 := principalZeroBudget K
  let A1 := principalFirstBudget K |M ⟨1,by omega⟩|
  let A2 := principalSecondBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
  let B := A0+A1+A2
  let C := 36*B*CG
  have hA0 : 0 ≤ A0 := by dsimp only [A0,principalZeroBudget];linarith only [hK]
  have hA1 : 0 ≤ A1 := by dsimp only [A1,principalFirstBudget];positivity
  have hA2 : 0 ≤ A2 := by dsimp only [A2,principalSecondBudget];positivity
  have hB : 0 ≤ B := add_nonneg (add_nonneg hA0 hA1) hA2
  have hG : 0 ≤ CG := zero_le_one.trans hCG
  have h0B : A0 ≤ B := by dsimp only [B];linarith only [hA1,hA2]
  have h1B : A1 ≤ B := by dsimp only [B];linarith only [hA0,hA2]
  have h2B : A2 ≤ B := le_add_of_nonneg_left (add_nonneg hA0 hA1)
  have h9C : 9*B*CG ≤ C := by dsimp only [C];nlinarith only [mul_nonneg hB hG]
  have h18C : 18*B*CG ≤ C := by dsimp only [C];nlinarith only [mul_nonneg hB hG]
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  intro floor hf ε hε hε1 d hd k
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hKP := zero_lt_one.trans_le hK
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ :=
    ⟨fun a b => (hd.1.2.2.1.1 a b).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have hFrame : ∀ x ∈ Y,∀ a b,metricPair d.γ x (d.frame x a) (d.frame x b)=if a=b then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  let F := fun (p : I×I) (x : X) => scalarPrincipalMatrix d.γ d.g₂ d.radius x p.1 p.2*
    christoffel d.γ x k p.1 p.2
  have hFS (p : I×I) : ContDiffOn ℝ ∞ (F p) Y :=
    (hd.2.2.2.2.1.1.mul (contDiffOn_principal_entry hg hg2 hKP p.1 p.2)).mul
      (hg.contDiffOn_christoffel hY hKP k p.1 p.2)
  have hEq : scalarPrincipalConnectionWeight d k=(fun x => ∑ p : I×I,F p x) := by
    funext x
    simp only [scalarPrincipalConnectionWeight,F,Fintype.sum_prod_type]
  refine ⟨(ContDiffOn.sum (fun p _ => hFS p)).congr (fun x _ => congrFun hEq x),?_⟩
  intro y hy i j
  let β := beta d.γ d.radius y
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβ0 := zero_le_one.trans hβ
  have hSharp (p : I×I) (i j : I) := scalar_principal_sharp_two_jet_weights hY hg hg2 hK d.frame hFrame
    hd.2.2.2.2.1 hf hε hε1 hd.2.2.2.2.2 hy |M ⟨1,by omega⟩| |M ⟨2,by omega⟩|
    (abs_nonneg _) (abs_nonneg _)
    (fun a b => (hd.1.reference_fderiv_bound (by omega) (hSub hy) a b).trans (le_abs_self _))
    (fun a b => (hd.1.reference_second_fderiv_bound (by omega) (hSub hy) a b).trans (le_abs_self _))
    p.1 p.2 i j
  have hGamma (p : I×I) := hConnection d.γ d.g₁ d.g₂ d.frame hd.1 y (hSub hy) k p.1 p.2
  have hGJets (p : I×I) (i j : I) := (hGamma p).coordinate_two_jets le_rfl i j
  have hProduct (p : I×I) := small_scalar_two_jet_product_bounds hY
    (fun x => scalarPrincipalMatrix d.γ d.g₂ d.radius x p.1 p.2)
    (fun x => christoffel d.γ x k p.1 p.2)
    (hd.2.2.2.2.1.1.mul (contDiffOn_principal_entry hg hg2 hKP p.1 p.2))
    (hg.contDiffOn_christoffel hY hKP k p.1 p.2) hy i j B CG ε β hB hG hε hβ
    ((hSharp p i j).1.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h0B hε) (sq_nonneg β)))
    (fun a => (hSharp p a a).2.1.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1B hε) hβ0))
    ((hSharp p i j).2.2.trans (mul_le_mul_of_nonneg_right h2B hε))
    (hGJets p i j).1 (fun a => (hGJets p a a).2.1) (hGJets p i j).2.2
  have hSum (v : I×I → ℝ) (A : ℝ) (hv : ∀ p,|v p| ≤ A) : |∑ p,v p| ≤ 9*A := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun p _ => hv p)).trans_eq
      (by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul];ring))
  rw [hEq]
  refine ⟨?_,?_,?_⟩
  · exact (hSum _ _ (fun p => (hProduct p).1)).trans (by
      calc
        9*(B*CG*ε/β^2) = (9*B*CG)*ε/β^2 := by ring
        _ ≤ C*ε/β^2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h9C hε) (sq_nonneg β))
  · rw [coordinate_sum hY F hFS hy i]
    exact (hSum _ _ (fun p => (hProduct p).2.1)).trans (by
      calc
        9*(2*B*CG*ε/β) = (18*B*CG)*ε/β := by ring
        _ ≤ C*ε/β := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h18C hε) hβ0)
  · rw [coordinate_second_sum hY F hFS hy j i]
    exact (hSum _ _ (fun p => (hProduct p).2.2)).trans_eq (by dsimp only [C];ring)

end ShrinkingSpheres

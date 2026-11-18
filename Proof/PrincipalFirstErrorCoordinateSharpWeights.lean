import Proof.PrincipalFirstErrorCoordinateTwoJetWeights
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.PrincipalCommutator

/-- Small coordinate weights for bounded physical background operators.
The original profile smallness supplies the gain; no frame jet is bounded. -/
theorem Admissible.principalFirstErrorCoordinateWeight_sharp_zero_first_bounds {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} (hm : 1 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (a b i : I) :
    let B := principalFirstErrorCoordinateWeightBudget K |M ⟨1,by omega⟩|
    |principalFirstErrorCoordinateWeight d a b y| ≤ B*ε/(beta d.γ d.radius y)^2 ∧
      |directionalFDeriv (axis i) (principalFirstErrorCoordinateWeight d a b) y| ≤ B*ε/beta d.γ d.radius y := by
  let B := principalFirstErrorCoordinateWeightBudget K |M ⟨1,by omega⟩|
  let A0 := principalZeroBudget K
  let A1 := principalFirstBudget K |M ⟨1,by omega⟩|
  let β := beta d.γ d.radius y
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ := ⟨fun j k => (hd.1.1.1 j k).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ := ⟨fun j k => (hd.1.2.2.1.1 j k).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have hK0 := zero_le_one.trans hK
  have hKP := zero_lt_one.trans_le hK
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hA0 : 0 ≤ A0 := by dsimp only [A0,principalZeroBudget];positivity
  have hA1 : 0 ≤ A1 := by dsimp only [A1,principalFirstBudget];positivity
  have h0B : 2*A0 ≤ B := by change 2*A0 ≤ 2*(A0+A1);linarith only [hA1]
  have h1B : 2*A1 ≤ B := by change 2*A1 ≤ 2*(A0+A1);linarith only [hA0]
  have hWeights (j k : I) := principal_radius_zero_first_weights hY hg hg2 hK d.frame
    (fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)) hd.2.2.2.2.1 hf hε hε1 hd.2.2.2.2.2 hy
    |M ⟨1,by omega⟩| (abs_nonneg _)
    (fun j k => (hd.1.reference_fderiv_bound hm (hSub hy) j k).trans (le_abs_self _)) j k i
  have hβP : 0 < β := zero_lt_one.trans_le hβ
  have h0 (j k : I) : |d.radius y*principal d.γ d.g₂ y j k| ≤ A0*ε/β^2 :=
    (hWeights j k).1
  have h1 (j k : I) : |coordDeriv i (fun x => d.radius x*principal d.γ d.g₂ x j k) y| ≤ A1*ε/β :=
    (hWeights j k).2
  have hfun : principalFirstErrorCoordinateWeight d a b=
      (fun x => d.radius x*principal d.γ d.g₂ x a b+d.radius x*principal d.γ d.g₂ x b a) := by
    funext x
    exact mul_add _ _ _
  have hD (j k : I) : DifferentiableAt ℝ (fun x => d.radius x*principal d.γ d.g₂ x j k) y :=
    ((hd.2.2.2.2.1.1.mul (contDiffOn_principal_entry hg hg2 hKP j k)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hdFun : directionalFDeriv (axis i) (principalFirstErrorCoordinateWeight d a b) y=
      coordDeriv i (fun x => d.radius x*principal d.γ d.g₂ x a b) y+
        coordDeriv i (fun x => d.radius x*principal d.γ d.g₂ x b a) y := by
    rw [hfun]
    unfold directionalFDeriv coordDeriv
    rw [fderiv_fun_add (hD a b) (hD b a)]
    rfl
  refine ⟨?_,?_⟩
  · rw [hfun]
    calc
      _ ≤ A0*ε/β^2+A0*ε/β^2 := (abs_add_le _ _).trans (add_le_add (h0 a b) (h0 b a))
      _ = (2*A0)*ε/β^2 := by ring
      _ ≤ B*ε/β^2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h0B hε) (sq_nonneg _)
  · rw [hdFun]
    calc
      _ ≤ A1*ε/β+A1*ε/β := (abs_add_le _ _).trans (add_le_add (h1 a b) (h1 b a))
      _ = (2*A1)*ε/β := by ring
      _ ≤ B*ε/β := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1B hε) hβP.le

/-- Sharp zero/first/second scalar weights for bounded geometric
corrections, retaining the original epsilon and beta powers. -/
theorem Admissible.principalFirstErrorCoordinateWeight_small_two_jet_bounds {Y Ω : Set X}
    (hY : IsOpen Y) {m : ℕ} (hm : 2 ≤ m)
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (a b i j : I) :
    let B := principalFirstErrorCoordinateTwoJetBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
    |principalFirstErrorCoordinateWeight d a b y| ≤ B*ε/(beta d.γ d.radius y)^2 ∧
      |fderiv ℝ (principalFirstErrorCoordinateWeight d a b) y (axis i)| ≤ B*ε/beta d.γ d.radius y ∧
      |fderiv ℝ (fun x => fderiv ℝ (principalFirstErrorCoordinateWeight d a b) x (axis i))
        y (axis j)| ≤ B*ε := by
  let A2 := principalSecondBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
  let B1 := principalFirstErrorCoordinateWeightBudget K |M ⟨1,by omega⟩|
  let B := principalFirstErrorCoordinateTwoJetBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
  have hA2 : 0 ≤ A2 := by dsimp only [A2,principalSecondBudget];positivity
  have hB1 : 0 ≤ B1 := principalFirstErrorCoordinateWeightBudget_nonneg _ _
    (zero_le_one.trans hK) (abs_nonneg _)
  have hB1B : B1 ≤ B := by change B1 ≤ B1+2*A2;linarith only [hA2]
  have h2B : 2*A2 ≤ B := by change 2*A2 ≤ B1+2*A2;linarith only [hB1]
  have hβ : 0 ≤ beta d.γ d.radius y := zero_le_one.trans (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  have h01 := hd.principalFirstErrorCoordinateWeight_sharp_zero_first_bounds hY (by omega) hK hf hε hε1 hy a b i
  have h2 := hd.principalFirstErrorCoordinateWeight_second_small_bound hY hm hK hf hε hε1 hy a b i j
  refine ⟨h01.1.trans ?_,h01.2.trans ?_,h2.trans ?_⟩
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hB1B hε) (sq_nonneg _)
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hB1B hε) hβ
  · exact mul_le_mul_of_nonneg_right h2B hε

end ShrinkingSpheres

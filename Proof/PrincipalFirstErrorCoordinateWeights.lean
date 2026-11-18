import Proof.PrincipalAdjointBudgetDefinitions
import Proof.BackgroundBudgets
import Proof.NormalGeodesicBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.PrincipalCommutator

def principalFirstErrorCoordinateWeight (d : Data) (a b : I) (x : X) : ℝ :=
  d.radius x*(principal d.γ d.g₂ x a b+principal d.γ d.g₂ x b a)

def principalFirstErrorCoordinateWeightBudget (K M1 : ℝ) : ℝ :=
  2*(principalZeroBudget K+principalFirstBudget K M1)

lemma principalFirstErrorCoordinateWeightBudget_nonneg (K M1 : ℝ) (hK : 0 ≤ K) (hM1 : 0 ≤ M1) :
    0 ≤ principalFirstErrorCoordinateWeightBudget K M1 := by
  unfold principalFirstErrorCoordinateWeightBudget principalZeroBudget principalFirstBudget
  positivity

lemma Admissible.contDiffOn_principalFirstErrorCoordinateWeight {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (a b : I) :
    ContDiffOn ℝ ∞ (principalFirstErrorCoordinateWeight d a b) Y := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ := ⟨fun i j => (hd.1.2.2.1.1 i j).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  exact hd.2.2.2.2.1.1.mul ((contDiffOn_principal_entry hg hg2 hK a b).add
    (contDiffOn_principal_entry hg hg2 hK b a))

/-- Common relative scalar bounds for the actual coordinate weight. Only
    the reference metric's first background jet is needed. -/
theorem Admissible.principalFirstErrorCoordinateWeight_bounds {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} (hm : 1 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (a b i : I) :
    let B := principalFirstErrorCoordinateWeightBudget K |M ⟨1,by omega⟩|
    |principalFirstErrorCoordinateWeight d a b y| ≤ B ∧
      |directionalFDeriv (axis i) (principalFirstErrorCoordinateWeight d a b) y| ≤ B*beta d.γ d.radius y := by
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
  have hB : 0 ≤ B := (mul_nonneg (by norm_num) hA0).trans h0B
  have hWeights (j k : I) := principal_radius_zero_first_weights hY hg hg2 hK d.frame
    (fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)) hd.2.2.2.2.1 hf hε hε1 hd.2.2.2.2.2 hy
    |M ⟨1,by omega⟩| (abs_nonneg _)
    (fun j k => (hd.1.reference_fderiv_bound hm (hSub hy) j k).trans (le_abs_self _)) j k i
  have h0 (j k : I) : |d.radius y*principal d.γ d.g₂ y j k| ≤ A0 :=
    (hWeights j k).1.trans ((div_le_self (mul_nonneg hA0 hε) (one_le_pow₀ hβ)).trans
      ((mul_le_mul_of_nonneg_left hε1 hA0).trans_eq (mul_one _)))
  have h1 (j k : I) : |coordDeriv i (fun x => d.radius x*principal d.γ d.g₂ x j k) y| ≤ A1 :=
    (hWeights j k).2.trans ((div_le_self (mul_nonneg hA1 hε) hβ).trans
      ((mul_le_mul_of_nonneg_left hε1 hA1).trans_eq (mul_one _)))
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
    exact ((abs_add_le _ _).trans (add_le_add (h0 a b) (h0 b a))).trans (by linarith only [h0B])
  · rw [hdFun]
    have ht : |coordDeriv i (fun x => d.radius x*principal d.γ d.g₂ x a b) y+
        coordDeriv i (fun x => d.radius x*principal d.γ d.g₂ x b a) y| ≤ B :=
      ((abs_add_le _ _).trans (add_le_add (h1 a b) (h1 b a))).trans (by linarith only [h1B])
    exact ht.trans (by nlinarith only [mul_le_mul_of_nonneg_left hβ hB])
end ShrinkingSpheres

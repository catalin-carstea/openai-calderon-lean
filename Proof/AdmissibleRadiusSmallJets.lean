import Proof.ProfileRadiusThirdJet
import Proof.BackgroundBudgets
import Proof.PrincipalSecondCoefficientWeight
import Proof.NormalGeodesicBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- Shared sharp coordinate radius weights from the original profile and
r beta squared smallness. Only one background metric derivative is used. -/
theorem Admissible.coordinate_radius_two_small_jet_bounds {Y Ω : Set X}
    (hY : IsOpen Y) {m : ℕ} (hm : 1 ≤ m)
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    {y : X} (hy : y ∈ Y) (i j : I) :
    |coordDeriv i d.radius y| ≤ K*ε/beta d.γ d.radius y ∧
      |coordDeriv j (coordDeriv i d.radius) y| ≤
        (K^2+9*K^2*|Cj 2|+27*K^2*|M ⟨1,by omega⟩|)*ε := by
  let M1 := |M ⟨1,by omega⟩|
  let G := 9*K*M1
  let R2 := K^2+9*K^2*|Cj 2|+3*G*K
  let β := beta d.γ d.radius y
  have hKP := zero_lt_one.trans_le hK
  have hK0 := zero_le_one.trans hK
  have hM1 : 0 ≤ M1 := abs_nonneg _
  have hG : 0 ≤ G := by dsimp only [G];positivity
  have hR2 : 0 ≤ R2 := by dsimp only [R2];positivity
  have hβ : 0 < β := zero_lt_one.trans_le (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ := ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hFrame := fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hDg (a b : I) : ‖fderiv ℝ (fun x => d.γ x a b) y‖ ≤ M1 :=
    (hd.1.reference_fderiv_bound hm (hSub hy) a b).trans (le_abs_self _)
  have hGamma (a b c : I) : |christoffel d.γ y a b c| ≤ G :=
    hg.christoffel_entry_bound hKP hy M1 hM1 hDg a b c
  have hSmall := (hd.2.2.2.2.2 y hy).2
  constructor
  · have hh := hd.2.2.2.2.1.coordinate_radius_first_bound hY hg hK d.frame hFrame hy i
    exact hh.trans ((le_div_iff₀ hβ).mpr (by
      calc
        (K*d.radius y*β)*β = K*(d.radius y*β^2) := by ring
        _ ≤ K*ε := mul_le_mul_of_nonneg_left hSmall hK0))
  · have hh := hd.2.2.2.2.1.coordinate_radius_second_bound hY hg hK d.frame hFrame hf hG hy hGamma j i
    have hBound : |coordDeriv j (coordDeriv i d.radius) y| ≤ R2*ε :=
      hh.trans (by
        calc
          R2*d.radius y*β^2 = R2*(d.radius y*β^2) := by ring
          _ ≤ R2*ε := mul_le_mul_of_nonneg_left hSmall hR2)
    convert hBound using 1 <;> dsimp only [R2,G,M1] <;> ring

/-- The actual third radius derivative has the original epsilon beta
weight, requiring only the second reference-metric derivative. -/
theorem Admissible.coordinate_radius_third_small_jet_bound {Y Ω : Set X}
    (hY : IsOpen Y) {m : ℕ} (hm : 2 ≤ m)
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    {y : X} (hy : y ∈ Y) (i j k : I) :
    |coordDeriv k (coordDeriv j (coordDeriv i d.radius)) y| ≤
      profileRadiusThirdBudget K (9*K*|M ⟨1,by omega⟩|)
        (81*K^2*|M ⟨1,by omega⟩|^2+9*K*|M ⟨2,by omega⟩|) (Cj 2) (Cj 3)*
          ε*beta d.γ d.radius y := by
  let M1 := |M ⟨1,by omega⟩|
  let M2 := |M ⟨2,by omega⟩|
  let G := 9*K*M1
  let DG := 81*K^2*M1^2+9*K*M2
  let R3 := profileRadiusThirdBudget K G DG (Cj 2) (Cj 3)
  let β := beta d.γ d.radius y
  have hKP := zero_lt_one.trans_le hK
  have hK0 := zero_le_one.trans hK
  have hG : 0 ≤ G := by dsimp only [G];positivity
  have hDG : 0 ≤ DG := by dsimp only [DG];positivity
  have hR3 : 0 ≤ R3 := profileRadiusThirdBudget_nonneg _ _ _ _ _ hK0 hG hDG
  have hβ : 0 ≤ β := zero_le_one.trans (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ := ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hFrame := fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hDg (a b : I) : ‖fderiv ℝ (fun x => d.γ x a b) y‖ ≤ M1 :=
    (hd.1.reference_fderiv_bound (by omega) (hSub hy) a b).trans (le_abs_self _)
  have hD2g (a b : I) : ‖fderiv ℝ (fderiv ℝ (fun x => d.γ x a b)) y‖ ≤ M2 :=
    (hd.1.reference_second_fderiv_bound hm (hSub hy) a b).trans (le_abs_self _)
  have hGamma (a b c : I) : |christoffel d.γ y a b c| ≤ G :=
    hg.christoffel_entry_bound hKP hy M1 (abs_nonneg _) hDg a b c
  have hDGamma (a b c t : I) : |coordDeriv a (fun x => christoffel d.γ x b c t) y| ≤ DG := by
    simpa only [coordDeriv,norm_axis,mul_one] using
      hg.christoffel_derivative_entry_bound hY hKP hy M1 M2 (abs_nonneg _) (abs_nonneg _) hDg hD2g (axis a) b c t
  have hh := hd.2.2.2.2.1.coordinate_radius_third_bound hY hg hK d.frame hFrame hf G DG hG hDG hy hGamma hDGamma k j i
  calc
    _ ≤ R3*d.radius y*β^3 := hh
    _ = R3*(d.radius y*β^2)*β := by ring
    _ ≤ R3*ε*β := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hd.2.2.2.2.2 y hy).2 hR3) hβ

end ShrinkingSpheres

import Proof.ProfileLogFourthJet
import Proof.CoordinateThirdNormBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def profileLogCovectorThreeJetBudget (K G DG DDG C2 C3 C4 : ℝ) : ℝ :=
  profileLogCovectorJetBudget K G DG C2 C3+81*profileLogFourthBudget K G DG DDG C2 C3 C4

lemma profileLogCovectorThreeJetBudget_nonneg (K G DG DDG C2 C3 C4 : ℝ)
    (hK : 0 ≤ K) (hG : 0 ≤ G) (hDG : 0 ≤ DG) (hDDG : 0 ≤ DDG) :
    0 ≤ profileLogCovectorThreeJetBudget K G DG DDG C2 C3 C4 := by
  have hThird := profileLogThirdBudget_nonneg K G DG C2 C3 hK hG hDG
  have hFourth := profileLogFourthBudget_nonneg K G DG DDG C2 C3 C4 hK hG hDG hDDG
  unfold profileLogCovectorThreeJetBudget profileLogCovectorJetBudget
  positivity

/-- Three actual log-radius covector jets use only the frozen four profile
    derivatives and actual connection jets; arbitrary frame derivatives cancel. -/
theorem Profile.log_covector_three_jets {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 1 ≤ K) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hf : 1 ≤ floor)
    (G DG DDG : ℝ) (hG : 0 ≤ G) (hDG : 0 ≤ DG) (hDDG : 0 ≤ DDG) {y : X} (hy : y ∈ Y)
    (hΓ : ∀ a b c : I,|christoffel g y a b c| ≤ G)
    (hDΓ : ∀ a b c d : I,|coordDeriv a (fun x => christoffel g x b c d) y| ≤ DG)
    (hDDΓ : ∀ a b c d e : I,|coordDeriv a (coordDeriv b (fun x => christoffel g x c d e)) y| ≤ DDG) :
    ∀ n : ℕ,n ≤ 3 → ‖iteratedFDeriv ℝ n (fderiv ℝ (fun x => Real.log (r x))) y‖ ≤
      profileLogCovectorThreeJetBudget K G DG DDG (Cj 2) (Cj 3) (Cj 4)*(beta g r y)^(n+1) := by
  let f := fun x => Real.log (r x)
  let β := beta g r y
  let B := profileLogCovectorJetBudget K G DG (Cj 2) (Cj 3)
  let L4 := profileLogFourthBudget K G DG DDG (Cj 2) (Cj 3) (Cj 4)
  have hK0 := zero_le_one.trans hK
  have hThird := profileLogThirdBudget_nonneg K G DG (Cj 2) (Cj 3) hK0 hG hDG
  have hB : 0 ≤ B := by unfold B profileLogCovectorJetBudget;positivity
  have hL4 : 0 ≤ L4 := profileLogFourthBudget_nonneg _ _ _ _ _ _ _ hK0 hG hDG hDDG
  have hβ0 : 0 ≤ β := Real.sqrt_nonneg _
  have hSf : ContDiffOn ℝ ∞ f Y := hp.1.log (fun x hx => (hp.2 x hx).1.ne')
  have hOld := hp.log_covector_higher_jets hY h hK e hframe hf G DG hG hDG hy hΓ hDΓ
  have hFour : ‖iteratedFDeriv ℝ 3 (fderiv ℝ f) y‖ ≤ 81*L4*β^4 := by
    have hh := norm_iteratedFDeriv_fderiv_le_coordinate_jets f y (hSf.contDiffAt (hY.mem_nhds hy)) 3
      (27*L4*β^4) (by positivity) (fun l => by
        rw [norm_iteratedFDeriv_three_eq_nested]
        have hSl := contDiffOn_coordDeriv hY hSf l
        rw [mul_assoc]
        apply norm_trilinear_le_of_axis_bound _ (L4*β^4) (by positivity)
        intro a b c
        rw [← coordinate_third_derivative hY (coordDeriv l f) hSl hy a b c,Real.norm_eq_abs]
        exact hp.coordinate_log_fourth_bound hY h hK e hframe hf G DG DDG hG hDG hDDG hy hΓ hDΓ hDDΓ a b c l)
    exact hh.trans_eq (by ring)
  intro n hn
  by_cases hn2 : n ≤ 2
  · exact (hOld n hn2).trans (mul_le_mul_of_nonneg_right
      (show B ≤ profileLogCovectorThreeJetBudget K G DG DDG (Cj 2) (Cj 3) (Cj 4) by
        change B ≤ B+81*L4
        linarith only [hL4]) (by positivity))
  · have : n=3 := by omega
    subst n
    exact hFour.trans (mul_le_mul_of_nonneg_right
      (show 81*L4 ≤ profileLogCovectorThreeJetBudget K G DG DDG (Cj 2) (Cj 3) (Cj 4) by
        change 81*L4 ≤ B+81*L4
        linarith only [hB]) (by positivity))
end ShrinkingSpheres

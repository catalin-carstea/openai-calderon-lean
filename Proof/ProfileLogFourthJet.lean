import Proof.FourTensorFrameBounds
import Proof.CovariantFourthCoordinateBound
import Proof.ProfileLogThirdJet
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

def profileLogFourthBudget (K G DG DDG C2 C3 C4 : ℝ) : ℝ :=
  fourthCoordinateJetBudget K (9*K^2*|C2|+3*G*K) (profileLogThirdBudget K G DG C2 C3)
    (9*K^2*|C2|) (27*K^3*|C3|) (81*K^4*|C4|) G DG DDG

lemma profileLogFourthBudget_nonneg (K G DG DDG C2 C3 C4 : ℝ)
    (hK : 0 ≤ K) (hG : 0 ≤ G) (hDG : 0 ≤ DG) (hDDG : 0 ≤ DDG) :
    0 ≤ profileLogFourthBudget K G DG DDG C2 C3 C4 := by
  have hThird := profileLogThirdBudget_nonneg K G DG C2 C3 hK hG hDG
  exact fourthCoordinateJetBudget_nonneg _ _ _ _ _ _ _ _ _ hK (by positivity) hThird
    (by positivity) (by positivity) (by positivity) hG hDG hDDG

/-- The frozen fourth covariant profile budget supplies the actual fourth
    coordinate log-radius jet. Only actual metric connection derivatives enter. -/
theorem Profile.coordinate_log_fourth_bound {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 1 ≤ K) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hf : 1 ≤ floor)
    (G DG DDG : ℝ) (hG : 0 ≤ G) (hDG : 0 ≤ DG) (hDDG : 0 ≤ DDG) {y : X} (hy : y ∈ Y)
    (hΓ : ∀ a b c : I,|christoffel g y a b c| ≤ G)
    (hDΓ : ∀ a b c d : I,|coordDeriv a (fun x => christoffel g x b c d) y| ≤ DG)
    (hDDΓ : ∀ a b c d e : I,|coordDeriv a (coordDeriv b (fun x => christoffel g x c d e)) y| ≤ DDG)
    (i j k l : I) :
    |coordDeriv i (coordDeriv j (coordDeriv k (coordDeriv l (fun x => Real.log (r x))))) y| ≤
      profileLogFourthBudget K G DG DDG (Cj 2) (Cj 3) (Cj 4)*(beta g r y)^4 := by
  let f := fun x => Real.log (r x)
  let β := beta g r y
  let H2 := 9*K^2*|Cj 2|
  let H3 := 27*K^3*|Cj 3|
  let H4 := 81*K^4*|Cj 4|
  let B2 := H2+3*G*K
  let B3 := profileLogThirdBudget K G DG (Cj 2) (Cj 3)
  have hK0 := zero_le_one.trans hK
  have hH2 : 0 ≤ H2 := by dsimp only [H2];positivity
  have hH3 : 0 ≤ H3 := by dsimp only [H3];positivity
  have hH4 : 0 ≤ H4 := by dsimp only [H4];positivity
  have hB2 : 0 ≤ B2 := by dsimp only [B2];positivity
  have hB3 : 0 ≤ B3 := profileLogThirdBudget_nonneg _ _ _ _ _ hK0 hG hDG
  have hβ : 1 ≤ β := hf.trans (hp.2 y hy).2.1
  have hfSm : ContDiffOn ℝ ∞ f Y := hp.1.log (fun x hx => (hp.2 x hx).1.ne')
  have hCov2 (idx : Fin 2 → I) : |covJet g f 2 y idx| ≤ H2*β^2 := by
    have hIdx : idx = ![idx 0,idx 1] := by ext t;fin_cases t <;> rfl
    rw [hIdx]
    exact hp.coordinate_hessian_bound h hK e hframe hy (idx 0) (idx 1)
  have hCov3 (idx : Fin 3 → I) : |covJet g f 3 y idx| ≤ H3*β^3 := by
    have hIdx : idx = ![idx 0,idx 1,idx 2] := by ext t;fin_cases t <;> rfl
    rw [hIdx]
    exact hp.coordinate_third_covariant_bound h hK e hframe hy (idx 0) (idx 1) (idx 2)
  have hCov4 (idx : Fin 4 → I) : |covJet g f 4 y idx| ≤ H4*β^4 := by
    have hIdx : idx = ![idx 0,idx 1,idx 2,idx 3] := by ext t;fin_cases t <;> rfl
    rw [hIdx]
    exact hp.coordinate_fourth_covariant_bound h hK e hframe hy (idx 0) (idx 1) (idx 2) (idx 3)
  exact coordinate_fourth_bound_of_covJets hY g f hfSm
    (fun a b c => h.contDiffOn_christoffel hY (zero_lt_one.trans_le hK) a b c) hy
    β K B2 B3 H2 H3 H4 G DG DDG hβ hK0 hB2 hB3 hH2 hH3 hH4 hG hDG hDDG
    hΓ hDΓ hDDΓ
    (fun a => h.coord_logRadius_bound hK e r hy (hframe y hy) a)
    (fun a b => hp.coordinate_log_second_bound h hK e hframe hf hG hy hΓ a b)
    (fun a b c => hp.coordinate_log_third_bound hY h hK e hframe hf G DG hG hDG hy hΓ hDΓ a b c)
    hCov2 hCov3 hCov4 i j k l
end ShrinkingSpheres

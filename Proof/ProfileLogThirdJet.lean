import Proof.ThirdTensorFrameBounds
import Proof.CovariantThirdCoordinateExpansion
import Proof.ProfileRadiusSecondJet

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def profileLogThirdBudget (K G DG C2 C3 : ℝ) : ℝ :=
  27*K^3*|C3|+3*DG*K+3*G*(9*K^2*|C2|+3*G*K)+6*G*(9*K^2*|C2|)

lemma profileLogThirdBudget_nonneg (K G DG C2 C3 : ℝ) (hK : 0 ≤ K) (hG : 0 ≤ G) (hDG : 0 ≤ DG) :
    0 ≤ profileLogThirdBudget K G DG C2 C3 := by
  unfold profileLogThirdBudget
  positivity

/-- The third coordinate log-radius bound follows from the frozen profile's
third covariant jet and actual background connection jets. No radius or frame
is replaced by a special family. -/
theorem Profile.coordinate_log_third_bound {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 1 ≤ K) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hf : 1 ≤ floor)
    (G DG : ℝ) (hG : 0 ≤ G) (hDG : 0 ≤ DG) {y : X} (hy : y ∈ Y)
    (hΓ : ∀ a b c : I,|christoffel g y a b c| ≤ G)
    (hDΓ : ∀ a b c d : I,|coordDeriv a (fun x => christoffel g x b c d) y| ≤ DG)
    (i j k : I) :
    |coordDeriv i (coordDeriv j (coordDeriv k (fun x => Real.log (r x)))) y| ≤
      profileLogThirdBudget K G DG (Cj 2) (Cj 3)*(beta g r y)^3 := by
  let f := fun x => Real.log (r x)
  let β := beta g r y
  let H2 := 9*K^2*|Cj 2|
  let L2 := H2+3*G*K
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hβ : 1 ≤ β := hf.trans (hp.2 y hy).2.1
  have hβ0 : 0 ≤ β := zero_le_one.trans hβ
  have hH2 : 0 ≤ H2 := by dsimp [H2];positivity
  have hL2 : 0 ≤ L2 := by dsimp [L2];positivity
  have hfSmooth : ContDiffOn ℝ ∞ f Y := hp.1.log (fun x hx => (hp.2 x hx).1.ne')
  have hEq := coordinate_third_of_covJet hY g f hfSmooth
    (fun a b c => h.contDiffOn_christoffel hY (zero_lt_one.trans_le hK) a b c) hy i j k
  have hD1 (a : I) : |coordDeriv a f y| ≤ K*β := h.coord_logRadius_bound hK e r hy (hframe y hy) a
  have hD2 (a b : I) : |coordDeriv a (coordDeriv b f) y| ≤ L2*β^2 :=
    hp.coordinate_log_second_bound h hK e hframe hf hG hy hΓ a b
  have hCov2 (a b : I) : |covJet g f 2 y ![a,b]| ≤ H2*β^2 :=
    hp.coordinate_hessian_bound h hK e hframe hy a b
  have hCov3 : |covJet g f 3 y ![i,j,k]| ≤ (27*K^3*|Cj 3|)*β^3 :=
    hp.coordinate_third_covariant_bound h hK e hframe hy i j k
  have hTermD (l : I) : |(coordDeriv i (fun x => christoffel g x l j k) y)*coordDeriv l f y+
        christoffel g y l j k*coordDeriv i (coordDeriv l f) y| ≤ DG*K*β+G*L2*β^2 := by
    have h1 := mul_le_mul (hDΓ i l j k) (hD1 l) (abs_nonneg _) hDG
    have h2 := mul_le_mul (hΓ l j k) (hD2 i l) (abs_nonneg _) hG
    exact (abs_add_le _ _).trans ((add_le_add (by simpa only [abs_mul] using h1)
      (by simpa only [abs_mul] using h2)).trans_eq (by ring))
  have hSumD : |∑ l,((coordDeriv i (fun x => christoffel g x l j k) y)*coordDeriv l f y+
        christoffel g y l j k*coordDeriv i (coordDeriv l f) y)| ≤ 3*DG*K*β+3*G*L2*β^2 :=
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun l _ => hTermD l)).trans_eq
      (by simp only [Fin.sum_univ_three];ring))
  have hTermC (l a b c d : I) : |christoffel g y l a b*covJet g f 2 y ![c,d]| ≤ G*H2*β^2 := by
    rw [abs_mul]
    exact (mul_le_mul (hΓ l a b) (hCov2 c d) (abs_nonneg _) hG).trans_eq (by ring)
  have hSumC1 : |∑ l,christoffel g y l i j*covJet g f 2 y ![l,k]| ≤ 3*G*H2*β^2 :=
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun l _ => hTermC l i j l k)).trans_eq
      (by simp only [Fin.sum_univ_three];ring))
  have hSumC2 : |∑ l,christoffel g y l i k*covJet g f 2 y ![j,l]| ≤ 3*G*H2*β^2 :=
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun l _ => hTermC l i k j l)).trans_eq
      (by simp only [Fin.sum_univ_three];ring))
  have hβ23 : β^2 ≤ β^3 := by
    have hMul := mul_le_mul_of_nonneg_left hβ (sq_nonneg β)
    nlinarith only [hMul]
  have hβ13 : β ≤ β^3 := (show β ≤ β^2 by nlinarith).trans hβ23
  have hAbs : |coordDeriv i (coordDeriv j (coordDeriv k f)) y| ≤
      |covJet g f 3 y ![i,j,k]|+
      |∑ l,((coordDeriv i (fun x => christoffel g x l j k) y)*coordDeriv l f y+
        christoffel g y l j k*coordDeriv i (coordDeriv l f) y)|+
      |∑ l,christoffel g y l i j*covJet g f 2 y ![l,k]|+
      |∑ l,christoffel g y l i k*covJet g f 2 y ![j,l]| := by
    rw [hEq]
    exact (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  calc
    _ ≤ (27*K^3*|Cj 3|)*β^3+(3*DG*K*β+3*G*L2*β^2)+3*G*H2*β^2+3*G*H2*β^2 :=
      hAbs.trans (add_le_add (add_le_add (add_le_add hCov3 hSumD) hSumC1) hSumC2)
    _ ≤ (27*K^3*|Cj 3|)*β^3+(3*DG*K*β^3+3*G*L2*β^3)+3*G*H2*β^3+3*G*H2*β^3 := by
      gcongr <;> first | exact hβ13 | exact hβ23
    _ = profileLogThirdBudget K G DG (Cj 2) (Cj 3)*β^3 := by
      dsimp only [profileLogThirdBudget,L2,H2]
      ring

end ShrinkingSpheres

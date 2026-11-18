import Proof.ProfileRadiusThirdJet
import Proof.PrincipalThirdCoefficientBound
import Proof.CoordinateThirdProductBound
import Proof.PrincipalSecondCoefficientWeight

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def principalRadiusAllThreeJetBudget (K M1 M2 C2 C3 : ℝ) : ℝ :=
  1+K+(K^2+9*K^2*|C2|+3*(9*K*M1)*K)+
    profileRadiusThirdBudget K (9*K*M1) (81*K^2*M1^2+9*K*M2) C2 C3

def principalAllThreeJetBudget (K M1 M2 M3 : ℝ) : ℝ :=
  (K+1)+(9*K^2*M1+1)+(162*K^3*M1^2+9*K^2*M2+1)+(principalThirdEntryBudget K M1 M2 M3+1)

def principalRadiusThirdWeightBudget (K M1 M2 M3 C2 C3 : ℝ) : ℝ :=
  8*principalRadiusAllThreeJetBudget K M1 M2 C2 C3*principalAllThreeJetBudget K M1 M2 M3

/-- The genuine third coordinate coefficient of rQ has its epsilon*beta
weight for every admitted radius and smooth orthonormal frame. The supplied
third product estimate is fed by the actual arbitrary-profile producers. -/
theorem principal_radius_third_weight {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₂ : MetricField}
    (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂) (hK : 1 ≤ K) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hf : 1 ≤ floor)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hs : Small Y g g₂ r ε)
    {y : X} (hy : y ∈ Y) (M1 M2 M3 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3)
    (hD : ∀ a b,‖fderiv ℝ (fun x => g x a b) y‖ ≤ M1)
    (hD2 : ∀ a b,‖fderiv ℝ (fderiv ℝ (fun x => g x a b)) y‖ ≤ M2)
    (hD3 : ∀ a b,‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun x => g x a b))) y‖ ≤ M3)
    (a b i j k : I) :
    |coordDeriv i (coordDeriv j (coordDeriv k (fun x => r x*principal g g₂ x a b))) y| ≤
      principalRadiusThirdWeightBudget K M1 M2 M3 (Cj 2) (Cj 3)*ε*beta g r y := by
  let β := beta g r y
  let G := 9*K*M1
  let DG := 81*K^2*M1^2+9*K*M2
  let R2 := K^2+9*K^2*|Cj 2|+3*G*K
  let R3 := profileRadiusThirdBudget K G DG (Cj 2) (Cj 3)
  let CR := principalRadiusAllThreeJetBudget K M1 M2 (Cj 2) (Cj 3)
  let CQ := principalAllThreeJetBudget K M1 M2 M3
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hK0 : 0 ≤ K := hKpos.le
  have hG : 0 ≤ G := by dsimp [G];positivity
  have hDG : 0 ≤ DG := by dsimp [DG];positivity
  have hR2 : 0 ≤ R2 := by dsimp [R2];positivity
  have hR3 : 0 ≤ R3 := profileRadiusThirdBudget_nonneg K G DG (Cj 2) (Cj 3) hK0 hG hDG
  have hCR1 : 1 ≤ CR := by change 1 ≤ 1+K+R2+R3;linarith
  have hCRK : K ≤ CR := by change K ≤ 1+K+R2+R3;linarith
  have hCR2 : R2 ≤ CR := by change R2 ≤ 1+K+R2+R3;linarith
  have hCR3 : R3 ≤ CR := by change R3 ≤ 1+K+R2+R3;linarith
  have hCR0 : 0 ≤ CR := zero_le_one.trans hCR1
  have hQ3Nonneg := principalThirdEntryBudget_nonneg K M1 M2 M3 hK0 hM1 hM2 hM3
  have hN0 : 0 ≤ K+1 := by positivity
  have hN1 : 0 ≤ 9*K^2*M1+1 := by positivity
  have hN2 : 0 ≤ 162*K^3*M1^2+9*K^2*M2+1 := by positivity
  have hN3 : 0 ≤ principalThirdEntryBudget K M1 M2 M3+1 := by positivity
  have hCQ0 : 0 ≤ CQ := by dsimp only [CQ,principalAllThreeJetBudget];linarith only [hN0,hN1,hN2,hN3]
  have hβ : 1 ≤ β := hf.trans (hp.2 y hy).2.1
  have hβ0 : 0 ≤ β := zero_le_one.trans hβ
  have hβ23 : β^2 ≤ β^3 := by
    have hMul := mul_le_mul_of_nonneg_left hβ (sq_nonneg β)
    nlinarith only [hMul]
  have hβ13 : β ≤ β^3 := (show β ≤ β^2 by nlinarith).trans hβ23
  have hβ03 : 1 ≤ β^3 := hβ.trans hβ13
  have hr := (hp.2 y hy).1
  have hrε : r y ≤ ε := (radius_bounds (r y) β floor ε hr.le hf (hp.2 y hy).2.1 (hs y hy).2).2.2
  have hr1 : r y ≤ 1 := hrε.trans hε1
  have hεr : ε*r y ≤ 1 := (mul_le_mul_of_nonneg_right hε1 hr.le).trans (by simpa using hr1)
  have hΓ (u v w : I) : |christoffel g y u v w| ≤ G := h.christoffel_entry_bound hKpos hy M1 hM1 hD u v w
  have hDΓ (t u v w : I) : |coordDeriv t (fun x => christoffel g x u v w) y| ≤ DG := by
    simpa only [coordDeriv,norm_axis,mul_one] using
      h.christoffel_derivative_entry_bound hY hKpos hy M1 M2 hM1 hM2 hD hD2 (axis t) u v w
  have hRadius : CoordinateScalarThreeJetBound r y (CR*r y*β^3) := by
    constructor
    · rw [abs_of_pos hr]
      calc
        r y ≤ r y*β^3 := by nlinarith only [mul_le_mul_of_nonneg_left hβ03 hr.le]
        _ ≤ CR*r y*β^3 := by nlinarith only [mul_le_mul_of_nonneg_right hCR1 (mul_nonneg hr.le (pow_nonneg hβ0 3))]
    · intro t
      have hFirst := hp.coordinate_radius_first_bound hY h hK e hframe hy t
      exact hFirst.trans (by gcongr)
    · intro t u
      have hSecond := hp.coordinate_radius_second_bound hY h hK e hframe hf hG hy hΓ t u
      exact hSecond.trans (by change R2*r y*β^2 ≤ CR*r y*β^3;gcongr)
    · intro t u v
      have hThird := hp.coordinate_radius_third_bound hY h hK e hframe hf G DG hG hDG hy hΓ hDΓ t u v
      exact hThird.trans (by change R3*r y*β^3 ≤ CR*r y*β^3;gcongr)
  have hPrincipal : CoordinateScalarThreeJetBound (fun x => principal g g₂ x a b) y CQ := by
    constructor
    · have hQ0 := (principal_entry_le_inverse_add h hKpos hs hy a b).trans (show K+ε*r y ≤ K+1 by linarith)
      exact hQ0.trans (by dsimp only [CQ,principalAllThreeJetBudget];linarith only [hN0,hN1,hN2,hN3])
    · intro t
      have hQ1 := (principal_derivative_le_inverse_add hY h h₂ hKpos hs hy M1 hM1 hD a b t).trans
        (show 9*K^2*M1+ε*r y ≤ 9*K^2*M1+1 by linarith)
      exact hQ1.trans (by dsimp only [CQ,principalAllThreeJetBudget];linarith only [hN0,hN1,hN2,hN3])
    · intro t u
      have hQ2 := (principal_second_le_inverse_add hY h h₂ hKpos hs hy M1 M2 hM1 hM2 hD hD2 a b u t).trans
        (show 162*K^3*M1^2+9*K^2*M2+ε*r y ≤ 162*K^3*M1^2+9*K^2*M2+1 by linarith)
      exact hQ2.trans (by dsimp only [CQ,principalAllThreeJetBudget];linarith only [hN0,hN1,hN2,hN3])
    · intro t u v
      have hQ3 := (principal_third_le_inverse_add hY h h₂ hKpos hs hy M1 M2 M3 hM1 hM2 hM3 hD hD2 hD3 a b t u v).trans
        (show principalThirdEntryBudget K M1 M2 M3+ε*r y ≤ principalThirdEntryBudget K M1 M2 M3+1 by linarith)
      exact hQ3.trans (by dsimp only [CQ,principalAllThreeJetBudget];linarith only [hN0,hN1,hN2,hN3])
  have hProduct := hRadius.mul_third_bound hY hp.1 (contDiffOn_principal_entry h h₂ hKpos a b) hy
    (by positivity) hCQ0 hPrincipal i j k
  have hSmall : r y*β^3 ≤ ε*β := by
    have ht := mul_le_mul_of_nonneg_right (hs y hy).2 hβ0
    convert ht using 1 <;> dsimp only [β] <;> ring
  calc
    _ ≤ 8*(CR*r y*β^3)*CQ := hProduct
    _ = (8*CR*CQ)*(r y*β^3) := by ring
    _ ≤ (8*CR*CQ)*(ε*β) := mul_le_mul_of_nonneg_left hSmall (by positivity)
    _ = principalRadiusThirdWeightBudget K M1 M2 M3 (Cj 2) (Cj 3)*ε*β := by
      dsimp only [principalRadiusThirdWeightBudget,CR,CQ]
      ring

end ShrinkingSpheres

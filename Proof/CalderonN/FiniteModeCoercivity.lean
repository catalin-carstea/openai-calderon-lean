module

public import Proof.CalderonN.ProfileModeEnergy
import Mathlib.Tactic

@[expose] public section

/- Port of FiniteModeCoercivity.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

variable [NeZero n]

open OAI.AnisotropicCalderon.AngularPolynomial

def profileCoercivityConstant (a c₀ : ℝ) : ℝ := min (1/8 : ℝ) (min (a/16) (c₀/12))

lemma profileCoercivityConstant_pos (a c₀ : ℝ) (ha : 0 < a) (hc₀ : 0 < c₀) :
    0 < profileCoercivityConstant a c₀ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))

lemma profileCoercivityConstant_le (a c₀ : ℝ) :
    profileCoercivityConstant a c₀ ≤ 1/8 ∧ profileCoercivityConstant a c₀ ≤ a/16 ∧
      profileCoercivityConstant a c₀ ≤ c₀/12 :=
  ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩

variable {ι : Type*} [Fintype ι]

/-- The four weighted mode energies are controlled by the genuine finite raising-minus-
    lowering Fischer energies. No prescribed construction of the radius is used. -/
theorem Profile.modeFischerEnergy_coercive (hnDimension : 3 ≤ n) {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : (X n) → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hc₀ : 0 < c₀) (hfloor : 1 ≤ floor) (m : ℕ) (b : ι → MvPolynomial (I n) ℝ)
    (hb : ∀ j, (b j).IsHomogeneous (m+1)) (hΔ : ∀ j, laplacian (b j) = 0)
    (c : (X n) → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y)
    (a Ccurv : ℝ) (ha : 0 < a) (hC : 0 ≤ Ccurv) (hasmall : a ≤ c₀/8) (haf : a ≤ floor)
    (habsorb : 10*((n:ℝ)+2)*Ccurv ≤ c₀*floor)
    (hcurv : |integratedFullCovectorCurvature g e b c| ≤ Ccurv*((m : ℝ)+1)^2*fischerMass g b c) :
    profileCoercivityConstant a c₀ * (profileModeFischerEnergy g e r (m+1) b c / sphereNormalization n (m+1)) ≤
      fischerRaisingEnergy g e b c (fun x => Real.log (r x)) m -
        fischerLoweringEnergy g e b c (fun x => Real.log (r x)) m := by
  let degree : ℝ := (m : ℝ)+1
  let Eplus := ∫ y, metricDensity g y * weightedFrameEnergy g e b c (fun x => Real.log (r x)) (m+1) 1 y
  let W := profileWeightedFrameEnergy g e b c r (m+1) 1
  let M := profileFischerMass g b c r
  let Raw := profileModeFischerEnergy g e r (m+1) b c
  let E := Raw / sphereNormalization n (m+1)
  let N := sphereNormalization n (m+1)
  let Δ := fischerRaisingEnergy g e b c (fun x => Real.log (r x)) m - fischerLoweringEnergy g e b c (fun x => Real.log (r x)) m
  let C := profileCoercivityConstant a c₀
  have hCpos : 0 < C := profileCoercivityConstant_pos a c₀ ha hc₀
  have hN : 0 < N := sphereNormalization_pos (n:=n) (by omega) (m+1)
  have heq : E = Raw/N := rfl
  have hn : 0 ≤ degree := by positivity
  have hX : 0 ≤ Eplus := weightedFrameEnergy_integral_nonneg g e b c _ (m+1) 1
  have hW : 0 ≤ W := profileWeightedFrameEnergy_nonneg g e b c r (m+1) 1
  have hM : 0 ≤ M := profileFischerMass_nonneg g b c r
  have hnorm : Raw ≤ 4*Eplus+4*degree*W+12*degree^3*M := by
    simpa only [Raw, Eplus, W, M, degree, Nat.cast_add, Nat.cast_one] using
      (hp.modeFischerEnergy_le hY h hK e he hframe hc₀ hfloor (k:=m+1) (by omega) b c hc hcompact hsupp)
  have hgain : Eplus/2+(a/4)*(degree+(n:ℝ)-1)*W+c₀*degree^3*M ≤ N*Δ := by
    simpa only [Eplus, W, M, degree, N, Δ, Nat.cast_add, Nat.cast_one,
      show (m : ℝ)+1+(n:ℝ)-1 = (m : ℝ)+(n:ℝ) by ring] using
      (hp.fischerRaisingEnergy_gain hnDimension hY h hK e he hframe hc₀ hfloor m b hb hΔ c hc hcompact hsupp
        a Ccurv ha hC hasmall haf habsorb hcurv)
  obtain ⟨hC1,hC2,hC3⟩ := profileCoercivityConstant_le a c₀
  have hcx : 4*C ≤ 1/2 := by dsimp only [C]; linarith only [hC1]
  have hcw : 4*C ≤ a/4 := by dsimp only [C]; linarith only [hC2]
  have hcm : 12*C ≤ c₀ := by dsimp only [C]; linarith only [hC3]
  have hreserve : C*(4*Eplus+4*degree*W+12*degree^3*M) ≤ Eplus/2+(a/4)*(degree+(n:ℝ)-1)*W+c₀*degree^3*M := by
    have hx := mul_le_mul_of_nonneg_right hcx hX
    have hw := mul_le_mul_of_nonneg_right hcw (show 0 ≤ degree*W by positivity)
    have hm := mul_le_mul_of_nonneg_right hcm (show 0 ≤ degree^3*M by positivity)
    have haW := mul_nonneg ha.le hW
    have hDim : 0 ≤ (n:ℝ)-1 := by
      have hh : (3:ℝ) ≤ n := by exact_mod_cast hnDimension
      linarith
    have hdimW := mul_nonneg haW hDim
    nlinarith only [hx, hw, hm, hdimW]
  have hfinal : N*(C*E) ≤ N*Δ := by
    calc
      N*(C*E) = C*Raw := by rw [heq]; field_simp [hN.ne'] <;> ring
      _ ≤ C*(4*Eplus+4*degree*W+12*degree^3*M) := mul_le_mul_of_nonneg_left hnorm hCpos.le
      _ ≤ Eplus/2+(a/4)*(degree+(n:ℝ)-1)*W+c₀*degree^3*M := hreserve
      _ ≤ N*Δ := hgain
  change C*E ≤ Δ
  by_contra hnot
  have hpos : 0 < N*(C*E-Δ) := mul_pos hN (sub_pos.mpr (lt_of_not_ge hnot))
  nlinarith only [hfinal, hpos]

theorem Profile.modeFischerEnergy_coercive_of_curvature_bound (hnDimension : 3 ≤ n) {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : (X n) → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hc₀ : 0 < c₀) (hfloor : 1 ≤ floor) (B : ℝ) (hB : 0 ≤ B)
    (hR : ∀ y ∈ Y, ∀ i j a b, |frameCurvatureCoefficient g e y (e y i) (e y j) a b| ≤ B)
    (hthreshold : 10*((n:ℝ)+2)*(n:ℝ)^2*B ≤ c₀*floor) (m : ℕ) (b : ι → MvPolynomial (I n) ℝ)
    (hb : ∀ j, (b j).IsHomogeneous (m+1)) (hΔ : ∀ j, laplacian (b j) = 0)
    (c : (X n) → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y)
    (a : ℝ) (ha : 0 < a) (hasmall : a ≤ c₀/8) (haf : a ≤ floor) :
    profileCoercivityConstant a c₀ * (profileModeFischerEnergy g e r (m+1) b c / sphereNormalization n (m+1)) ≤
      fischerRaisingEnergy g e b c (fun x => Real.log (r x)) m -
        fischerLoweringEnergy g e b c (fun x => Real.log (r x)) m := by
  have hcurv := integratedFullCovectorCurvature_bound hY h hK e he hframe B hB hR (by omega) b hb c hc.contDiffOn hcompact hsupp
  have hcurv' : |integratedFullCovectorCurvature g e b c| ≤ ((n:ℝ)^2*B)*((m : ℝ)+1)^2*fischerMass g b c := by
    simpa only [Nat.cast_add, Nat.cast_one, fischerMass] using hcurv
  exact hp.modeFischerEnergy_coercive hnDimension hY h hK e he hframe hc₀ hfloor m b hb hΔ c hc hcompact hsupp
    a ((n:ℝ)^2*B) ha (by positivity) hasmall haf (by nlinarith only [hthreshold]) hcurv'

end CalderonN

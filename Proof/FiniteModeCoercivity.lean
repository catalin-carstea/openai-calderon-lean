import Proof.ProfileModeEnergy

noncomputable section
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
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
theorem Profile.modeFischerEnergy_coercive {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hc₀ : 0 < c₀) (hfloor : 1 ≤ floor) (m : ℕ) (b : ι → MvPolynomial I ℝ)
    (hb : ∀ j, (b j).IsHomogeneous (m+1)) (hΔ : ∀ j, laplacian (b j) = 0)
    (c : X → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y)
    (a Ccurv : ℝ) (ha : 0 < a) (hC : 0 ≤ Ccurv) (hasmall : a ≤ c₀/8) (haf : a ≤ floor)
    (habsorb : 50*Ccurv ≤ c₀*floor)
    (hcurv : |integratedFullCovectorCurvature g e b c| ≤ Ccurv*((m : ℝ)+1)^2*fischerMass g b c) :
    profileCoercivityConstant a c₀ * (profileModeFischerEnergy g e r (m+1) b c / sphereNormalization 3 (m+1)) ≤
      fischerRaisingEnergy g e b c (fun x => Real.log (r x)) m -
        fischerLoweringEnergy g e b c (fun x => Real.log (r x)) m := by
  let n : ℝ := (m : ℝ)+1
  let X := ∫ y, metricDensity g y * weightedFrameEnergy g e b c (fun x => Real.log (r x)) (m+1) 1 y
  let W := profileWeightedFrameEnergy g e b c r (m+1) 1
  let M := profileFischerMass g b c r
  let Raw := profileModeFischerEnergy g e r (m+1) b c
  let E := Raw / sphereNormalization 3 (m+1)
  let N := sphereNormalization 3 (m+1)
  let Δ := fischerRaisingEnergy g e b c (fun x => Real.log (r x)) m - fischerLoweringEnergy g e b c (fun x => Real.log (r x)) m
  let C := profileCoercivityConstant a c₀
  have hCpos : 0 < C := profileCoercivityConstant_pos a c₀ ha hc₀
  have hN : 0 < N := sphereNormalization_pos (n:=3) (by norm_num) (m+1)
  have heq : E = Raw/N := rfl
  have hn : 0 ≤ n := by positivity
  have hX : 0 ≤ X := weightedFrameEnergy_integral_nonneg g e b c _ (m+1) 1
  have hW : 0 ≤ W := profileWeightedFrameEnergy_nonneg g e b c r (m+1) 1
  have hM : 0 ≤ M := profileFischerMass_nonneg g b c r
  have hnorm : Raw ≤ 4*X+4*n*W+12*n^3*M := by
    simpa only [Raw, X, W, M, n, Nat.cast_add, Nat.cast_one] using
      (hp.modeFischerEnergy_le hY h hK e he hframe hc₀ hfloor (k:=m+1) (by omega) b c hc hcompact hsupp)
  have hgain : X/2+(a/4)*(n+2)*W+c₀*n^3*M ≤ N*Δ := by
    simpa only [X, W, M, n, N, Δ, Nat.cast_add, Nat.cast_one,
      show (m : ℝ)+1+2 = (m : ℝ)+3 by ring] using
      (hp.fischerRaisingEnergy_gain hY h hK e he hframe hc₀ hfloor m b hb hΔ c hc hcompact hsupp
        a Ccurv ha hC hasmall haf habsorb hcurv)
  obtain ⟨hC1,hC2,hC3⟩ := profileCoercivityConstant_le a c₀
  have hcx : 4*C ≤ 1/2 := by dsimp only [C]; linarith only [hC1]
  have hcw : 4*C ≤ a/4 := by dsimp only [C]; linarith only [hC2]
  have hcm : 12*C ≤ c₀ := by dsimp only [C]; linarith only [hC3]
  have hreserve : C*(4*X+4*n*W+12*n^3*M) ≤ X/2+(a/4)*(n+2)*W+c₀*n^3*M := by
    have hx := mul_le_mul_of_nonneg_right hcx hX
    have hw := mul_le_mul_of_nonneg_right hcw (show 0 ≤ n*W by positivity)
    have hm := mul_le_mul_of_nonneg_right hcm (show 0 ≤ n^3*M by positivity)
    have haW := mul_nonneg ha.le hW
    nlinarith only [hx, hw, hm, haW]
  have hfinal : N*(C*E) ≤ N*Δ := by
    calc
      N*(C*E) = C*Raw := by rw [heq]; field_simp [hN.ne'] <;> ring
      _ ≤ C*(4*X+4*n*W+12*n^3*M) := mul_le_mul_of_nonneg_left hnorm hCpos.le
      _ ≤ X/2+(a/4)*(n+2)*W+c₀*n^3*M := hreserve
      _ ≤ N*Δ := hgain
  change C*E ≤ Δ
  by_contra hnot
  have hpos : 0 < N*(C*E-Δ) := mul_pos hN (sub_pos.mpr (lt_of_not_ge hnot))
  nlinarith only [hfinal, hpos]

theorem Profile.modeFischerEnergy_coercive_of_curvature_bound {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hc₀ : 0 < c₀) (hfloor : 1 ≤ floor) (B : ℝ) (hB : 0 ≤ B)
    (hR : ∀ y ∈ Y, ∀ i j a b, |frameCurvatureCoefficient g e y (e y i) (e y j) a b| ≤ B)
    (hthreshold : 450*B ≤ c₀*floor) (m : ℕ) (b : ι → MvPolynomial I ℝ)
    (hb : ∀ j, (b j).IsHomogeneous (m+1)) (hΔ : ∀ j, laplacian (b j) = 0)
    (c : X → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y)
    (a : ℝ) (ha : 0 < a) (hasmall : a ≤ c₀/8) (haf : a ≤ floor) :
    profileCoercivityConstant a c₀ * (profileModeFischerEnergy g e r (m+1) b c / sphereNormalization 3 (m+1)) ≤
      fischerRaisingEnergy g e b c (fun x => Real.log (r x)) m -
        fischerLoweringEnergy g e b c (fun x => Real.log (r x)) m := by
  have hcurv := integratedFullCovectorCurvature_bound hY h hK e he hframe B hB hR (by omega) b hb c hc.contDiffOn hcompact hsupp
  have hcurv' : |integratedFullCovectorCurvature g e b c| ≤ (9*B)*((m : ℝ)+1)^2*fischerMass g b c := by
    simpa only [Nat.cast_add, Nat.cast_one, fischerMass] using hcurv
  exact hp.modeFischerEnergy_coercive hY h hK e he hframe hc₀ hfloor m b hb hΔ c hc hcompact hsupp
    a (9*B) ha (by positivity) hasmall haf (by linarith) hcurv'

end ShrinkingSpheres

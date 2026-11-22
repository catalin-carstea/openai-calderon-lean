module

public import Proof.CalderonN.FockIntegration
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

@[expose] public section

/- Port of FiniteProfileGain.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

variable [NeZero n]
open Set MeasureTheory MvPolynomial

open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι : Type*} [Fintype ι]

def fischerMass (g : (MetricField n)) (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) : ℝ :=
  ∫ y, metricDensity g y * fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)

lemma fischerMass_nonneg (g : (MetricField n)) (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) : 0 ≤ fischerMass g b c :=
  integral_nonneg (fun y => mul_nonneg (Real.sqrt_nonneg _) (fischerInner_self_nonneg _))

lemma profileFischerMass_nonneg (g : (MetricField n)) (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (r : (X n) → ℝ) :
    0 ≤ profileFischerMass g b c r :=
  integral_nonneg (fun y => mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (fischerInner_self_nonneg _))

lemma weightedFrameEnergy_integral_nonneg (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k s : ℝ) : 0 ≤ ∫ y, metricDensity g y * weightedFrameEnergy g e b c f k s y :=
  integral_nonneg (fun y => mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg (fun i _ => fischerInner_self_nonneg _)))

lemma loweredWeightedTraceSquare_nonneg (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (f : (X n) → ℝ) (k s : ℝ) : 0 ≤ loweredWeightedTraceSquare g e b c f k s :=
  integral_nonneg (fun y => mul_nonneg (Real.sqrt_nonneg _) (fischerInner_self_nonneg _))

lemma Profile.minus_frameEnergy_le_plus {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : (X n) → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hc₀ : 0 < c₀) (hfloor : 1 ≤ floor) (b : ι → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y)
    {k : ℝ} (hk : 0 ≤ k) :
    (∫ y, metricDensity g y * weightedFrameEnergy g e b c (fun x => Real.log (r x)) k (-1) y) ≤
      (∫ y, metricDensity g y * weightedFrameEnergy g e b c (fun x => Real.log (r x)) k 1 y) := by
  have hf : ContDiffOn ℝ ∞ (fun x => Real.log (r x)) Y := hp.1.log (fun x hx => (hp.2 x hx).1.ne')
  have hp' := compact_weighted_energy_expansion hY h hK e he (metricDensity g) (h.contDiffOn_density hK)
    _ hf b c hc hcompact hsupp k 1
  have hm' := compact_weighted_energy_expansion hY h hK e he (metricDensity g) (h.contDiffOn_density hK)
    _ hf b c hc hcompact hsupp k (-1)
  have hcross := profile_weighted_gradient_cross_nonneg hY h hK e he hframe hp hc₀ hfloor b c hc hcompact hsupp
  have hcross' : 0 ≤ ∫ y, metricDensity g y * polynomialGradientCross g e b c (fun x => Real.log (r x)) y := by
    simpa only [polynomialGradientCross, ← mul_assoc] using hcross
  rw [hp', hm']
  simp only [one_pow, one_mul, neg_one_sq, neg_one_mul]
  nlinarith only [mul_nonneg hk hcross']

/-- The degreewise raising gain for an arbitrary admissible profile. The curvature premise
    has a checked producer in integratedFullCovectorCurvature_bound. -/
theorem Profile.fischerRaisingEnergy_gain (hn : 3 ≤ n) {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
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
    (∫ y, metricDensity g y * weightedFrameEnergy g e b c (fun x => Real.log (r x)) (m+1) 1 y)/2 +
      (a/4)*((m : ℝ)+(n:ℝ))*profileWeightedFrameEnergy g e b c r (m+1) 1 +
      c₀*((m : ℝ)+1)^3*profileFischerMass g b c r ≤
      sphereNormalization n (m+1)*(fischerRaisingEnergy g e b c (fun x => Real.log (r x)) m -
        fischerLoweringEnergy g e b c (fun x => Real.log (r x)) m) := by
  let k : ℝ := (m : ℝ)+1
  let d : ℝ := k+(n:ℝ)/2-1
  let f := fun x => Real.log (r x)
  let Eplus := ∫ y, metricDensity g y * weightedFrameEnergy g e b c f k 1 y
  let W := (k+(n:ℝ)-1)*profileWeightedFrameEnergy g e b c r k 1
  let G := loweredWeightedTraceSquare g e b c f k (-1)
  let M := profileFischerMass g b c r
  let V := fischerMass g b c
  let S := loweredWeightedTraceSquare g e b c f k 1
  let H := loweredHessianEnergy g e b c f k
  let E := integratedFullCovectorCurvature g e b c
  let C := ((n:ℝ)+2)*Ccurv
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hk : 1 ≤ k := by dsimp [k]; exact le_add_of_nonneg_left (Nat.cast_nonneg m)
  have hk0 : 0 ≤ k := zero_le_one.trans hk
  have hd : 0 < d := by dsimp [d]; linarith
  have hV : 0 ≤ V := fischerMass_nonneg g b c
  have hM : 0 ≤ M := profileFischerMass_nonneg g b c r
  have hX : 0 ≤ Eplus := weightedFrameEnergy_integral_nonneg g e b c f k 1
  have hW : 0 ≤ W := mul_nonneg (by linarith) (profileWeightedFrameEnergy_nonneg g e b c r k 1)
  have hG : 0 ≤ G := loweredWeightedTraceSquare_nonneg g e b c f k (-1)
  have hMV : floor*V ≤ M := hp.floor_fischer_mass_le hY h hK hfloor b c hc.contDiffOn hcompact hsupp
  have hf : ContDiffOn ℝ ∞ f Y := hp.1.log (fun x hx => (hp.2 x hx).1.ne')
  have hminus := hp.minus_frameEnergy_le_plus hY h hK e he hframe hc₀ hfloor b c hc hcompact hsupp hk0
  have hfirst := loweredWeighted_second_integrated_inequality hY h hK e he hframe
    (by omega) b hb c f hc hf hcompact hsupp
  have hfirst' : S ≤ k*(Eplus+0)-H+(-E) := by
    have hh : S ≤ k*(∫ y, metricDensity g y * weightedFrameEnergy g e b c f k (-1) y)-H-E := by
      simpa only [S, k, H, E, Nat.cast_add, Nat.cast_one] using hfirst
    have hm := mul_le_mul_of_nonneg_left hminus hk0
    change k*(∫ y, metricDensity g y * weightedFrameEnergy g e b c f k (-1) y) ≤ k*Eplus at hm
    linarith only [hh, hm]
  have hsecond := hp.trace_convex_uniform_integrated_bound hY h hK e he hframe hfloor
    (by omega) b hb c hc hcompact hsupp a ha.le haf
  have hsecond' : S ≤ (k+(n:ℝ)-1)*Eplus-a*W+(2*a/floor)*G+8*a*k^3*M := by
    convert hsecond using 1 <;> dsimp only [S, k, Eplus, W, G, M, f] <;> push_cast <;> ring
  have hhH := hp.loweredHessianEnergy_le hY h hK e he hframe hfloor b hb c hc.contDiffOn hcompact hsupp
  have hH : H ≤ -2*c₀*k^2*M := by
    simpa only [H, k, M, profileFischerMass, f, Nat.cast_add, Nat.cast_one, mul_assoc] using hhH
  have hR2 : -E ≤ C*k^2*V := by
    refine (neg_le_abs E).trans (hcurv.trans ?_)
    dsimp only [C, k]
    have hC' : Ccurv ≤ ((n:ℝ)+2)*Ccurv := by nlinarith [mul_nonneg hC (show 0 ≤ (n:ℝ)+1 by linarith)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC' (sq_nonneg _)) hV
  have hR3 : -C*k^3*V ≤ ((n:ℝ)+2*k)*E := by
    have hE : -(Ccurv*k^2*V) ≤ E := by
      have hh : -E ≤ Ccurv*k^2*V := (neg_le_abs E).trans hcurv
      linarith
    have hcoef : (n:ℝ)+2*k ≤ ((n:ℝ)+2)*k := by
      nlinarith [mul_nonneg (show 0 ≤ (n:ℝ) by linarith) (show 0 ≤ k-1 by linarith)]
    calc
      _ = -((((n:ℝ)+2)*k)*(Ccurv*k^2*V)) := by dsimp only [C]; ring
      _ ≤ -(((n:ℝ)+2*k)*(Ccurv*k^2*V)) :=
        neg_le_neg (mul_le_mul_of_nonneg_right hcoef (by positivity))
      _ ≤ _ := by
        rw [← mul_neg]
        exact mul_le_mul_of_nonneg_left hE (by positivity)
  have hbound := OAI.AnisotropicCalderon.raising_form_lower_bound
    (n:=(n:ℝ)) (k:=k) (c₀:=c₀) (c₁:=a) (C:=C) (β:=floor)
    (X:=Eplus) (Y:=W) (G:=G) (W:=M) (V:=V) (F:=S) (H:=H) (T:=0)
    (R₂:=-E) (R₃:=((n:ℝ)+2*k)*E) hnR hk hc₀ ha (by dsimp [C]; positivity) hfloor hasmall haf
    (by dsimp only [C]; linarith only [habsorb]) hMV hX hW hG hM hV hfirst' hsecond'
    le_rfl hH hR2 hR3
  have henergy := fischerRaisingEnergy_sub_loweringEnergy_reduced
    hY h hK e he hframe m b hb hΔ c f hc hf hcompact hsupp
  have hN := sphereNormalization_pos (n:=n) (show 0 < n by omega) (m+1)
  have hExact : sphereNormalization n (m+1)*(fischerRaisingEnergy g e b c f m-fischerLoweringEnergy g e b c f m) =
      (2+2/d)*(d*Eplus-S-d*H)+2*G+((n:ℝ)+2*k)*E := by
    have henergy' : fischerRaisingEnergy g e b c f m-fischerLoweringEnergy g e b c f m =
        (((n:ℝ)+2*k)*(Eplus-(1/d)*S-H)+2*G+((n:ℝ)+2*k)*E)/
          sphereNormalization n (m+1) := by
      have hden : 4 * ((m : ℝ) + (n : ℝ)/2) = 4*d := by dsimp [d,k]; ring
      have hfrac : 4/(4*d) = 1/d := by field_simp [hd.ne']
      rw [hden, hfrac] at henergy
      exact henergy
    rw [henergy', mul_div_cancel₀ _ hN.ne']
    have hco : (n:ℝ)+2*k = (2+2/d)*d := by
      field_simp [hd.ne']
      dsimp only [d]
      ring
    rw [hco]
    field_simp [hd.ne'] <;> ring
  change _ ≤ (2+2/d)*(d*Eplus-S-d*H)+2*G+((n:ℝ)+2*k)*E at hbound
  rw [← hExact] at hbound
  simpa only [Eplus, W, k, M, f, Nat.cast_add, Nat.cast_one, mul_assoc,
    show (m : ℝ)+1+(n:ℝ)-1 = (m : ℝ)+(n:ℝ) by ring] using hbound

end CalderonN

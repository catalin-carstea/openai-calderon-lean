import Proof.FockIntegration

noncomputable section
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι : Type*} [Fintype ι]

def fischerMass (g : MetricField) (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) : ℝ :=
  ∫ y, metricDensity g y * fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)

lemma fischerMass_nonneg (g : MetricField) (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) : 0 ≤ fischerMass g b c :=
  integral_nonneg (fun y => mul_nonneg (Real.sqrt_nonneg _) (fischerInner_self_nonneg _))

lemma profileFischerMass_nonneg (g : MetricField) (b : ι → MvPolynomial I ℝ) (c : X → ι → ℝ) (r : X → ℝ) :
    0 ≤ profileFischerMass g b c r :=
  integral_nonneg (fun y => mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (fischerInner_self_nonneg _))

lemma weightedFrameEnergy_integral_nonneg (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (k s : ℝ) : 0 ≤ ∫ y, metricDensity g y * weightedFrameEnergy g e b c f k s y :=
  integral_nonneg (fun y => mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg (fun i _ => fischerInner_self_nonneg _)))

lemma loweredWeightedTraceSquare_nonneg (g : MetricField) (e : Frame) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (f : X → ℝ) (k s : ℝ) : 0 ≤ loweredWeightedTraceSquare g e b c f k s :=
  integral_nonneg (fun y => mul_nonneg (Real.sqrt_nonneg _) (fischerInner_self_nonneg _))

lemma Profile.minus_frameEnergy_le_plus {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hc₀ : 0 < c₀) (hfloor : 1 ≤ floor) (b : ι → MvPolynomial I ℝ)
    (c : X → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y)
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
theorem Profile.fischerRaisingEnergy_gain {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
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
    (∫ y, metricDensity g y * weightedFrameEnergy g e b c (fun x => Real.log (r x)) (m+1) 1 y)/2 +
      (a/4)*((m : ℝ)+3)*profileWeightedFrameEnergy g e b c r (m+1) 1 +
      c₀*((m : ℝ)+1)^3*profileFischerMass g b c r ≤
      sphereNormalization 3 (m+1)*(fischerRaisingEnergy g e b c (fun x => Real.log (r x)) m -
        fischerLoweringEnergy g e b c (fun x => Real.log (r x)) m) := by
  let n : ℝ := (m : ℝ)+1
  let f := fun x => Real.log (r x)
  let X := ∫ y, metricDensity g y * weightedFrameEnergy g e b c f n 1 y
  let W := (n+2)*profileWeightedFrameEnergy g e b c r n 1
  let G := loweredWeightedTraceSquare g e b c f n (-1)
  let M := profileFischerMass g b c r
  let V := fischerMass g b c
  let S := loweredWeightedTraceSquare g e b c f n 1
  let H := loweredHessianEnergy g e b c f n
  let E := integratedFullCovectorCurvature g e b c
  have hn : 1 ≤ n := by dsimp only [n]; linarith [show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m]
  have hn0 : 0 ≤ n := by linarith
  have hV : 0 ≤ V := fischerMass_nonneg g b c
  have hM : 0 ≤ M := profileFischerMass_nonneg g b c r
  have hX : 0 ≤ X := weightedFrameEnergy_integral_nonneg g e b c f n 1
  have hW : 0 ≤ W := mul_nonneg (by linarith) (profileWeightedFrameEnergy_nonneg g e b c r n 1)
  have hG : 0 ≤ G := loweredWeightedTraceSquare_nonneg g e b c f n (-1)
  have hMV : floor*V ≤ M := hp.floor_fischer_mass_le hY h hK hfloor b c hc.contDiffOn hcompact hsupp
  have hf : ContDiffOn ℝ ∞ f Y := hp.1.log (fun x hx => (hp.2 x hx).1.ne')
  have hminus := hp.minus_frameEnergy_le_plus hY h hK e he hframe hc₀ hfloor b c hc hcompact hsupp hn0
  have hfirst := loweredWeighted_second_integrated_inequality hY h hK e he hframe (by omega) b hb c f hc hf hcompact hsupp
  have hfirst' : S ≤ n*(X+0)-H+(-E) := by
    have hh : S ≤ n*(∫ y, metricDensity g y * weightedFrameEnergy g e b c f n (-1) y)-H-E := by
      simpa only [S, n, H, E, Nat.cast_add, Nat.cast_one] using hfirst
    have hm := mul_le_mul_of_nonneg_left hminus hn0
    change n*(∫ y, metricDensity g y * weightedFrameEnergy g e b c f n (-1) y) ≤ n*X at hm
    linarith only [hh, hm]
  have hsecond := hp.trace_convex_uniform_integrated_bound hY h hK e he hframe hfloor (by omega) b hb c hc hcompact hsupp a ha.le haf
  have hsecond' : S ≤ (n+3-1)*X-a*W+(2*a/floor)*G+8*a*n^3*M := by
    convert hsecond using 1 <;> dsimp only [S, n, X, W, G, M, f] <;> push_cast <;> ring
  have hhH := hp.loweredHessianEnergy_le hY h hK e he hframe hfloor b hb c hc.contDiffOn hcompact hsupp
  have hH : H ≤ -2*c₀*n^2*M := by
    simpa only [H, n, M, profileFischerMass, f, Nat.cast_add, Nat.cast_one, mul_assoc] using hhH
  have hR2 : -E ≤ (5*Ccurv)*n^2*V := by
    have hh : -E ≤ Ccurv*n^2*V := (neg_le_abs E).trans hcurv
    have hpC : 0 ≤ Ccurv*n^2*V := by positivity
    linarith
  have hR3 : -(5*Ccurv)*n^3*V ≤ (3+2*n)*E := by
    have hE : -(Ccurv*n^2*V) ≤ E := by linarith [(neg_le_abs E).trans hcurv]
    have hcE := mul_le_mul_of_nonneg_left hE (show 0 ≤ 3+2*n by positivity)
    have hcost : (3+2*n)*(Ccurv*n^2*V) ≤ (5*Ccurv)*n^3*V := by
      nlinarith only [mul_nonneg (show 0 ≤ n-1 by linarith) (show 0 ≤ 3*Ccurv*n^2*V by positivity)]
    linarith
  have hbound := OAI.AnisotropicCalderon.raising_form_lower_bound (n:=3) (k:=n) (c₀:=c₀) (c₁:=a)
    (C:=5*Ccurv) (β:=floor) (X:=X) (Y:=W) (G:=G) (W:=M) (V:=V) (F:=S) (H:=H) (T:=0)
    (R₂:=-E) (R₃:=(3+2*n)*E) (by norm_num) hn hc₀ ha (by positivity) hfloor hasmall haf
    (by linarith) hMV hX hW hG hM hV hfirst' hsecond' (by norm_num) hH hR2 hR3
  have henergy := fischerRaisingEnergy_sub_loweringEnergy_reduced hY h hK e he hframe m b hb hΔ c f hc hf hcompact hsupp
  have hN := sphereNormalization_pos (n:=3) (by norm_num : 0 < 3) (m+1)
  have hExact : sphereNormalization 3 (m+1)*(fischerRaisingEnergy g e b c f m-fischerLoweringEnergy g e b c f m) =
      (2+2/(n+3/2-1))*((n+3/2-1)*X-S-(n+3/2-1)*H)+2*G+(3+2*n)*E := by
    have henergy' : fischerRaisingEnergy g e b c f m-fischerLoweringEnergy g e b c f m =
        ((3+2*n)*(X-(4/(4*(m : ℝ)+6))*S-H)+2*G+(3+2*n)*E)/sphereNormalization 3 (m+1) := by
      convert henergy using 1 <;> dsimp only [X, S, H, G, E, n] <;> ring
    have hden : 4*(m : ℝ)+6 = 4*(n+3/2-1) := by dsimp only [n]; ring
    rw [henergy', hden]
    have hd : n+3/2-1 ≠ 0 := by linarith
    field_simp [hN.ne', hd]
    <;> ring_nf
    <;> field_simp [show 1+n*2 ≠ 0 by linarith]
    <;> ring
  rw [← hExact] at hbound
  simpa only [X, W, n, M, f, Nat.cast_add, Nat.cast_one, mul_assoc,
    show (m : ℝ)+1+2 = (m : ℝ)+3 by ring] using hbound

end ShrinkingSpheres

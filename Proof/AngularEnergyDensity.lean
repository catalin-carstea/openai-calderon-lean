import Proof.FiniteAngularNorms

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

/-- The integrand of the frozen energySq, factored out for finite angular sums. -/
def physicalEnergyDensity (g : MetricField) (e : Frame) (r : X → ℝ) (φ : Field) (y : X) : ℝ :=
  metricDensity g y * ((∑ j,fiberSq e y (fun w => horizontal g φ y w (e y j))) +
    (beta g r y)^2*sobolevSq g e 1 y (fun w => φ (y,w)) +
    (beta g r y)⁻¹*(∑ j,sobolevSq g e (1/2) y (fun w => horizontal g φ y w (e y j))) +
    beta g r y*sobolevSq g e (3/2) y (fun w => φ (y,w)))

lemma energySq_eq_integral_density (Y : Set X) (g : MetricField) (e : Frame) (r : X → ℝ) (φ : Field) :
    energySq Y g e r φ = ∫ y in Y,physicalEnergyDensity g e r φ y := rfl

variable {α ι : Type*} [Fintype ι]

def pairedModeDensity (g : MetricField) (e : Frame) (r : X → ℝ) (k : ℕ)
    (b : ι → MvPolynomial I ℝ) (c d : X → ι → ℝ) (y : X) : ℝ :=
  let V := normalizedFischerSquare k (finitePolynomialField b c y)+normalizedFischerSquare k (finitePolynomialField b d y)
  let H := ∑ j,(normalizedFischerSquare k (covariantPolynomialDerivative g e b c y (e y j))+
    normalizedFischerSquare k (covariantPolynomialDerivative g e b d y (e y j)))
  metricDensity g y*(H+(1+(k : ℝ))^2*(beta g r y)^2*V+
    (1+(k : ℝ))*(beta g r y)⁻¹*H+(1+(k : ℝ))^3*beta g r y*V)

lemma pairedModeDensity_eq_fischer (g : MetricField) (e : Frame) (r : X → ℝ) (k : ℕ)
    (b : ι → MvPolynomial I ℝ) (c d : X → ι → ℝ) (y : X) :
    pairedModeDensity g e r k b c d y =
      (modeFischerDensity g e r k b c y+modeFischerDensity g e r k b d y)/sphereNormalization 3 k := by
  simp only [pairedModeDensity,normalizedFischerSquare,normalizedFischerInner,Fintype.card_fin,
    modeFischerDensity,covariantFrameEnergy,Finset.sum_add_distrib,← Finset.sum_div]
  ring

lemma finite_weighted_energy_sum (s : Finset α) (ρ β : ℝ) (weight V : α → ℝ) (H : α → I → ℝ) :
    ρ*((∑ j,∑ i ∈ s,H i j)+β^2*(∑ i ∈ s,(weight i)^2*V i)+
      β⁻¹*(∑ j,∑ i ∈ s,weight i*H i j)+β*(∑ i ∈ s,(weight i)^3*V i)) =
      ∑ i ∈ s,ρ*((∑ j,H i j)+(weight i)^2*β^2*V i+weight i*β⁻¹*(∑ j,H i j)+(weight i)^3*β*V i) := by
  have h1 : (∑ j,∑ i ∈ s,H i j) = ∑ i ∈ s,∑ j,H i j := Finset.sum_comm
  have h2 : (∑ j,∑ i ∈ s,weight i*H i j) = ∑ i ∈ s,weight i*(∑ j,H i j) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
  rw [h1,h2]
  calc
    _ = ∑ i ∈ s,ρ*((∑ j,H i j)+β^2*((weight i)^2*V i)+β⁻¹*(weight i*(∑ j,H i j))+β*((weight i)^3*V i)) := by
      simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib,mul_assoc]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      ring

lemma physicalEnergyDensity_pairedPolynomialField {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (r : X → ℝ) {k : ℕ} (hk : 1 ≤ k) (b : ι → MvPolynomial I ℝ) (hb : ∀ t,(b t).IsHomogeneous k)
    (hΔ : ∀ t,laplacian (b t) = 0) (c d : X → ι → ℝ)
    (hc : ContDiffOn ℝ ∞ c Y) (hd : ContDiffOn ℝ ∞ d Y) {y : X} (hy : y ∈ Y) :
    physicalEnergyDensity g e r (pairedPolynomialField g e b c d) y = pairedModeDensity g e r k b c d y := by
  unfold physicalEnergyDensity
  simp_rw [sobolevSq_pairedPolynomialField_weight g e y (hframe y hy) _ k b hb hΔ c d,
    sobolevSq_pairedPolynomialField_horizontal_weight hY h hK e he hframe _ hk b hb hΔ c d hc hd hy]
  norm_num only [mul_one,show (2 : ℝ)*(1/2) = 1 by norm_num,show (2 : ℝ)*(3/2) = 3 by norm_num,
    Real.rpow_one,Real.rpow_two,show (1+(k : ℝ))^(3 : ℝ) = (1+(k : ℝ))^3 from Real.rpow_natCast _ 3]
  simp_rw [fiberSq_pairedPolynomialField g e y (hframe y hy) b hb hΔ c d,
    fiberSq_pairedPolynomialField_horizontal hY h hK e he hframe hk b hb hΔ c d hc hd hy]
  simp only [pairedModeDensity,Finset.mul_sum]
  ring

/-- The full physical energy density diagonalizes finite distinct harmonic degrees. -/
theorem physicalEnergyDensity_finiteAngularField {κ : α → Type*} [∀ i,Fintype (κ i)] {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (r : X → ℝ) (s : Finset α) (degree : α → ℕ) (hpos : ∀ i ∈ s,1 ≤ degree i) (hinj : Set.InjOn degree (s : Set α))
    (b : (i : α) → κ i → MvPolynomial I ℝ) (hb : ∀ i ∈ s,∀ t,(b i t).IsHomogeneous (degree i))
    (hΔ : ∀ i ∈ s,∀ t,laplacian (b i t) = 0) (c d : (i : α) → X → κ i → ℝ)
    (hc : ∀ i ∈ s,ContDiffOn ℝ ∞ (c i) Y) (hd : ∀ i ∈ s,ContDiffOn ℝ ∞ (d i) Y)
    {y : X} (hy : y ∈ Y) :
    physicalEnergyDensity g e r (finiteAngularField g e s b c d) y =
      ∑ i ∈ s,pairedModeDensity g e r (degree i) (b i) (c i) (d i) y := by
  unfold physicalEnergyDensity
  simp_rw [fiberSq_finiteAngularField_horizontal hY h hK e he hframe s degree hpos hinj b hb hΔ c d hc hd hy,
    sobolevSq_finiteAngularField g e y (hframe y hy) _ s degree hinj b hb hΔ c d,
    sobolevSq_finiteAngularField_horizontal hY h hK e he hframe _ s degree hpos hinj b hb hΔ c d hc hd hy]
  norm_num only [mul_one,show (2 : ℝ)*(1/2) = 1 by norm_num,show (2 : ℝ)*(3/2) = 3 by norm_num,
    Real.rpow_one,Real.rpow_two,Real.rpow_natCast]
  have hthree (i : α) : (1+(degree i : ℝ))^(3 : ℝ) = (1+(degree i : ℝ))^3 := Real.rpow_natCast _ 3
  simp_rw [hthree]
  exact finite_weighted_energy_sum s (metricDensity g y) (beta g r y)
    (fun i => 1+(degree i : ℝ))
    (fun i => normalizedFischerSquare (degree i) (finitePolynomialField (b i) (c i) y)+
      normalizedFischerSquare (degree i) (finitePolynomialField (b i) (d i) y))
    (fun i j => normalizedFischerSquare (degree i) (covariantPolynomialDerivative g e (b i) (c i) y (e y j))+
      normalizedFischerSquare (degree i) (covariantPolynomialDerivative g e (b i) (d i) y (e y j)))

end ShrinkingSpheres

module

public import Proof.CalderonN.AngularEnergyDensity

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace CalderonN
variable {N : ℕ} [NeZero N]
open OAI.AnisotropicCalderon.AngularPolynomial

variable {α ι : Type*} [Fintype ι]

lemma Profile.integrable_pairedModeDensity {Y : Set (X N)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField N)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame N))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    {r : (X N) → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor)
    (k : ℕ) (b : ι → MvPolynomial (I N) ℝ) (c d : (X N) → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d)
    (hcompactc : HasCompactSupport c) (hcompactd : HasCompactSupport d) (hsuppc : tsupport c ⊆ Y) (hsuppd : tsupport d ⊆ Y) :
    Integrable (pairedModeDensity g e r k b c d) := by
  have hfun : pairedModeDensity g e r k b c d =
      fun y => (modeFischerDensity g e r k b c y+modeFischerDensity g e r k b d y)/sphereNormalization N k := by
    funext y
    exact pairedModeDensity_eq_fischer g e r k b c d y
  rw [hfun]
  exact ((hp.integrable_modeFischerDensity hY h hK e he hfloor k b c hc hcompactc hsuppc).add
    (hp.integrable_modeFischerDensity hY h hK e he hfloor k b d hd hcompactd hsuppd)).div_const _

/-- The exact full energy of a finite angular field is the sum of the individual energies.
    Local integrability is proved before interchanging the base integral and angular sum. -/
theorem Profile.energySq_finiteAngularField {κ : α → Type*} [∀ i,Fintype (κ i)] (hn : 3 ≤ N) {Y : Set (X N)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField N)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame N))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : (X N) → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor)
    (s : Finset α) (degree : α → ℕ) (hpos : ∀ i ∈ s,1 ≤ degree i) (hinj : Set.InjOn degree (s : Set α))
    (b : (i : α) → κ i → MvPolynomial (I N) ℝ) (hb : ∀ i ∈ s,∀ t,(b i t).IsHomogeneous (degree i))
    (hΔ : ∀ i ∈ s,∀ t,laplacian (b i t) = 0) (c d : (i : α) → (X N) → κ i → ℝ)
    (hc : ∀ i ∈ s,ContDiff ℝ ∞ (c i)) (hd : ∀ i ∈ s,ContDiff ℝ ∞ (d i))
    (hcompactc : ∀ i ∈ s,HasCompactSupport (c i)) (hcompactd : ∀ i ∈ s,HasCompactSupport (d i))
    (hsuppc : ∀ i ∈ s,tsupport (c i) ⊆ Y) (hsuppd : ∀ i ∈ s,tsupport (d i) ⊆ Y) :
    energySq Y g e r (finiteAngularField g e s b c d) =
      ∑ i ∈ s,energySq Y g e r (pairedPolynomialField g e (b i) (c i) (d i)) := by
  rw [energySq_eq_integral_density]
  rw [setIntegral_congr_fun hY.measurableSet (fun y hy =>
    physicalEnergyDensity_finiteAngularField hn hY h hK e he hframe r s degree hpos hinj b hb hΔ c d
      (fun i hi => (hc i hi).contDiffOn) (fun i hi => (hd i hi).contDiffOn) hy)]
  rw [integral_finsetSum s (fun i hi => (hp.integrable_pairedModeDensity hY h hK e he hfloor
    (degree i) (b i) (c i) (d i) (hc i hi) (hd i hi) (hcompactc i hi) (hcompactd i hi) (hsuppc i hi) (hsuppd i hi)).integrableOn)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [energySq_eq_integral_density]
  apply setIntegral_congr_fun hY.measurableSet
  intro y hy
  exact (physicalEnergyDensity_pairedPolynomialField hn hY h hK e he hframe r (hpos i hi)
    (b i) (hb i hi) (hΔ i hi) (c i) (d i) (hc i hi).contDiffOn (hd i hi).contDiffOn hy).symm

end CalderonN

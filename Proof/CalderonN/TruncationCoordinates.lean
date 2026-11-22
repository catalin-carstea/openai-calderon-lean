module

public import Proof.CalderonN.ZeroHarmonicComponent
public import Proof.CalderonN.FiniteAngularFields

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace CalderonN
variable {N : ℕ} [NeZero N]
open OAI.AnisotropicCalderon.SphereHarmonic

lemma pairedPolynomialField_eq_degreePart (hn : 3 ≤ N) (g : (MetricField N)) (e : (Frame N)) (y : (X N))
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (φ : (Field N)) (U V : (SphereL2 N))
    (hRe : U =ᵐ[(unitSphereProbability N)] (fun v : (UnitSphere N) => (φ (y,frameVector e y v.val)).re))
    (hIm : V =ᵐ[(unitSphereProbability N)] (fun v : (UnitSphere N) => (φ (y,frameVector e y v.val)).im))
    {ι : Type*} [Fintype ι] (k : ℕ) (b : ι → MvPolynomial (I N) ℝ)
    (hb : ∀ j,b j ∈ harmonicHomogeneous N k) (c d : (X N) → ι → ℝ)
    (hc : polynomialSphereL2 (finitePolynomialField b c y) = (harmonicProjection k U : (SphereL2 N)))
    (hd : polynomialSphereL2 (finitePolynomialField b d y) = (harmonicProjection k V : (SphereL2 N))) (v : (UnitSphere N)) :
    pairedPolynomialField g e b c d (y,frameVector e y v.val) =
      degreePart g e k y (fun w => φ (y,w)) (frameVector e y v.val) := by
  have hHp (f : X N → ι → ℝ) :
      finitePolynomialField b f y ∈ harmonicHomogeneous N k :=
    ⟨finitePolynomialField_homogeneous b (fun i => (hb i).1) f y,
      finitePolynomialField_harmonic b (fun i => (hb i).2) f y⟩
  have hPr (f : X N → ι → ℝ) (u : SphereL2 N)
      (he : polynomialSphereL2 (finitePolynomialField b f y) = (harmonicProjection k u : SphereL2 N)) :
      (harmonicProjectionPolynomial k u).val = finitePolynomialField b f y :=
    (polynomialSphereL2_injective_degree (sphereFischerInner N) k _ _
      (harmonicProjectionPolynomial k u).property (hHp f)).mp
      ((polynomialSphereL2_harmonicProjectionPolynomial k u).trans he.symm)
  rw [degreePart_harmonicProjection_components hn g e y hframe _ U V hRe hIm v k,
    hPr c U hc, hPr d V hd]
  exact movingFrameComplexPolynomial_frameVector g e y hframe _ _ v.val

lemma Test.degreePart_zero {Y : Set (X N)} {g : (MetricField N)} {e : (Frame N)} {φ : (Field N)}
    (hφ : Test Y g e φ) {y : (X N)} (hy : y ∈ Y) (w : (X N)) :
    degreePart g e 0 y (fun v => φ (y,v)) w = 0 := by
  simpa only [degreePart, zonal, harmonicMultiplicity, Nat.cast_one, Complex.ofReal_one, one_mul]
    using hφ.2.2 y hy

lemma smoothNear_finiteAngularField {Y : Set (X N)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField N)}
    (h : Elliptic Y K g) (e : (Frame N)) (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    {α : Type*} {ι : α → Type*} [∀ i,Fintype (ι i)] (s : Finset α)
    (b : (i : α) → ι i → MvPolynomial (I N) ℝ) (c d : (i : α) → (X N) → ι i → ℝ)
    (hc : ∀ i ∈ s,ContDiffOn ℝ ∞ (c i) Y) (hd : ∀ i ∈ s,ContDiffOn ℝ ∞ (d i) Y) :
    smoothNear (finiteAngularField g e s b c d) (bundle Y g) := by
  refine ⟨Prod.fst ⁻¹' Y,hY.preimage continuous_fst,fun p hp => hp.1,?_⟩
  rw [finiteAngularField_eq_sum]
  intro p hp
  have hfun : (∑ i ∈ s,pairedPolynomialField g e (b i) (c i) (d i)) =
      (fun q => ∑ i ∈ s,pairedPolynomialField g e (b i) (c i) (d i) q) := by
    funext q
    simp only [Finset.sum_apply]
  rw [hfun]
  exact (ContDiffAt.sum (fun i hi => contDiffAt_pairedPolynomialField hY h e he (b i) (c i) (d i)
    (hc i hi) (hd i hi) hp p.2)).contDiffWithinAt

end CalderonN

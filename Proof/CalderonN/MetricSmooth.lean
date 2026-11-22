module

public import Proof.CalderonN.MetricDensity
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic

@[expose] public section

/- Port of MetricSmooth.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

lemma Elliptic.contDiffOn_inverse_entry {Ω : Set (X n)} {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) (i j : (I n)) :
    ContDiffOn ℝ ∞ (fun x => (g x)⁻¹ i j) Ω :=
  contDiffOn_metric_inv_entry (h.smoothMetric hK) i j

lemma Elliptic.contDiffOn_christoffel {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) (k i j : (I n)) :
    ContDiffOn ℝ ∞ (fun x => christoffel g x k i j) Ω := by
  have hD (a b c : (I n)) : ContDiffOn ℝ ∞ (coordDeriv a (fun x => g x b c)) Ω :=
    ((h.1 b c).fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  exact (ContDiffOn.sum (fun l _ => (h.contDiffOn_inverse_entry hK k l).mul
    (((hD i l j).add (hD j i l)).sub (hD l i j)))).div_const 2

lemma contDiffOn_vector_component {Ω : Set (X n)} (V : (X n) → (X n)) (hV : ContDiffOn ℝ ∞ V Ω) (i : (I n)) :
    ContDiffOn ℝ ∞ (fun x => V x i) Ω :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hV

lemma Elliptic.contDiffOn_connection {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) (V W : (X n) → (X n))
    (hV : ContDiffOn ℝ ∞ V Ω) (hW : ContDiffOn ℝ ∞ W Ω) :
    ContDiffOn ℝ ∞ (fun x => connection g x (V x) (W x)) Ω := by
  apply (contDiffOn_piLp 2).mpr
  intro k
  change ContDiffOn ℝ ∞ (fun x => ∑ i, ∑ j, christoffel g x k i j * V x i * W x j) Ω
  exact ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
    ((h.contDiffOn_christoffel hΩ hK k i j).mul (contDiffOn_vector_component V hV i)).mul
      (contDiffOn_vector_component W hW j)))

lemma Elliptic.contDiffOn_metricPair {Ω : Set (X n)} {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (V W : (X n) → (X n))
    (hV : ContDiffOn ℝ ∞ V Ω) (hW : ContDiffOn ℝ ∞ W Ω) :
    ContDiffOn ℝ ∞ (fun x => metricPair g x (V x) (W x)) Ω :=
  ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
    ((h.1 i j).mul (contDiffOn_vector_component V hV i)).mul (contDiffOn_vector_component W hW j)))

lemma Elliptic.contDiffOn_frameConnection {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (V : (X n) → (X n)) (hV : ContDiffOn ℝ ∞ V Ω) (i j : (I n)) :
    ContDiffOn ℝ ∞ (fun x => frameConnectionCoefficient g e x (V x) i j) Ω :=
  h.contDiffOn_metricPair _ _
    ((((he i).fderiv_of_isOpen hΩ (by simp)).clm_apply hV).add
      (h.contDiffOn_connection hΩ hK V (fun x => e x i) hV (he i))) (he j)

end CalderonN

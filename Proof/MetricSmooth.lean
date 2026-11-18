import Proof.MetricDensity
import Proof.FrameConnection
import Mathlib.Analysis.Calculus.ContDiff.WithLp

noncomputable section
open Set
open scoped ContDiff
namespace ShrinkingSpheres

lemma contDiffOn_det_entries {Ω : Set X} (g : MetricField)
    (h : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) Ω) :
    ContDiffOn ℝ ∞ (fun x => (g x).det) Ω := by
  classical
  simp_rw [Matrix.det_apply']
  exact ContDiffOn.sum (fun σ _ => contDiffOn_const.mul (contDiffOn_prod (fun i _ => h (σ i) i)))

lemma Elliptic.contDiffOn_adjugate_entry {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (i j : I) : ContDiffOn ℝ ∞ (fun x => (g x).adjugate i j) Ω := by
  classical
  simp_rw [Matrix.adjugate_apply]
  apply contDiffOn_det_entries (fun x => (g x).updateRow j (Pi.single i 1))
  intro a b
  by_cases ha : a = j
  · subst a
    simp only [Matrix.updateRow_self]
    exact contDiffOn_const
  · simpa [Matrix.updateRow_apply, ha] using h.1 a b

lemma Elliptic.contDiffOn_inverse_entry {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (i j : I) :
    ContDiffOn ℝ ∞ (fun x => (g x)⁻¹ i j) Ω := by
  have hd := (contDiffOn_det_entries g h.1).inv (fun x hx => (h.posDef hK hx).det_pos.ne')
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact hd.mul (h.contDiffOn_adjugate_entry i j)

lemma Elliptic.contDiffOn_christoffel {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (k i j : I) :
    ContDiffOn ℝ ∞ (fun x => christoffel g x k i j) Ω := by
  have hD (a b c : I) : ContDiffOn ℝ ∞ (coordDeriv a (fun x => g x b c)) Ω :=
    ((h.1 b c).fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  exact (ContDiffOn.sum (fun l _ => (h.contDiffOn_inverse_entry hK k l).mul
    (((hD i l j).add (hD j i l)).sub (hD l i j)))).div_const 2

lemma contDiffOn_vector_component {Ω : Set X} (V : X → X) (hV : ContDiffOn ℝ ∞ V Ω) (i : I) :
    ContDiffOn ℝ ∞ (fun x => V x i) Ω :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hV

lemma Elliptic.contDiffOn_connection {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (V W : X → X)
    (hV : ContDiffOn ℝ ∞ V Ω) (hW : ContDiffOn ℝ ∞ W Ω) :
    ContDiffOn ℝ ∞ (fun x => connection g x (V x) (W x)) Ω := by
  apply (contDiffOn_piLp 2).mpr
  intro k
  change ContDiffOn ℝ ∞ (fun x => ∑ i, ∑ j, christoffel g x k i j * V x i * W x j) Ω
  exact ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
    ((h.contDiffOn_christoffel hΩ hK k i j).mul (contDiffOn_vector_component V hV i)).mul
      (contDiffOn_vector_component W hW j)))

lemma Elliptic.contDiffOn_metricPair {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (V W : X → X)
    (hV : ContDiffOn ℝ ∞ V Ω) (hW : ContDiffOn ℝ ∞ W Ω) :
    ContDiffOn ℝ ∞ (fun x => metricPair g x (V x) (W x)) Ω :=
  ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
    ((h.1 i j).mul (contDiffOn_vector_component V hV i)).mul (contDiffOn_vector_component W hW j)))

lemma Elliptic.contDiffOn_frameConnection {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (V : X → X) (hV : ContDiffOn ℝ ∞ V Ω) (i j : I) :
    ContDiffOn ℝ ∞ (fun x => frameConnectionCoefficient g e x (V x) i j) Ω :=
  h.contDiffOn_metricPair _ _
    ((((he i).fderiv_of_isOpen hΩ (by simp)).clm_apply hV).add
      (h.contDiffOn_connection hΩ hK V (fun x => e x i) hV (he i))) (he j)

end ShrinkingSpheres

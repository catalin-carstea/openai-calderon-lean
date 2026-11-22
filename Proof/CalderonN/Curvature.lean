module

public import Proof.CalderonN.MetricSmooth
public import Proof.CalderonN.MetricConnection
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic

@[expose] public section

/- Port of Curvature.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

open Set


variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def vectorFieldDeriv (V : E → E) (u : E → F) (z : E) : F := fderiv ℝ u z (V z)

/-- The second derivatives cancel at the point under local smoothness hypotheses. -/
lemma vectorFieldDeriv_commutator_at (V W : E → E) (u : E → F) (z : E)
    (hV : DifferentiableAt ℝ V z) (hW : DifferentiableAt ℝ W z) (hu : ContDiffAt ℝ ∞ u z) :
    vectorFieldDeriv V (vectorFieldDeriv W u) z -
      vectorFieldDeriv W (vectorFieldDeriv V u) z =
      fderiv ℝ u z (fderiv ℝ W z (V z) - fderiv ℝ V z (W z)) := by
  have hD := (hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  unfold vectorFieldDeriv
  rw [fderiv_clm_apply hD hW, fderiv_clm_apply hD hV]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  rw [(hu.isSymmSndFDerivAt (by simp)).eq (V z) (W z), map_sub]
  abel

def coordinateCurvature (Γ : (X n) → (X n) →L[ℝ] (X n) →L[ℝ] (X n)) (y a b w : (X n)) : (X n) :=
  (fderiv ℝ Γ y a) b w - (fderiv ℝ Γ y b) a w + Γ y a (Γ y b w) - Γ y b (Γ y a w)

def horizontalVectorField (Γ : (X n) → (X n) →L[ℝ] (X n) →L[ℝ] (X n)) (V : (X n) → (X n)) : (X n) × (X n) → (X n) × (X n) :=
  fun z => (V z.1, -Γ z.1 (V z.1) z.2)

def baseVectorFieldBracket (V W : (X n) → (X n)) (y : (X n)) : (X n) :=
  fderiv ℝ W y (V y) - fderiv ℝ V y (W y)

lemma differentiableAt_horizontalVectorField (Γ : (X n) → (X n) →L[ℝ] (X n) →L[ℝ] (X n)) (V : (X n) → (X n))
    (z : (X n) × (X n)) (hΓ : DifferentiableAt ℝ Γ z.1) (hV : DifferentiableAt ℝ V z.1) :
    DifferentiableAt ℝ (horizontalVectorField Γ V) z :=
  (hV.comp z differentiableAt_fst).prodMk
    (((hΓ.comp z differentiableAt_fst).clm_apply (hV.comp z differentiableAt_fst)).clm_apply
      differentiableAt_snd).neg

lemma fderiv_horizontalVectorField (Γ : (X n) → (X n) →L[ℝ] (X n) →L[ℝ] (X n)) (V : (X n) → (X n))
    (z a : (X n) × (X n)) (hΓ : DifferentiableAt ℝ Γ z.1) (hV : DifferentiableAt ℝ V z.1) :
    fderiv ℝ (horizontalVectorField Γ V) z a =
      (fderiv ℝ V z.1 a.1, -((fderiv ℝ Γ z.1 a.1) (V z.1) z.2) -
        Γ z.1 (fderiv ℝ V z.1 a.1) z.2 - Γ z.1 (V z.1) a.2) := by
  have hfst : HasFDerivAt (Prod.fst : X n × X n → X n)
      (ContinuousLinearMap.fst ℝ (X n) (X n)) z := hasFDerivAt_fst
  have hg := HasFDerivAt.comp (G := X n →L[ℝ] X n →L[ℝ] X n) z hΓ.hasFDerivAt hfst
  have hv := HasFDerivAt.comp (G := X n) z hV.hasFDerivAt hfst
  have hh := hv.prodMk ((hg.clm_apply hv).clm_apply (hasFDerivAt_snd (𝕜 := ℝ) (p := z))).neg
  change HasFDerivAt (horizontalVectorField Γ V) _ z at hh
  rw [hh.fderiv]
  change (fderiv ℝ V z.1 a.1, -(Γ z.1 (V z.1) a.2 +
    (Γ z.1 (fderiv ℝ V z.1 a.1) + (fderiv ℝ Γ z.1 a.1) (V z.1)) z.2)) = _
  simp only [_root_.add_apply]
  congr 1
  abel

lemma horizontalVectorField_bracket (Γ : (X n) → (X n) →L[ℝ] (X n) →L[ℝ] (X n)) (V W : (X n) → (X n))
    (z : (X n) × (X n)) (hΓ : DifferentiableAt ℝ Γ z.1)
    (hV : DifferentiableAt ℝ V z.1) (hW : DifferentiableAt ℝ W z.1) :
    fderiv ℝ (horizontalVectorField Γ W) z (horizontalVectorField Γ V z) -
      fderiv ℝ (horizontalVectorField Γ V) z (horizontalVectorField Γ W z) =
      horizontalVectorField Γ (baseVectorFieldBracket V W) z +
        (0, -coordinateCurvature Γ z.1 (V z.1) (W z.1) z.2) := by
  rw [fderiv_horizontalVectorField Γ W z _ hΓ hW, fderiv_horizontalVectorField Γ V z _ hΓ hV]
  simp only [horizontalVectorField, baseVectorFieldBracket, Prod.mk_sub_mk, Prod.mk_add_mk,
    add_zero, coordinateCurvature, map_neg, map_sub, _root_.sub_apply]
  congr 1
  abel

/-- The horizontal commutator is the vertical action of the actual coordinate curvature,
    after subtracting the horizontal lift of the base bracket. -/
theorem horizontalVectorField_covariant_commutator (Γ : (X n) → (X n) →L[ℝ] (X n) →L[ℝ] (X n))
    (V W : (X n) → (X n)) (u : (X n) × (X n) → F) (z : (X n) × (X n))
    (hΓ : DifferentiableAt ℝ Γ z.1) (hV : DifferentiableAt ℝ V z.1)
    (hW : DifferentiableAt ℝ W z.1) (hu : ContDiffAt ℝ ∞ u z) :
    vectorFieldDeriv (horizontalVectorField Γ V) (vectorFieldDeriv (horizontalVectorField Γ W) u) z -
      vectorFieldDeriv (horizontalVectorField Γ W) (vectorFieldDeriv (horizontalVectorField Γ V) u) z -
      vectorFieldDeriv (horizontalVectorField Γ (baseVectorFieldBracket V W)) u z =
      fderiv ℝ u z (0, -coordinateCurvature Γ z.1 (V z.1) (W z.1) z.2) := by
  rw [vectorFieldDeriv_commutator_at _ _ u z
    (differentiableAt_horizontalVectorField Γ V z hΓ hV)
    (differentiableAt_horizontalVectorField Γ W z hΓ hW) hu,
    horizontalVectorField_bracket Γ V W z hΓ hV hW, map_add]
  simp only [vectorFieldDeriv]
  abel

lemma Elliptic.contDiffOn_connectionBilinear {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) :
    ContDiffOn ℝ ∞ (connectionBilinear g) Ω := by
  unfold connectionBilinear
  refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ => ?_
  let v : X n →L[ℝ] X n →L[ℝ] X n :=
    (EuclideanSpace.proj i).smulRight ((EuclideanSpace.proj j).smulRight (axis k))
  let L : ℝ →L[ℝ] X n →L[ℝ] X n →L[ℝ] X n := ContinuousLinearMap.toSpanSingleton ℝ v
  have hL : ContDiff ℝ ∞ L :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := ℝ) (F := X n →L[ℝ] X n →L[ℝ] X n) L
  exact hL.comp_contDiffOn (h.contDiffOn_christoffel hΩ hK k i j)

def metricCurvature (g : (MetricField n)) (y a b w : (X n)) : (X n) := coordinateCurvature (connectionBilinear g) y a b w

theorem metric_horizontal_commutator {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) (V W : (X n) → (X n))
    (hV : ContDiffOn ℝ ∞ V Ω) (hW : ContDiffOn ℝ ∞ W Ω)
    (u : (X n) × (X n) → F) {y : (X n)} (hy : y ∈ Ω) (w : (X n)) (hu : ContDiffAt ℝ ∞ u (y,w)) :
    vectorFieldDeriv (horizontalVectorField (connectionBilinear g) V)
        (vectorFieldDeriv (horizontalVectorField (connectionBilinear g) W) u) (y,w) -
      vectorFieldDeriv (horizontalVectorField (connectionBilinear g) W)
        (vectorFieldDeriv (horizontalVectorField (connectionBilinear g) V) u) (y,w) -
      vectorFieldDeriv (horizontalVectorField (connectionBilinear g) (baseVectorFieldBracket V W)) u (y,w) =
      fderiv ℝ u (y,w) (0, -metricCurvature g y (V y) (W y) w) :=
  horizontalVectorField_covariant_commutator _ V W u (y,w)
    (((h.contDiffOn_connectionBilinear hΩ hK).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
    ((hV.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
    ((hW.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)) hu

end CalderonN

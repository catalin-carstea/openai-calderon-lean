module

public import Proof.CalderonPatch.MatchedCoordinates

import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Tactic.Ring
import Proof.CalderonN.LinearMetric
import Proof.CalderonN.MetricPair

@[expose] public section

noncomputable section
open Bundle Matrix Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN (I X axis MetricField metricPair vector_eq_sum_axis metricPair_eq_dotProduct)

variable {n : ℕ} [NeZero n] {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) 1 M]

local notation "J" => (𝓡∂ n)
local notation "K" => 𝓘(ℝ, X n)

/-- The native metric in an interior chart, expressed in its coordinate basis. -/
def coordinateMetric (g : SmoothMetric n M) (e : OpenPartialHomeomorph M (X n)) : MetricField n :=
  fun x i j =>
    let D := mfderiv K J e.symm x
    g.inner (e.symm x) (D (axis i)) (D (axis j))

theorem realizesCoordinateMetric (g : SmoothMetric n M) (e : OpenPartialHomeomorph M (X n)) :
    RealizesCoordinateMetric g e (coordinateMetric g e) := by
  intro x hx v w
  let D : X n →L[ℝ] X n := mfderiv K J e.symm x
  let b : X n →L[ℝ] X n →L[ℝ] ℝ := g.inner (e.symm x)
  have hsum (a : X n) : D a = ∑ i : I n, a i • D (axis i) := by
    calc
      D a = D (∑ i : I n, a i • axis i) := congrArg D (vector_eq_sum_axis a).symm
      _ = _ := by
        rw [map_sum D]
        simp only [map_smul]
  change metricPair (coordinateMetric g e) x v w = b (D v) (D w)
  rw [hsum v, hsum w]
  simp only [metricPair, coordinateMetric, map_sum, map_smul, _root_.sum_apply,
    _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    change b (D (axis i)) (D (axis j)) * v i * w j = w j * (v i * b (D (axis i)) (D (axis j)))
    ring

theorem coordinateMetric_posDef (g : SmoothMetric n M) (e : OpenPartialHomeomorph M (X n))
    (he : e.MDifferentiable J K) {x : X n} (hx : x ∈ e.target) :
    (coordinateMetric g e x).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    change star (coordinateMetric g e x j i) = coordinateMetric g e x i j
    rw [star_trivial]
    exact g.symm _ _ _
  · intro v hv
    let v' : X n := WithLp.toLp 2 v
    have hv' : v' ≠ 0 := by
      intro h
      exact hv (congrArg WithLp.ofLp h)
    have h := realizesCoordinateMetric g e x hx v' v'
    rw [metricPair_eq_dotProduct] at h
    rw [show star v = v from star_trivial v]
    change 0 < (fun i => v' i) ⬝ᵥ (coordinateMetric g e x *ᵥ (fun i => v' i))
    rw [h]
    apply g.pos
    intro hzero
    apply hv'
    apply he.symm.mfderiv_injective hx
    exact hzero.trans ((mfderiv K J e.symm x).map_zero).symm

theorem coordinateMetric_smooth (g : SmoothMetric n M) (e : OpenPartialHomeomorph M (X n))
    (he : ContMDiffOn J K ∞ e e.source) (hinv : ContMDiffOn K J ∞ e.symm e.target) :
    CalderonN.SmoothMetric e.target (coordinateMetric g e) := by
  refine ⟨?_, fun x hx => coordinateMetric_posDef g e
    ⟨he.mdifferentiableOn (by simp), hinv.mdifferentiableOn (by simp)⟩ hx⟩
  let _ : RiemannianBundle (fun x : M => TangentSpace J x) := ⟨g.toRiemannianMetric⟩
  have haxis (i : I n) : ContMDiffOn K (ModelWithCorners.tangent J) ∞
      (fun x : X n => (⟨e.symm x, mfderiv K J e.symm x (axis i)⟩ :
        TangentBundle J M)) e.target := by
    let σ : X n → TangentBundle K (X n) := fun x => ⟨x, axis i⟩
    have hσ : ContMDiff K (ModelWithCorners.tangent K) ∞ σ := by
      let d := tangentBundleModelSpaceDiffeomorph K ⊤
      have hpair : ContMDiff K (ModelWithCorners.prod K K) ∞
          (fun x : X n => (x, axis i)) := contMDiff_id.prodMk contMDiff_const
      rw [chartedSpaceSelf_prod] at hpair
      exact d.symm.contMDiff.comp hpair
    have hD := hinv.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
      e.open_target.uniqueMDiffOn
    refine (hD.comp hσ.contMDiffOn (fun x hx => hx)).congr ?_
    intro x hx
    change _ = (⟨e.symm x, mfderivWithin K J e.symm e.target x (axis i)⟩ : TangentBundle J M)
    rw [mfderivWithin_of_isOpen e.open_target hx]
  intro i j
  rw [← contMDiffOn_iff_contDiffOn]
  exact (haxis i).inner_bundle (haxis j)

end CalderonPatch

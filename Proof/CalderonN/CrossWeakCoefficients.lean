module

public import Proof.CalderonN.HarmonicL2Space
public import Proof.CalderonN.CrossPairing

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Ring

public section

open Set Filter MeasureTheory
open scoped ENNReal

namespace CalderonN

variable {d : ℕ} [NeZero d]
open LocalMetricExtension

/-- Every square-integrable slice is represented by a classical harmonic
function. Orthogonality and Fubini keep its Hilbert coefficient in the
same closed space. -/
theorem tensorCoefficient_mem_harmonicL2Space {S U : Set (X d)}
    (hS : MeasurableSet S) (hU : IsOpen U) {g : (MetricField d)} (hg : SmoothMetric U g)
    (v : ChartL2 (d := d) S)
    (Q : Lp ℝ 2 (((volume : Measure (X d)).restrict S).prod ((volume : Measure (X d)).restrict U)))
    {F : (X d) × (X d) → ℝ}
    (hQ : (Q : (X d) × (X d) → ℝ) =ᵐ[((volume : Measure (X d)).restrict S).prod
      ((volume : Measure (X d)).restrict U)] F)
    (hF : ∀ x ∈ S, Harmonic U g (fun y => F (x,y))) :
    tensorCoefficient v Q ∈ harmonicL2Space hU hg := by
  let L := harmonicL2Space hU hg
  change tensorCoefficient v Q ∈ L
  rw [← ClosedSubmodule.orthogonal_orthogonal_eq L, ClosedSubmodule.mem_orthogonal']
  intro ψ hψ
  rw [tensorCoefficient_inner_integral]
  calc
    _ = ∫ x in S, (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [Measure.ae_ae_of_ae_prod hQ,ae_restrict_mem hS,ae_memLp_right_of_prod Q]
        with x hx hxS hL
      let w := hL.toLp (fun y => Q (x,y))
      have hw : w ∈ L := (mem_harmonicL2Space_iff hU hg w).mpr
        ⟨_,hF x hxS,hL.coeFn_toLp.trans hx⟩
      have hz := (ClosedSubmodule.mem_orthogonal L ψ).mp hψ w hw
      have htest : (∫ y in U, Q (x,y) * ψ y) = inner ℝ w ψ := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hL.coeFn_toLp] with y hy
        rw [RCLike.inner_apply,conj_trivial,show w y = Q (x,y) from hy]
        ring
      rw [htest,hz,mul_zero]
    _ = 0 := integral_zero _ _

end CalderonN

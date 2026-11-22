module

public import Proof.CalderonN.GeodesicFirstVariation

import Proof.CalderonN.CovariantHessian
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Differentiating the actual geodesic equation yields the coordinate
Jacobi equation, with the Christoffel symbols of the same metric. -/
theorem coordinate_jacobi_equation
    {Ω : Set (X dim)} (hΩ : IsOpen Ω) {γ : (MetricField dim)} (hγ : SmoothMetric Ω γ)
    {q : ℝ × ℝ → (X dim)} (hq : ContDiff ℝ ∞ q)
    (hfamily : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
      q (s,t) ∈ Ω ∧ timeVelocity (timeVelocity q) (s,t) =
        -connection γ (q (s,t)) (timeVelocity q (s,t)) (timeVelocity q (s,t)))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (k : (I dim)) :
    let x := q (0,t)
    let v := timeVelocity q (0,t)
    let J := pathVariation q (0,t)
    let J' := timeVelocity (pathVariation q) (0,t)
    timeVelocity (timeVelocity (pathVariation q)) (0,t) k =
      - ∑ i, ∑ j, (fderiv ℝ (fun y => christoffel γ y k i j) x J * v i * v j +
        christoffel γ x k i j * (J' i * v j + v i * J' j)) := by
  let x := q (0,t)
  let T := timeVelocity q
  let v := T (0,t)
  let J := pathVariation q (0,t)
  let J' := timeVelocity (pathVariation q) (0,t)
  let G (i j : (I dim)) (s : ℝ) := christoffel γ (q (s,t)) k i j
  let V (i : (I dim)) (s : ℝ) := T (s,t) i
  have hqD : HasDerivAt (fun s => q (s,t)) J 0 :=
    hasDerivAt_variation_slice (hq.differentiable (by simp) (0,t))
  have hTD : HasDerivAt (fun s => T (s,t)) J' 0 := by
    change HasDerivAt (fun s => timeVelocity q (s,t)) (timeVelocity (pathVariation q) (0,t)) 0
    rw [← mixed_slice_deriv_eq hq]
    exact hasDerivAt_variation_slice ((contDiff_timeVelocity hq).differentiable (by simp) (0,t))
  have hG (i j : (I dim)) : HasDerivAt (G i j)
      (fderiv ℝ (fun y => christoffel γ y k i j) x J) 0 :=
    by
      have H : HasFDerivAt (fun y => christoffel γ y k i j)
          (fderiv ℝ (fun y => christoffel γ y k i j) x) x :=
        (((contDiffOn_christoffel hΩ hγ k i j).contDiffAt
          (hΩ.mem_nhds (hfamily.self_of_nhds t ht).1)).differentiableAt
            (by simp)).hasFDerivAt
      exact H.comp_hasDerivAt 0 hqD
  have hV (i : (I dim)) : HasDerivAt (V i) (J' i) 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) i : (X dim) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 hTD
  have hsum : HasDerivAt
      (fun s => -(∑ i, ∑ j, G i j s * V i s * V j s))
      (-∑ i, ∑ j, (fderiv ℝ (fun y => christoffel γ y k i j) x J * v i * v j +
        christoffel γ x k i j * (J' i * v j + v i * J' j))) 0 := by
    convert (HasDerivAt.fun_sum (u := (Finset.univ : Finset (I dim))) fun i _ =>
      HasDerivAt.fun_sum (u := (Finset.univ : Finset (I dim))) fun j _ =>
        ((hG i j).mul (hV i)).mul (hV j)).neg using 1
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [G,V,v,x,Pi.mul_apply]
    ring
  have hacc := (contDiff_timeVelocity (contDiff_timeVelocity hq)).differentiable (by simp) (0,t)
  have hleft : HasDerivAt (fun s => timeVelocity (timeVelocity q) (s,t) k)
      (pathVariation (timeVelocity (timeVelocity q)) (0,t) k) 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) k : (X dim) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0
      (hasDerivAt_variation_slice hacc)
  have he : (fun s => timeVelocity (timeVelocity q) (s,t) k) =ᶠ[𝓝 (0 : ℝ)]
      fun s => -(∑ i, ∑ j, G i j s * V i s * V j s) := by
    filter_upwards [hfamily] with s h
    rw [(h t ht).2]
    simp only [connection,PiLp.neg_apply,G,V,T]
  have hcomm : pathVariation (timeVelocity q) = timeVelocity (pathVariation q) := by
    funext p
    exact mixed_slice_deriv_eq hq p.1 p.2
  have h := hleft.unique (hsum.congr_of_eventuallyEq he)
  rw [mixed_slice_deriv_eq (contDiff_timeVelocity hq),hcomm] at h
  exact h

end CalderonN

module

public import Proof.CalderonPatch.BoundaryNormalChart
public import Proof.CalderonN.GeodesicFirstVariation

import Proof.CalderonN.MetricPair
import Proof.CalderonN.SphereFrame
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

public section

noncomputable section
open Filter Metric Set
open scoped ContDiff Topology

namespace CalderonPatch

open CalderonN (I X MetricField axis metricPair GeodesicPhase GeodesicFlowOn geodesicEndpoint
  timeVelocity pathVariation connection hasDerivAt_geodesicTime hasDerivAt_variation_slice)

variable {n : ℕ} [NeZero n]

private theorem timeVelocity_eq_deriv {Q : ℝ × ℝ → X n} (hQ : ContDiff ℝ ∞ Q) (s t : ℝ) :
    timeVelocity Q (s,t) = deriv (fun a => Q (s,a)) t :=
  (hasDerivAt_geodesicTime (hQ.differentiable (by simp) (s,t))).deriv.symm

set_option maxHeartbeats 2200000 in
/-- The actual boundary normal flow gives a unit normal direction
orthogonal to the transported tangent hyperplane. -/
theorem boundaryNormalEndpoint_unit_orthogonal {g : MetricField n} (hg : CalderonN.SmoothMetric univ g)
    {p q : X n} {i : I n} {r : ℝ} {F : GeodesicPhase n → ℝ → GeodesicPhase n}
    (hF : GeodesicFlowOn (fun _ => g) ({(0 : ℝ)} ×ˢ closedBall p 1) r F)
    (hr : 0 < r) (hq : q ∈ ball p 1) (hq₀ : q i = 0) (t : ℝ)
    (ht : ‖t • positiveCoordinateNormal g i q‖ < r) :
    let f := boundaryNormalEndpoint g i F
    let x := q + t • axis i
    let D := fderiv ℝ f x
    metricPair g (f x) (D (axis i)) (D (axis i)) = 1 ∧
      ∀ v : X n, v i = 0 → metricPair g (f x) (D (axis i)) (D v) = 0 := by
  let f := boundaryNormalEndpoint g i F
  let ν := positiveCoordinateNormal g i
  let hf := boundaryNormalEndpoint_smooth hF hg i
  let x := q + t • axis i
  let D := fderiv ℝ f x
  have hν : ContDiff ℝ ∞ ν := contDiffOn_univ.mp (contDiffOn_positiveCoordinateNormal hg i)
  have hAxis : axis i i = 1 := by simp [axis]
  change metricPair g (f x) (D (axis i)) (D (axis i)) = 1 ∧
    ∀ v : X n, v i = 0 → metricPair g (f x) (D (axis i)) (D v) = 0
  by_cases ht₀ : t = 0
  · have hx : x = q := by simp [x, ht₀]
    have hfq : f q = q := by
      change geodesicEndpoint F ((0, boundaryFoot i q), q i • ν (boundaryFoot i q)) = q
      rw [boundaryFoot_on_face i hq₀, hq₀, zero_smul]
      exact hF.endpoint_rest ⟨mem_singleton _, ball_subset_closedBall hq⟩
    have hD : D = boundaryFoot i + (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (ν q) := by
      change fderiv ℝ f x = _
      rw [hx]
      exact (boundaryNormalEndpoint_hasFDerivAt hF hr hg hq₀ hq).fderiv
    have hdE : D (axis i) = ν q := by
      rw [hD]
      change boundaryFoot i (axis i) + axis i i • ν q = _
      rw [boundaryFoot_apply, hAxis, one_smul, sub_self, zero_add, one_smul]
    have hfv : f x = q := by rw [hx, hfq]
    refine ⟨by rw [hfv, hdE]; exact positiveCoordinateNormal_unit g (hg.2 q (mem_univ _)) i, ?_⟩
    intro v hv
    have hdv : D v = v := by
      rw [hD]
      change boundaryFoot i v + v i • ν q = v
      rw [boundaryFoot_on_face i hv, hv, zero_smul, add_zero]
    rw [hfv, hdE, hdv, metricPair_positiveCoordinateNormal g (hg.2 q (mem_univ _)), hv, mul_zero]
  · have hProbe (v : X n) (hv : v i = 0) :
        metricPair g (f x) (D (axis i)) (D (axis i)) = 1 ∧
          metricPair g (f x) (D (axis i)) (D v) = 0 := by
      let z : ℝ → X n := fun s => q + s • v
      let Q : ℝ × ℝ → X n := fun p => f (z p.1 + (p.2 * t) • axis i)
      have hz : ContDiff ℝ ∞ z := contDiff_const.add (contDiff_id.smul contDiff_const)
      have hz₀ : z 0 = q := by simp [z]
      have hQ : ContDiff ℝ ∞ Q := hf.comp
        ((hz.comp contDiff_fst).add ((contDiff_snd.mul contDiff_const).smul contDiff_const))
      have hCoord (s a : ℝ) : (z s + (a * t) • axis i) i = a * t := by
        have hzFace : z s i = 0 := by simp [z, hq₀, hv]
        simp [hzFace, hAxis]
      have hFoot (s a : ℝ) : boundaryFoot i (z s + (a * t) • axis i) = z s := by
        rw [boundaryFoot_apply, hCoord, add_sub_cancel_right]
      have hRadial (s : ℝ) : (fun a => Q (s,a)) =
          fun a => geodesicEndpoint F ((0,z s), a • (t • ν (z s))) := by
        funext a
        change geodesicEndpoint F ((0, boundaryFoot i (z s + (a * t) • axis i)),
          (z s + (a * t) • axis i) i • ν (boundaryFoot i (z s + (a * t) • axis i))) = _
        rw [hFoot, hCoord, mul_smul]
      have hGood : ∀ᶠ s in 𝓝 (0 : ℝ), z s ∈ ball p 1 ∧ ‖t • ν (z s)‖ < r := by
        have h₁ := hz.continuous.continuousAt.eventually_mem (hz₀.symm ▸ isOpen_ball.mem_nhds hq)
        have hνz : Continuous (fun s : ℝ => ν (z s)) := hν.continuous.comp hz.continuous
        have hc : Continuous (fun s : ℝ => ‖t • ν (z s)‖) := by
          simp only [norm_smul]
          exact continuous_const.mul hνz.norm
        have h₀ : ‖t • ν (z (0 : ℝ))‖ < r := by rwa [hz₀]
        have h₂ : ∀ᶠ s : ℝ in 𝓝 0, ‖t • ν (z s)‖ < r :=
          (isOpen_lt hc continuous_const).mem_nhds h₀
        exact h₁.and h₂
      have hPath : ∀ᶠ s in 𝓝 (0 : ℝ),
          Q (s,0) = z s ∧ timeVelocity Q (s,0) = t • ν (z s) ∧ ∀ a ∈ Icc (0 : ℝ) 1,
            Q (s,a) ∈ (univ : Set (X n)) ∧ timeVelocity (timeVelocity Q) (s,a) =
              -connection g (Q (s,a)) (timeVelocity Q (s,a)) (timeVelocity Q (s,a)) := by
        filter_upwards [hGood] with s hs
        have hvel : t • ν (z s) ∈ closedBall (0 : X n) r := mem_closedBall_zero_iff.mpr hs.2.le
        have hpK : (0,z s) ∈ ({(0 : ℝ)} ×ˢ closedBall p 1) := ⟨mem_singleton _, ball_subset_closedBall hs.1⟩
        have h := hF.radial_geodesic hpK hvel
        have hQ₀ : Q (s,0) = z s := by
          have hh := congrFun (hRadial s) 0
          change Q (s,0) = geodesicEndpoint F ((0,z s), (0 : ℝ) • (t • ν (z s))) at hh
          rw [zero_smul, hF.endpoint_rest hpK] at hh
          exact hh
        refine ⟨hQ₀, (timeVelocity_eq_deriv hQ s 0).trans ?_, fun a ha => ⟨mem_univ _, ?_⟩⟩
        · rw [hRadial]; exact h.2.1
        · have hvEq : (fun a => timeVelocity Q (s,a)) = deriv (fun a => Q (s,a)) :=
            funext fun a => timeVelocity_eq_deriv hQ s a
          rw [timeVelocity_eq_deriv (CalderonN.contDiff_timeVelocity hQ), hvEq]
          let c : ℝ → X n := fun a => geodesicEndpoint F ((0,z s), a • (t • ν (z s)))
          have hAcc : deriv (deriv c) a = -connection g (c a) (deriv c a) (deriv c a) := h.2.2 a ha
          have hc : (fun a => Q (s,a)) = c := hRadial s
          rw [← hc] at hAcc
          rw [timeVelocity_eq_deriv hQ]
          exact hAcc
      have hIni : (fun s => metricPair g (Q (s,0)) (timeVelocity Q (s,0)) (timeVelocity Q (s,0)) / 2)
          =ᶠ[𝓝 (0 : ℝ)] fun _ => t ^ 2 / 2 := by
        filter_upwards [hPath] with s hs
        rw [hs.1, hs.2.1, CalderonN.metricPair_smul_same,
          positiveCoordinateNormal_unit g (hg.2 _ (mem_univ _)), mul_one]
      have hQ₀ := hPath.self_of_nhds
      have hzD : HasDerivAt z v 0 := by
        simpa only [id_eq, one_smul, zero_add] using
          HasDerivAt.fun_add (hasDerivAt_const (0 : ℝ) q) ((hasDerivAt_id (0 : ℝ)).smul_const v)
      have hZvar : pathVariation Q (0,0) = v := by
        have hSame : (fun s => Q (s,0)) =ᶠ[𝓝 (0 : ℝ)] z := hPath.mono fun _ hs => hs.1
        exact (hasDerivAt_variation_slice (hQ.differentiable (by simp) (0,0))).unique
          (hzD.congr_of_eventuallyEq hSame)
      have hEnd : Q (0,1) = f x := by simp [Q, z, x]
      have htEnd : timeVelocity Q (0,1) = t • D (axis i) := by
        have hc : HasDerivAt (fun a : ℝ => z 0 + (a * t) • axis i) (t • axis i) 1 := by
          simpa only [id_eq, one_mul, zero_add] using
            HasDerivAt.fun_add (hasDerivAt_const (1 : ℝ) (z 0))
              (((hasDerivAt_id (1 : ℝ)).mul_const t).smul_const (axis i))
        have hD : HasFDerivAt f D (z 0 + (1 * t) • axis i) := by
          simpa only [hz₀, one_mul, x] using (hf.differentiable (by simp) x).hasFDerivAt
        have hComp : HasDerivAt (fun a => Q (0,a)) (D (t • axis i)) 1 := by
          change HasDerivAt (f ∘ fun a => z 0 + (a * t) • axis i) _ _
          exact hD.comp_hasDerivAt 1 hc
        have h := (hasDerivAt_geodesicTime (hQ.differentiable (by simp) (0,1))).unique hComp
        rwa [map_smul] at h
      have hvEnd : pathVariation Q (0,1) = D v := by
        have hc : HasDerivAt (fun s : ℝ => z s + (1 * t) • axis i) v 0 := by
          simpa only [add_zero] using
            HasDerivAt.fun_add hzD (hasDerivAt_const (0 : ℝ) ((1 * t) • axis i))
        have hD : HasFDerivAt f D (z 0 + (1 * t) • axis i) := by
          simpa only [hz₀, one_mul, x] using (hf.differentiable (by simp) x).hasFDerivAt
        have hComp : HasDerivAt (fun s => Q (s,1)) (D v) 0 := by
          change HasDerivAt (f ∘ fun s => z s + (1 * t) • axis i) _ _
          exact hD.comp_hasDerivAt 0 hc
        exact (hasDerivAt_variation_slice (hQ.differentiable (by simp) (0,1))).unique hComp
      have hSpeed := CalderonN.geodesic_squaredSpeed_eq_initial isOpen_univ hg hQ hQ₀.2.2
        (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
      rw [hEnd, htEnd, hQ₀.1, hQ₀.2.1, hz₀, CalderonN.metricPair_smul_same,
        CalderonN.metricPair_smul_same, positiveCoordinateNormal_unit g (hg.2 q (mem_univ _)), mul_one] at hSpeed
      have hVariation := (CalderonN.geodesic_firstVariation isOpen_univ hg hQ (hPath.mono fun _ hs => hs.2.2)).unique
        ((hasDerivAt_const (0 : ℝ) (t ^ 2 / 2)).congr_of_eventuallyEq hIni)
      rw [hEnd, htEnd, hvEnd, hQ₀.1, hQ₀.2.1, hz₀, hZvar, CalderonN.metricPair_smul_left,
        CalderonN.metricPair_smul_left, metricPair_positiveCoordinateNormal g (hg.2 q (mem_univ _)),
        hv, mul_zero, mul_zero, sub_zero] at hVariation
      exact ⟨(mul_left_cancel₀ (pow_ne_zero 2 ht₀)) (hSpeed.trans (mul_one _).symm),
        (mul_eq_zero.mp hVariation).resolve_left ht₀⟩
    exact ⟨(hProbe 0 (by simp)).1, fun v hv => (hProbe v hv).2⟩

end CalderonPatch

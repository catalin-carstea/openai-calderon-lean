module

public import Proof.CalderonN.ActualFiniteRadialEndpoints
public import Proof.CalderonN.FiniteRadialResponseLinear
public import Proof.CalderonN.FiniteSphereMidpoint

import Mathlib.Tactic

/-! Interpolation of the actual finite-harmonic radial Taylor remainder on
the common classical solution and boundary trace. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Matrix.Norms.Elementwise Topology Classical
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet TauCeti PDE

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

omit [Nontrivial (Fin dim)] in
theorem sphereSobolevInclusionL_smoothBoundarySobolev (hn : 3 ≤ dim) (s t : ℝ)
    (hs : s ≤ 2) (ht : t ≤ 2) (hts : t ≤ s) (u : SmoothData dim) :
    sphereSobolevInclusionL s t hts (smoothBoundarySobolev hn s hs u) =
      smoothBoundarySobolev hn t ht u := by
  apply lp.ext
  funext k
  rw [sphereSobolevInclusionL_apply,smoothBoundarySobolev_apply,smoothBoundarySobolev_apply,smul_smul]
  have h : besselWeight (t-s) k*besselWeight s k = besselWeight t k := by
    unfold besselWeight
    rw [← Real.rpow_add (by positivity : 0 < 1+(k : ℝ)),sub_add_cancel]
  rw [h]

omit [Nontrivial (Fin dim)] in
theorem smoothBoundarySobolev_order_eq (hn : 3 ≤ dim) {s t : ℝ}
    (h : s = t) (hs : s ≤ 2) (ht : t ≤ 2) (u : SmoothData dim) :
    smoothBoundarySobolev hn s hs u = (smoothBoundarySobolev hn t ht u : SphereSobolev dim s) := by
  subst t
  rfl

/-- The radial remainder for the actual normalized first metric has a
quadratic bound from (H^1) to (L^2) on the same finite datum. -/
theorem uniform_actual_finite_radial_midpoint (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ f : HarmonicFiniteCoefficients dim,
        let r := d.radius y
        let A (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
        let ell := firstDensityCenterLinear d y
        let u := harmonicFiniteSmooth f
        let q := harmonicFiniteDriftVariationSmooth ell f
        ∃ b E : SmoothData dim,
          EqOn b.1 u.1 (standardSphere dim) ∧
          EqOn (negativeBallDivergence A b.1) 0 (ball (0 : X dim) 1) ∧
          (∀ z, E.1 z = fderiv ℝ b.1 z z-fderiv ℝ u.1 z z-r*fderiv ℝ q.1 z z) ∧
          ‖smoothBoundarySobolev hn 0 (by norm_num) E‖ ≤ C*r^2*‖harmonicBoundaryFiniteL 1 f‖ := by
  obtain ⟨η,C0,C1,hη,hC0,hC1,hU⟩ := uniform_actual_finite_radial_endpoints (Y := Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,(C0+C1)/2,hη,by positivity,?_⟩
  intro floor hf ε hε hεη d hd y hy
  obtain ⟨a,ha,hA,⟨lo,hi,hEll⟩,hF⟩ := hU floor hf ε hε hεη d hd y hy
  choose b E hT hH hE h0 h1 using hF
  let r := d.radius y
  let ell := firstDensityCenterLinear d y
  have hHA (f : HarmonicFiniteCoefficients dim) :
      EqOn (negativeBallDivergence a (b f).1) 0 (ball (0 : X dim) 1) := by
    intro z hz
    have hG : a =ᶠ[𝓝 z] fun w => firstNormalVelocityCoefficient d y (r • frameVector d.frame y w) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw using hA hw
    rw [negativeBallDivergence_congr_germ hG EventuallyEq.rfl]
    exact hH f hz
  let P : HarmonicFiniteCoefficients dim →ₗ[ℝ] smoothBallDataSubmodule dim :=
    smoothBallRadialDataL.comp (harmonicFiniteSmoothL+r • harmonicFiniteDriftVariationSmoothL ell)
  let F (s : ℝ) (hs : s ≤ 2) :=
    finiteRadialResponseL hn s hs ha hEll b hT hHA-(smoothBoundarySobolevLinear hn s hs).comp P
  have hEF (s : ℝ) (hs : s ≤ 2) (f : HarmonicFiniteCoefficients dim) :
      F s hs f = smoothBoundarySobolev hn s hs (E f) := by
    let b' := smoothBallRadialDerivative (b f)
    let v : smoothBallDataSubmodule dim := ⟨b'.1,b'.2⟩
    have hv : smoothBoundarySobolev hn s hs b' = smoothBoundarySobolevLinear hn s hs v :=
      (smoothBoundarySobolevLinear_apply hn s hs v).symm
    simp only [F,LinearMap.sub_apply,LinearMap.comp_apply,finiteRadialResponseL_apply]
    rw [hv,← map_sub,smoothBoundarySobolevLinear_apply]
    apply smoothBoundarySobolev_eq_of_eqOn
    intro z _
    have hP : (P f).1 z = (fderiv ℝ (harmonicFiniteSmooth f).1 z) z +
        r*(fderiv ℝ (harmonicFiniteDriftVariationSmooth ell f).1 z) z := by
      simp only [P,LinearMap.comp_apply,LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul]
      change (smoothBallRadialDataL (harmonicFiniteSmoothL f)).1 z+
          r*(smoothBallRadialDataL (harmonicFiniteDriftVariationSmoothL ell f)).1 z = _
      rw [smoothBallRadialDataL_val,smoothBallRadialDataL_val,harmonicFiniteSmoothL_val,
        harmonicFiniteDriftVariationSmoothL_val]
    change fderiv ℝ (b f).1 z z-(P f).1 z = (E f).1 z
    rw [hP,hE f z]
    change _ - (_ + r * _) = _ - _ - r * _
    ring
  intro f
  refine ⟨b f,E f,hT f,hH f,hE f,?_⟩
  have h : ‖F 0 (by norm_num) f‖ ≤ ((C0*r^2+C1*r^2)/2)*‖harmonicBoundaryFiniteL 1 f‖ := by
    refine norm_finiteSphere_midpoint_le
      (F (-1/2 : ℝ) (by norm_num)) (F 0 (by norm_num)) (F (1/2 : ℝ) (by norm_num))
      ?_ ?_ (C0*r^2) (C1*r^2) (by positivity) (by positivity) ?_ ?_ f
    · intro g
      rw [hEF 0, hEF (-1/2 : ℝ)]
      exact sphereSobolevInclusionL_smoothBoundarySobolev hn 0 (-1/2 : ℝ) _ _ _ (E g)
    · intro g
      rw [hEF (1/2 : ℝ), hEF (-1/2 : ℝ)]
      exact sphereSobolevInclusionL_smoothBoundarySobolev hn (1/2 : ℝ) (-1/2 : ℝ) _ _ _ (E g)
    · intro g
      have hneg : (-1/2 : ℝ) = -(1/2 : ℝ) := by ring
      rw [hEF,smoothBoundarySobolev_order_eq hn hneg _ (by norm_num)]
      exact h0 g
    · intro g
      rw [hEF]
      exact h1 g
  rw [hEF] at h
  exact h.trans_eq (by change _ = (C0+C1)/2*r^2*‖harmonicBoundaryFiniteL 1 f‖; ring)

end CalderonN

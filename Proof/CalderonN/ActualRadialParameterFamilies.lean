module

public import Proof.CalderonN.LocalCenterBallCoefficientFamily
public import Proof.CalderonN.ActualRelativeRadiusRadialResponse
public import Proof.CalderonN.MatchedBallRadialFamily

import Mathlib.Tactic

/-! The quadratic radial remainders measure the derivatives of actual
center and relative-radius Dirichlet families on the same unit sphere. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN
open BallDirichlet

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_actual_center_radial_family (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 5 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y, ∀ a : X dim, ‖a‖ ≤ K →
      ∀ f : HarmonicFiniteCoefficients dim,
        let r := d.radius y
        let u := harmonicFiniteSmooth f
        let q := harmonicFiniteDriftVariationSmooth (centerDensityCovariantLinear d y a) f
        ∃ F : ℝ → I dim → X dim, (∀ i, ContDiff ℝ ∞ (fun t => F t i)) ∧ F 0 = d.frame y ∧
        ∃ W : Set ℝ, IsOpen W ∧ (0 : ℝ) ∈ W ∧
          (∀ t ∈ W, y+t • a ∈ Y ∧
            (∀ i, HasDerivAt (fun s => F s i) (-connection d.γ (y+t • a) a (F t i)) t) ∧
            ∀ i j, metricPair d.γ (y+t • a) (F t i) (F t j) = if i=j then 1 else 0) ∧
        ∃ b : ℝ × X dim → ℝ, ContDiff ℝ ∞ b ∧
          (∀ t ∈ W,
            EqOn (fun z => b (t,z)) u.1 (standardSphere dim) ∧
            EqOn (negativeBallDivergence (fun z => fixedRadiusTransportedCoefficient d y a F (t,z))
              (fun z => b (t,z))) 0 (ball (0 : X dim) 1)) ∧
        ∃ R : SmoothData dim,
          (∀ z ∈ standardSphere dim,
            HasDerivAt (fun t => fderiv ℝ (fun x => b (t,x)) z z)
              (r*fderiv ℝ q.1 z z+R.1 z) 0) ∧
          ‖smoothBoundarySobolev hn 0 (by norm_num) R‖ ≤ B*r^2*‖harmonicBoundaryFiniteL 1 f‖ := by
  obtain ⟨η,B,hη,hB,hResponse⟩ := uniform_actual_center_radial_response (Y:=Y) hn hY hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨min η (ρ/4),B,lt_min hη (by positivity),hB,?_⟩
  intro floor hf ε he hε d hd y hy a ha f
  dsimp only
  let r := d.radius y
  let u := harmonicFiniteSmooth f
  let q := harmonicFiniteDriftVariationSmooth (centerDensityCovariantLinear d y a) f
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hre : r ≤ ε := (le_mul_of_one_le_right hr.le
    (one_le_pow₀ (hf.trans (hd.2.2.2.2.1.2 y hy).2.1))).trans (hd.2.2.2.2.2 y hy).2
  have hrρ : 2*r < ρ := by
    have h := hre.trans (hε.trans (min_le_right _ _))
    linarith only [h,hρ]
  obtain ⟨F,hF,hF₀,V,hV,hV₀,hTransport,hSmooth,hPos,hSlice⟩ :=
    exists_local_actualCenter_coefficientFamily hY hΩ hd (zero_lt_one.trans_le hK) hy a hrρ
  obtain ⟨b,w,R,hbT,hwT,hbH,hwH,hEq,hNorm⟩ := hResponse floor hf ε he
    (hε.trans (min_le_left _ _)) d hd y hy a ha f
  let A := fixedRadiusTransportedCoefficient d y a F
  have hClosed : {(0 : ℝ)} ×ˢ closedBall (0 : X dim) 1 ⊆ V ×ˢ ball (0 : X dim) 2 := by
    rintro ⟨t,z⟩ ⟨ht,hz⟩
    exact ⟨(mem_singleton_iff.mp ht).symm ▸ hV₀,closedBall_subset_ball (by norm_num) hz⟩
  have hLess : ball (0 : X dim) 1 ⊆ ball (0 : X dim) 2 := ball_subset_ball (by norm_num)
  obtain ⟨W,hW,hW₀,C,hC,hCEq,hCD⟩ := exists_matched_ball_radial_family
    (hV.prod isOpen_ball) hClosed hSmooth hPos
    (fun z hz => (hSlice z (hLess hz)).1) (fun z hz => (hSlice z (hLess hz)).2)
    u b w hbT hwT hbH hwH
  refine ⟨F,hF,hF₀,W ∩ V,hW.inter hV,⟨hW₀,hV₀⟩,(fun t ht => hTransport t ht.2),
    C,hC,(fun t ht => hCEq t ht.1),R,?_,hNorm⟩
  intro z hz
  apply (hCD z hz).congr_deriv
  rw [hEq z]
  ring

theorem uniform_actual_relativeRadius_radial_family (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y, ∀ f : HarmonicFiniteCoefficients dim,
        let r := d.radius y
        let u := harmonicFiniteSmooth f
        let q := harmonicFiniteDriftVariationSmooth (firstDensityCenterLinear d y) f
        ∃ W : Set ℝ, IsOpen W ∧ (0 : ℝ) ∈ W ∧
        ∃ b : ℝ × X dim → ℝ, ContDiff ℝ ∞ b ∧
          (∀ t ∈ W,
            EqOn (fun z => b (t,z)) u.1 (standardSphere dim) ∧
            EqOn (negativeBallDivergence (relativeRadiusCoefficient d y t) (fun z => b (t,z))) 0
              (ball (0 : X dim) 1)) ∧
        ∃ R : SmoothData dim,
          (∀ z ∈ standardSphere dim,
            HasDerivAt (fun t => fderiv ℝ (fun x => b (t,x)) z z)
              (r*fderiv ℝ q.1 z z+R.1 z) 0) ∧
          ‖smoothBoundarySobolev hn 0 (by norm_num) R‖ ≤ B*r^2*‖harmonicBoundaryFiniteL 1 f‖ := by
  obtain ⟨η,B,hη,hB,hResponse⟩ := uniform_actual_relative_radius_radial_response (Y:=Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηP,_,hηP,_,hCoeff⟩ := uniform_normalized_coefficient_remainder_C2 (Y:=Y)
    (by omega : 2 ≤ dim) hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨min η ηP,B,lt_min hη hηP,hB,?_⟩
  intro floor hf ε he hε d hd y hy f
  dsimp only
  let r := d.radius y
  let u := harmonicFiniteSmooth f
  let q := harmonicFiniteDriftVariationSmooth (firstDensityCenterLinear d y) f
  let A (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
  let C (p : ℝ × X dim) := (1+p.1) • p.2
  let U := C ⁻¹' ball (0 : X dim) 2
  let a (p : ℝ × X dim) := relativeRadiusCoefficient d y p.1 p.2
  have hC : ContDiff ℝ ∞ C := (contDiff_const.add contDiff_fst).smul contDiff_snd
  have hU : IsOpen U := isOpen_ball.preimage hC.continuous
  have hEq : a = A ∘ C := by
    funext p
    change relativeRadiusCoefficient d y p.1 p.2 =
      firstNormalVelocityCoefficient d y (r • frameVector d.frame y ((1+p.1) • p.2))
    rw [← frameVectorLinear_apply,map_smul,smul_smul,frameVectorLinear_apply]
    rfl
  have hClosed : {(0 : ℝ)} ×ˢ closedBall (0 : X dim) 1 ⊆ U := by
    rintro ⟨t,z⟩ ⟨ht,hz⟩
    have ht₀ : t = 0 := mem_singleton_iff.mp ht
    change C (t,z) ∈ ball (0 : X dim) 2
    rw [ht₀,show C (0,z) = z from by simp [C]]
    exact closedBall_subset_ball (by norm_num) hz
  have hPack (z : X dim) (hz : z ∈ ball (0 : X dim) 2) :
      ContDiffAt ℝ ∞ A z ∧ (A z).PosDef := by
    have hh := hCoeff floor hf ε he (hε.trans (min_le_right _ _)) d hd y hy z (ball_subset_closedBall hz)
    let L (z : X dim) := (1+r*firstDensityCenterLinear d y z) • (1 : Mat dim)
    have hL : ContDiff ℝ ∞ L :=
      (contDiff_const.add (contDiff_const.mul (firstDensityCenterLinear d y).contDiff)).smul contDiff_const
    have he : A = normalizedFirstCoefficientRemainder d y + L := by
      funext z
      change A z = (A z-L z)+L z
      abel
    refine ⟨?_,hh.2.2.2.2⟩
    rw [he]
    exact hh.1.add hL.contDiffAt
  have ha : ContDiffOn ℝ ∞ a U := by
    intro p hp
    rw [hEq]
    exact ((hPack (C p) hp).1.comp p hC.contDiffAt).contDiffWithinAt
  have hPos (p : ℝ × X dim) (hp : p ∈ U) : (a p).PosDef := by rw [hEq]; exact (hPack (C p) hp).2
  obtain ⟨b,w,R,hbT,hwT,hbH,hwH,hR,hNorm⟩ := hResponse floor hf ε he
    (hε.trans (min_le_left _ _)) d hd y hy f
  have hA₀ (z : X dim) (_hz : z ∈ ball (0 : X dim) 1) : a (0,z) = A z := by
    rw [hEq]
    simp [C]
  have hG₀ (z : X dim) (hz : z ∈ ball (0 : X dim) 1) :
      HasDerivAt (fun t => a (t,z)) (actualRelativeRadiusCoefficientDerivative d y z) 0 := by
    have ht : DifferentiableAt ℝ (fun t => a (t,z)) 0 := by
      have hLoc : ContDiffAt ℝ ∞ a (0,z) :=
        ha.contDiffAt (hU.mem_nhds (hClosed ⟨mem_singleton _,ball_subset_closedBall hz⟩))
      exact (hLoc.comp 0 (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    exact ht.hasDerivAt
  obtain ⟨W,hW,hW₀,Cb,hCb,hCEq,hCD⟩ := exists_matched_ball_radial_family
    hU hClosed ha hPos hA₀ hG₀ u b w hbT hwT hbH hwH
  refine ⟨W,hW,hW₀,Cb,hCb,hCEq,R,?_,hNorm⟩
  intro z hz
  apply (hCD z hz).congr_deriv
  rw [hR z]
  ring

end CalderonN

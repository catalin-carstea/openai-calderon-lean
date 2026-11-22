module

public import Proof.CalderonN.MultiplierConormalBoundary
public import Proof.CalderonN.SharpRadialHalfBound
public import Proof.CalderonN.SmoothBoundaryMultiplier

import Mathlib.Tactic

/-! The four Gauss-weighted boundary terms give a quadratic
half-order multiplication commutator bound. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Gradient Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4100000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem norm_multiplier_conormal_half_bound (hn : 3 ≤ dim)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (W D R : SmoothData dim)
    (hW : ∀ u : SmoothData dim, EqOn (smoothBallConormal A u.1)
      (fun z => W.1 z*fderiv ℝ u.1 z z) (standardSphere dim))
    {ell : X dim →L[ℝ] ℝ} {f : SmoothData dim} (m : SmoothData dim)
    (U : ConormalTaylorSolutions A ell f)
    (V : ConormalTaylorSolutions A ell ⟨fun z => m.1 z*f.1 z,m.2.mul f.2⟩)
    (r C J C₀ C₁ C_e : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) (hJ : 0 ≤ J)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC_e : 0 ≤ C_e)
    (hD : EqOn D.1 (fun z => W.1 z-1) (standardSphere dim))
    (hR : EqOn R.1 (fun z => W.1 z-1-r*ell z) (standardSphere dim))
    (hJets : ∀ z ∈ ball (0 : X dim) 1,
      (|W.1 z| ≤ C ∧ ‖fderiv ℝ W.1 z‖ ≤ C) ∧
      (|D.1 z| ≤ C*r ∧ ‖fderiv ℝ D.1 z‖ ≤ C*r) ∧
      (|R.1 z| ≤ C*r^2 ∧ ‖fderiv ℝ R.1 z‖ ≤ C*r^2) ∧
      (|fderiv ℝ m.1 z z| ≤ J ∧ ‖fderiv ℝ (fun x => fderiv ℝ m.1 x x) z‖ ≤ J)) :
    let w := smoothMultiplierDefect m U.actual V.actual
    let w₀ := smoothMultiplierDefect m U.flat V.flat
    let w₁ := smoothMultiplierDefect m U.first V.first
    let e : SmoothData dim := ⟨w.1-w₀.1-r • w₁.1,(w.2.sub w₀.2).sub (w₁.2.const_smul r)⟩
    let H := ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) f‖
    let L := 2*Real.sqrt ((dim:ℝ)+3)
    let S := Real.sqrt ((((dim:ℝ)+3)*‖ballRadialDerivativeL dim‖^2)/(unitSphereArea dim))
    ‖smoothBallSobolev 2 w₀‖ ≤ C₀*H → ‖smoothBallSobolev 2 w₁‖ ≤ C₁*H →
    ‖smoothBallSobolev 2 e‖ ≤ C_e*r^2*H →
    ∃ Z : SmoothData dim,
      EqOn Z.1 (fun z => (V.remainder hA r).1 z-m.1 z*(U.remainder hA r).1 z) (standardSphere dim) ∧
      ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) Z‖ ≤
        (L*C*S*(C₀+C₁+C_e)+L^2*C*J)*r^2*H := by
  dsimp only
  intro hw₀ hw₁ he
  let w := smoothMultiplierDefect m U.actual V.actual
  let w₀ := smoothMultiplierDefect m U.flat V.flat
  let w₁ := smoothMultiplierDefect m U.first V.first
  let e : SmoothData dim := ⟨w.1-w₀.1-r • w₁.1,(w.2.sub w₀.2).sub (w₁.2.const_smul r)⟩
  let H := ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) f‖
  let L := 2*Real.sqrt ((dim:ℝ)+3)
  let S := Real.sqrt ((((dim:ℝ)+3)*‖ballRadialDerivativeL dim‖^2)/(unitSphereArea dim))
  let B := smoothBoundarySobolevLinear hn (1/2:ℝ) (by norm_num)
  let d (v : SmoothData dim) := (⟨v.1,v.2⟩ : smoothBallDataSubmodule dim)
  let M := smoothBallRadialDerivative m
  let A₁ := d (smoothDataMul W (smoothBallRadialDerivative e))
  let A₂ := d (smoothDataMul R (smoothBallRadialDerivative w₀))
  let A₃ := d (smoothDataMul D (smoothBallRadialDerivative w₁))
  let A₄ := d (smoothDataMul R (smoothDataMul M f))
  let Q := A₁+A₂+r • A₃+A₄
  let Z : SmoothData dim := ⟨Q.1,smoothBallData_contDiff Q⟩
  refine ⟨Z,?_,?_⟩
  · intro z hz
    have hh := conormalTaylor_multiplier_boundary hA W hW m U V r hz
    change (V.remainder hA r).1 z-m.1 z*(U.remainder hA r).1 z =
      W.1 z*fderiv ℝ e.1 z z+(W.1 z-1-r*ell z)*fderiv ℝ w₀.1 z z+
        r*(W.1 z-1)*fderiv ℝ w₁.1 z z+(W.1 z-1-r*ell z)*(f.1 z*fderiv ℝ m.1 z z) at hh
    change Z.1 z = (V.remainder hA r).1 z-m.1 z*(U.remainder hA r).1 z
    rw [hh]
    change W.1 z*fderiv ℝ e.1 z z+R.1 z*fderiv ℝ w₀.1 z z+
      r*(D.1 z*fderiv ℝ w₁.1 z z)+R.1 z*(fderiv ℝ m.1 z z*f.1 z) = _
    have hD' : D.1 z = W.1 z-1 := hD hz
    have hR' : R.1 z = W.1 z-1-r*ell z := hR hz
    rw [hD',hR']
    ring
  have hMul (a u : SmoothData dim) (C' : ℝ) (hC' : 0 ≤ C')
      (hJet : ∀ z ∈ ball (0 : X dim) 1, |a.1 z| ≤ C' ∧ ‖fderiv ℝ a.1 z‖ ≤ C') :
      ‖B (d (smoothDataMul a u))‖ ≤ L*C'*‖B (d u)‖ := by
    apply norm_smoothBoundarySobolev_mul_half_le hn a u hC'
    · exact fun z hz => (hJet z hz).1
    · intro z hz
      rw [gradient,LinearIsometryEquiv.norm_map]
      exact (hJet z hz).2
  have hTrace (u : SmoothData dim) : ‖B (d (smoothBallRadialDerivative u))‖ ≤ S*‖smoothBallSobolev 2 u‖ :=
    norm_smoothBallRadialDerivative_half_le hn u
  have h₁ : ‖B A₁‖ ≤ L*C*(S*(C_e*r^2*H)) :=
    (hMul W _ C hC (fun z hz => (hJets z hz).1)).trans (mul_le_mul_of_nonneg_left ((hTrace e).trans (mul_le_mul_of_nonneg_left he (by positivity)))
        (by positivity))
  have h₂ : ‖B A₂‖ ≤ L*(C*r^2)*(S*(C₀*H)) :=
    (hMul R _ (C*r^2) (by positivity) (fun z hz => (hJets z hz).2.2.1)).trans
      (mul_le_mul_of_nonneg_left ((hTrace w₀).trans (mul_le_mul_of_nonneg_left hw₀ (by positivity)))
        (by positivity))
  have h₃ : ‖B A₃‖ ≤ L*(C*r)*(S*(C₁*H)) :=
    (hMul D _ (C*r) (by positivity) (fun z hz => (hJets z hz).2.1)).trans
      (mul_le_mul_of_nonneg_left ((hTrace w₁).trans (mul_le_mul_of_nonneg_left hw₁ (by positivity)))
        (by positivity))
  have h₄ : ‖B A₄‖ ≤ L*(C*r^2)*(L*J*H) :=
    (hMul R _ (C*r^2) (by positivity) (fun z hz => (hJets z hz).2.2.1)).trans
      (mul_le_mul_of_nonneg_left (hMul M f J hJ (fun z hz => (hJets z hz).2.2.2)) (by positivity))
  change ‖B Q‖ ≤ _
  simp only [Q,map_add,map_smul]
  calc
    _ ≤ ‖B A₁‖+‖B A₂‖+r*‖B A₃‖+‖B A₄‖ := by
      rw [← norm_smul_of_nonneg hr]
      exact (norm_add_le _ _).trans (add_le_add_left
        ((norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)) _)
    _ ≤ L*C*(S*(C_e*r^2*H))+L*(C*r^2)*(S*(C₀*H))+r*(L*(C*r)*(S*(C₁*H)))+
        L*(C*r^2)*(L*J*H) :=
      add_le_add (add_le_add (add_le_add h₁ h₂) (mul_le_mul_of_nonneg_left h₃ hr)) h₄
    _ = _ := by ring

end CalderonN

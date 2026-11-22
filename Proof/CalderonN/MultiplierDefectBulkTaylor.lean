module

public import Proof.CalderonN.MultiplierDefectTaylorEquation
public import Proof.CalderonN.SmoothMultiplierForcing

import Mathlib.Tactic

/-! The zero-boundary multiplication defect has a strong quadratic
Taylor bound controlled by the weak bulk size of the original solution. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem norm_multiplier_defect_bulk_taylor {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (hSym : ∀ z ∈ ball (0 : X dim) 1, ∀ i j,A z i j = A z j i)
    {ell : X dim →L[ℝ] ℝ} {f : SmoothData dim}
    (m : SmoothData dim)
    (U : ConormalTaylorSolutions A ell f)
    (V : ConormalTaylorSolutions A ell ⟨fun z => m.1 z*f.1 z,m.2.mul f.2⟩)
    (r : ℝ) (hr : 0 ≤ r)
    (K₀ K_A jA j₀ j₁ jD jR a₁ aD aR q₁ qR : ℝ)
    (hK₀ : 0 ≤ K₀) (hK_A : 0 ≤ K_A)
    (hjA : 0 ≤ jA) (hj₀ : 0 ≤ j₀) (hj₁ : 0 ≤ j₁) (hjD : 0 ≤ jD) (hjR : 0 ≤ jR)
    (ha₁ : 0 ≤ a₁) (haD : 0 ≤ aD) (haR : 0 ≤ aR) (hq₁ : 0 ≤ q₁) (hqR : 0 ≤ qR) :
    let A₀ : X dim → Mat dim := fun _ => 1
    let A₁ : X dim → Mat dim := fun z => ell z • 1
    let D := A-A₀
    let R := D-r • A₁
    let hA₀ : ContDiff ℝ ∞ A₀ := contDiff_const
    let hA₁ : ContDiff ℝ ∞ A₁ := ell.contDiff.smul contDiff_const
    let hD : ContDiff ℝ ∞ D := hA.sub hA₀
    let hR : ContDiff ℝ ∞ R := hD.sub (hA₁.const_smul r)
    let C₀ := K₀*j₀
    let C₁ := K₀*(a₁*C₀+j₁+j₀*q₁)
    let C := K_A*(jA*qR+jR+jD*q₁+aR*C₀+aD*C₁)
    let w := smoothMultiplierDefect m U.actual V.actual
    let w₀ := smoothMultiplierDefect m U.flat V.flat
    let w₁ := smoothMultiplierDefect m U.first V.first
    let e : SmoothData dim := ⟨w.1-w₀.1-r • w₁.1,(w.2.sub w₀.2).sub (w₁.2.const_smul r)⟩
    let E : SmoothData dim := ⟨U.actual.1-U.flat.1-r • U.first.1,
      (U.actual.2.sub U.flat.2).sub (U.first.2.const_smul r)⟩
    (∀ v g : SmoothData dim, EqOn v.1 0 (standardSphere dim) →
      EqOn (negativeBallDivergence A₀ v.1) g.1 (ball (0 : X dim) 1) →
        ‖smoothBallSobolev 2 v‖ ≤ K₀*‖smoothBallSobolev 0 g‖) →
    (∀ v g : SmoothData dim, EqOn v.1 0 (standardSphere dim) →
      EqOn (negativeBallDivergence A v.1) g.1 (ball (0 : X dim) 1) →
        ‖smoothBallSobolev 2 v‖ ≤ K_A*‖smoothBallSobolev 0 g‖) →
    (∀ v, ‖smoothBallSobolev 0 (smoothMultiplierForcing hA m v)‖ ≤ jA*‖smoothSobolev v‖) →
    (∀ v, ‖smoothBallSobolev 0 (smoothMultiplierForcing hA₀ m v)‖ ≤ j₀*‖smoothSobolev v‖) →
    (∀ v, ‖smoothBallSobolev 0 (smoothMultiplierForcing hA₁ m v)‖ ≤ j₁*‖smoothSobolev v‖) →
    (∀ v, ‖smoothBallSobolev 0 (smoothMultiplierForcing hD m v)‖ ≤ jD*r*‖smoothSobolev v‖) →
    (∀ v, ‖smoothBallSobolev 0 (smoothMultiplierForcing hR m v)‖ ≤ jR*r^2*‖smoothSobolev v‖) →
    (∀ v, ‖smoothBallSobolev 0 (smoothDivergenceForcing hA₁ v)‖ ≤ a₁*‖smoothBallSobolev 2 v‖) →
    (∀ v, ‖smoothBallSobolev 0 (smoothDivergenceForcing hD v)‖ ≤ aD*r*‖smoothBallSobolev 2 v‖) →
    (∀ v, ‖smoothBallSobolev 0 (smoothDivergenceForcing hR v)‖ ≤ aR*r^2*‖smoothBallSobolev 2 v‖) →
    ‖smoothSobolev U.first‖ ≤ q₁*‖smoothSobolev U.flat‖ →
    ‖smoothSobolev E‖ ≤ qR*r^2*‖smoothSobolev U.flat‖ →
    ‖smoothBallSobolev 2 w₀‖ ≤ C₀*‖smoothSobolev U.flat‖ ∧
    ‖smoothBallSobolev 2 w₁‖ ≤ C₁*‖smoothSobolev U.flat‖ ∧
    ‖smoothBallSobolev 2 e‖ ≤ C*r^2*‖smoothSobolev U.flat‖ := by
  dsimp only
  intro inv₀ invA cutA cut₀ cut₁ cutD cutR div₁ divD divR hq hE
  let A₀ : X dim → Mat dim := fun _ => 1
  let A₁ : X dim → Mat dim := fun z => ell z • 1
  let D := A-A₀
  let R := D-r • A₁
  have hA₀ : ContDiff ℝ ∞ A₀ := contDiff_const
  have hA₁ : ContDiff ℝ ∞ A₁ := ell.contDiff.smul contDiff_const
  have hD : ContDiff ℝ ∞ D := hA.sub hA₀
  have hR : ContDiff ℝ ∞ R := hD.sub (hA₁.const_smul r)
  let C₀ := K₀*j₀
  let C₁ := K₀*(a₁*C₀+j₁+j₀*q₁)
  let C := K_A*(jA*qR+jR+jD*q₁+aR*C₀+aD*C₁)
  let w := smoothMultiplierDefect m U.actual V.actual
  let w₀ := smoothMultiplierDefect m U.flat V.flat
  let w₁ := smoothMultiplierDefect m U.first V.first
  let e : SmoothData dim := ⟨w.1-w₀.1-r • w₁.1,(w.2.sub w₀.2).sub (w₁.2.const_smul r)⟩
  let E : SmoothData dim := ⟨U.actual.1-U.flat.1-r • U.first.1,
    (U.actual.2.sub U.flat.2).sub (U.first.2.const_smul r)⟩
  let W := ‖smoothSobolev U.flat‖
  let L := smoothBallSobolevLinear dim 0
  let S (v : SmoothData dim) : smoothBallDataSubmodule dim := ⟨v.1,v.2⟩
  obtain ⟨_,hw₀T,hw₁T,_,hw₀H,hw₁H⟩ := conormalTaylorSolutions_multiplierDefects hA hSym m U V
  have h₀ : ‖smoothBallSobolev 2 w₀‖ ≤ C₀*W := by
    let p := S (smoothMultiplierForcing hA₀ m U.flat)
    let g : SmoothData dim := ⟨(-p).1,smoothBallData_contDiff (-p)⟩
    have hg : EqOn (negativeBallDivergence A₀ w₀.1) g.1 (ball (0 : X dim) 1) := hw₀H
    refine (inv₀ w₀ g hw₀T hg).trans ?_
    change K₀*‖L (-p)‖ ≤ _
    rw [map_neg,norm_neg]
    exact (mul_le_mul_of_nonneg_left (cut₀ U.flat) hK₀).trans_eq (by dsimp [C₀,W]; ring)
  have h₁ : ‖smoothBallSobolev 2 w₁‖ ≤ C₁*W := by
    let p := S (smoothDivergenceForcing hA₁ w₀)
    let q := S (smoothMultiplierForcing hA₁ m U.flat)
    let t := S (smoothMultiplierForcing hA₀ m U.first)
    let g : SmoothData dim := ⟨(-p-q-t).1,smoothBallData_contDiff (-p-q-t)⟩
    have hg : EqOn (negativeBallDivergence A₀ w₁.1) g.1 (ball (0 : X dim) 1) := hw₁H
    refine (inv₀ w₁ g hw₁T hg).trans ?_
    change K₀*‖L (-p-q-t)‖ ≤ _
    rw [map_sub,map_sub,map_neg]
    have hh : ‖-L p-L q-L t‖ ≤ (a₁*C₀+j₁+j₀*q₁)*W := by
      calc
        _ ≤ ‖L p‖+‖L q‖+‖L t‖ := by
          simpa only [norm_neg] using
            (norm_sub_le (-L p-L q) (L t)).trans (add_le_add_left (norm_sub_le (-L p) (L q)) _)
        _ ≤ a₁*(C₀*W)+j₁*W+j₀*(q₁*W) :=
          add_le_add (add_le_add ((div₁ w₀).trans (mul_le_mul_of_nonneg_left h₀ ha₁)) (cut₁ U.flat))
            ((cut₀ U.first).trans (mul_le_mul_of_nonneg_left hq hj₀))
        _ = _ := by ring
    exact (mul_le_mul_of_nonneg_left hh hK₀).trans_eq (by dsimp only [C₁]; ring)
  refine ⟨h₀,h₁,?_⟩
  obtain ⟨heT,heH⟩ := multiplier_defect_taylor_equation hA hSym m U V r
  let p := S (smoothMultiplierForcing hA m E)
  let q := S (smoothMultiplierForcing hR m U.flat)
  let t := S (smoothMultiplierForcing hD m U.first)
  let v := S (smoothDivergenceForcing hR w₀)
  let x := S (smoothDivergenceForcing hD w₁)
  let g' := -p-q-r • t-v-r • x
  let g : SmoothData dim := ⟨g'.1,smoothBallData_contDiff g'⟩
  have hg : EqOn (negativeBallDivergence A e.1) g.1 (ball (0 : X dim) 1) := heH
  refine (invA e g heT hg).trans ?_
  change K_A*‖L g'‖ ≤ _
  simp only [g',map_sub,map_neg,map_smul]
  suffices hh : ‖-L p-L q-r • L t-L v-r • L x‖ ≤
      (jA*qR+jR+jD*q₁+aR*C₀+aD*C₁)*r^2*W by
    exact (mul_le_mul_of_nonneg_left hh hK_A).trans_eq (by dsimp only [C,C₀,C₁,W]; ring)
  calc
    _ ≤ ‖L p‖+‖L q‖+r*‖L t‖+‖L v‖+r*‖L x‖ := by
      rw [← norm_neg (L p),← norm_smul_of_nonneg hr,← norm_smul_of_nonneg hr]
      refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
      refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
      refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
      exact norm_sub_le _ _
    _ ≤ jA*(qR*r^2*W)+jR*r^2*W+r*(jD*r*(q₁*W))+aR*r^2*(C₀*W)+r*(aD*r*(C₁*W)) := by
      exact add_le_add (add_le_add (add_le_add
        (add_le_add ((cutA E).trans (mul_le_mul_of_nonneg_left hE hjA)) (cutR U.flat))
        (mul_le_mul_of_nonneg_left ((cutD U.first).trans (mul_le_mul_of_nonneg_left hq (by positivity))) hr))
        ((divR w₀).trans (mul_le_mul_of_nonneg_left h₀ (by positivity))))
        (mul_le_mul_of_nonneg_left ((divD w₁).trans (mul_le_mul_of_nonneg_left h₁ (by positivity))) hr)
    _ = _ := by ring

end CalderonN

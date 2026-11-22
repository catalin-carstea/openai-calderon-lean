module

public import Proof.Manuscript.LowerGreen.BallGreenSecondIdentity
public import Proof.Manuscript.LowerGreen.GreenCutoffOperators

import Mathlib.Tactic

public section

noncomputable section

open Set Filter Metric MeasureTheory CalderonN CalderonN.BallDirichlet
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]

private theorem smoothBallFlux_eq_zero_of_germ
    (a : X n → Mat n) {f : X n → ℝ} {x : X n} (h : f =ᶠ[𝓝 x] fun _ => 0) :
    smoothBallFlux a f x = 0 := by
  ext i
  have hz : fderiv ℝ f x = 0 := h.fderiv_eq.trans (by simp)
  simp [smoothBallFlux_apply,coordDeriv,hz]

private theorem integrableOn_unitBall_mul_forcing
    {a : X n → Mat n} (ha : ContDiff ℝ ∞ a) (u v : SmoothData n) :
    IntegrableOn (fun x => v.1 x * negativeBallDivergence a u.1 x) (ball (0 : X n) 1) :=
  ((v.2.continuous.mul (contDiff_negativeBallDivergence ha u.2).continuous).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : X n) 1)).mono_set ball_subset_closedBall

private theorem integral_symmetric_forcing_of_cutoff
    {a : X n → Mat n} (ha : ContDiff ℝ ∞ a) (u v : SmoothData n)
    (hSym : ∀ x ∈ ball (0 : X n) 1, ∀ i j, a x i j = a x j i)
    (hSupp : tsupport u.1 ⊆ ball (0 : X n) (1/2)) :
    (∫ x in ball (0 : X n) 1, v.1 x * negativeBallDivergence a u.1 x) =
      ∫ x in ball (0 : X n) 1, u.1 x * negativeBallDivergence a v.1 x := by
  have hG := integral_sub_ballGreenFlux ha hSym u v
  have h0 : unitSphereFlux (fun x => u.1 x • smoothBallFlux a v.1 x -
      v.1 x • smoothBallFlux a u.1 x) = 0 := by
    unfold unitSphereFlux
    have hz (w : ↥(sphere (0 : X n) 1)) : (w : X n) ∉ tsupport u.1 := by
      intro hw
      have ht := mem_ball_zero_iff.mp (hSupp hw)
      rw [mem_sphere_zero_iff_norm.mp w.property] at ht
      norm_num at ht
    have he : (fun w : ↥(sphere (0 : X n) 1) => ⟪(w : X n),
        u.1 w • smoothBallFlux a v.1 w - v.1 w • smoothBallFlux a u.1 w⟫_ℝ) = 0 := by
      funext w
      have hw : u.1 =ᶠ[𝓝 (w : X n)] fun _ => 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (hz w)
      rw [smoothBallFlux_eq_zero_of_germ a hw,hw.eq_of_nhds]
      simp
    rw [he]
    exact integral_zero _ _
  rw [integral_sub (integrableOn_unitBall_mul_forcing ha u v)
    (integrableOn_unitBall_mul_forcing ha v u),h0] at hG
  exact sub_eq_zero.mp hG

/-- The cutoff commutator is skew for real L² pairings. Its support gives
the vanishing boundary terms in both uses of Green’s identity. -/
theorem integral_greenCutoffError_skew
    {a : X n → Mat n} (ha : ContDiff ℝ ∞ a)
    (hSym : ∀ x ∈ ball (0 : X n) 1, ∀ i j, a x i j = a x j i)
    (χ u v : SmoothData n) (hSupp : tsupport χ.1 ⊆ ball (0 : X n) (1/2)) :
    (∫ x in ball (0 : X n) 1, v.1 x * greenSourceCutoffError a χ.1 u.1 x) =
      -(∫ x in ball (0 : X n) 1, u.1 x * greenSourceCutoffError a χ.1 v.1 x) := by
  let U : SmoothData n := ⟨fun x => χ.1 x * u.1 x,χ.2.mul u.2⟩
  let V : SmoothData n := ⟨fun x => χ.1 x * v.1 x,χ.2.mul v.2⟩
  have hU : tsupport U.1 ⊆ ball (0 : X n) (1/2) :=
    fun _ hz => hSupp (tsupport_mul_subset_left hz)
  have hV : tsupport V.1 ⊆ ball (0 : X n) (1/2) :=
    fun _ hz => hSupp (tsupport_mul_subset_left hz)
  have hS₁ := integral_symmetric_forcing_of_cutoff ha U v hSym hU
  have hS₂ := integral_symmetric_forcing_of_cutoff ha V u hSym hV
  have hE (f g : SmoothData n) :
      (∫ x in ball (0 : X n) 1, g.1 x * greenSourceCutoffError a χ.1 f.1 x) =
        (∫ x in ball (0 : X n) 1, g.1 x * negativeBallDivergence a (fun z => χ.1 z * f.1 z) x) -
        (∫ x in ball (0 : X n) 1, (χ.1 x * g.1 x) * negativeBallDivergence a f.1 x) := by
    rw [← integral_sub (integrableOn_unitBall_mul_forcing ha ⟨_,χ.2.mul f.2⟩ g)
      (integrableOn_unitBall_mul_forcing ha f ⟨_,χ.2.mul g.2⟩)]
    apply setIntegral_congr_fun isOpen_ball.measurableSet
    intro x hx
    dsimp only
    rw [negativeBallDivergence_mul_eq_at_symm ha χ.2 f.2 x (hSym x hx)]
    ring
  rw [hE u v,hE v u]
  change _ - (∫ x in ball (0 : X n) 1, V.1 x * negativeBallDivergence a u.1 x) =
    -((∫ x in ball (0 : X n) 1, u.1 x * negativeBallDivergence a V.1 x) -
      (∫ x in ball (0 : X n) 1, U.1 x * negativeBallDivergence a v.1 x))
  rw [show (∫ x in ball (0 : X n) 1, v.1 x *
      negativeBallDivergence a (fun z => χ.1 z * u.1 z) x) =
        ∫ x in ball (0 : X n) 1, U.1 x * negativeBallDivergence a v.1 x from hS₁,hS₂]
  ring

end CalderonPaper.LowerGreen

end

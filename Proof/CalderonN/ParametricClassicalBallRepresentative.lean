module

public import Proof.CalderonN.ClosedBallJetSmooth
public import Proof.CalderonN.ClassicalBallDirichlet

import Mathlib.Tactic

/-! Adapted from `ParametricClassicalBallRepresentative` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace CalderonN

variable {dim : ℕ} [NeZero dim]


open CalderonN.BallDirichlet

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

set_option maxHeartbeats 1700000 in
/-- The all-order strong inverse has compatible classical representatives.
Their spatial jets depend jointly smoothly on the parameters and the
evaluation point, including the boundary. -/
theorem exists_parametric_classicalBallRepresentative
    {V : Set P} (hV : IsOpen V)
    {U : (s : ℕ) → P → (StrongDirichletSpace dim) s}
    (hU : ∀ s, ContDiffOn ℝ ∞ (U s) V)
    (hAgree : ∀ p ∈ V, ∀ s,
      (strongDirichletProjectionL dim) s (U s p) = (strongDirichletProjectionL dim) 0 (U 0 p)) :
    ∃ b : P → (X dim) → ℝ, (∀ p, ContDiff ℝ ∞ (b p)) ∧
      (∀ p ∈ V, TauCeti.W1p.value ((strongDirichletProjectionL dim) 0 (U 0 p) : (FixedBallH1 dim))
        =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)] b p) ∧
      ∀ k : ℕ, ContDiffOn ℝ ∞ (fun q : P × (X dim) => iteratedFDeriv ℝ k (b q.1) q.2)
        (V ×ˢ closedBall (0 : (X dim)) 1) := by
  classical
  choose b hb hbv using (fun p (hp : p ∈ V) =>
    exists_smooth_strongBallRepresentative (U := fun s => U s p) (hAgree p hp))
  let B (p : P) : (X dim) → ℝ := if hp : p ∈ V then b p hp else (fun _ => 0)
  have hB (p : P) : ContDiff ℝ ∞ (B p) := by
    by_cases hp : p ∈ V
    · simpa only [B,dite_eq_left hp] using hb p hp
    · have he : B p = (fun _ : (X dim) => (0:ℝ)) := by simp [B,hp]
      rw [he]
      exact contDiff_const
  have hBV (p : P) (hp : p ∈ V) :
      TauCeti.W1p.value ((strongDirichletProjectionL dim) 0 (U 0 p) : (FixedBallH1 dim))
        =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)] B p := by
    simpa only [B,dite_eq_left hp] using hbv p hp
  refine ⟨B,hB,hBV,fun k => contDiffOn_infty.mpr fun n => ?_⟩
  let s := k+n+dim+1
  let m := s+2
  let d (p : P) : (smoothBallDataSubmodule dim) := ⟨B p,hB p⟩
  let W (p : P) : (ClosedBallSobolev dim) m := (denseSmoothBallSobolev dim) m (d p)
  let A : (ClosedBallSobolev dim) m →ₗᵢ[ℝ] (BallSobolev dim) m := ((closedBallSobolev dim) m).toSubmodule.subtypeₗᵢ
  letI : CompleteSpace ((ClosedBallSobolev dim) m) := (completeSpace_closedBallSobolev dim) m
  let incl := ((strongDirichletSubmodule dim) s).toSubmodule.subtypeL
  have hAgreeB (p : P) (hp : p ∈ V) : (A ∘ W) p = incl (U s p) := by
    change smoothBallSobolev m ⟨B p,hB p⟩ = (U s p : (BallSobolev dim) m)
    apply TauCeti.Wkp.ext m
    apply Lp.ext
    refine (value_smoothBallSobolev_ae m ⟨B p,hB p⟩).trans ?_
    have hv := congrArg (fun v : (FixedBallH1Zero dim) => TauCeti.W1p.value (v : (FixedBallH1 dim))) (hAgree p hp s)
    change TauCeti.W1p.value ((strongDirichletProjectionL dim) s (U s p) : (FixedBallH1 dim)) = _ at hv
    rw [strongDirichletProjectionL_apply,TauCeti.Wkp.value_firstOrder] at hv
    change B p =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
      ⇑(TauCeti.Wkp.value (s+2) (U s p : (BallSobolev dim) (s+2)))
    rw [hv]
    exact (hBV p hp).symm
  have hAW : ContDiffOn ℝ ∞ (A ∘ W) V :=
    (incl.contDiff.comp_contDiffOn (hU s)).congr hAgreeB
  have hW : ContDiffOn ℝ ∞ W V :=
    contDiffOn_top_of_closedRangeLinearIsometry hV A W hAW
  have hnm : k+n+dim+3 ≤ m := by dsimp only [m,s]; omega
  have hJ := contDiffOn_closedBallEval_order m n k hnm
  let C := closedBall (0 : (X dim)) 1
  have hFst : MapsTo Prod.fst (V ×ˢ C) V := fun _ h => h.1
  have hSnd : MapsTo Prod.snd (V ×ˢ C) C := fun _ h => h.2
  have hWn : ContDiffOn ℝ n W V := hW.of_le (by simp)
  have hComp := (hJ.comp contDiff_snd.contDiffOn hSnd).clm_apply
    (hWn.comp contDiff_fst.contDiffOn hFst)
  apply hComp.congr
  intro q hq
  change iteratedFDeriv ℝ k (B q.1) q.2 = (closedBallEval dim) k m q.2 (W q.1)
  rw [show (closedBallEval dim) k m q.2 (W q.1) =
      (closedBallJetL dim) k m (W q.1) (⟨q.2,hq.2⟩:(UnitClosedBall dim)) from
    closedBallEval_apply k m (W q.1) ⟨q.2,hq.2⟩]
  rw [show W q.1 = (denseSmoothBallSobolev dim) m (d q.1) from rfl,closedBallJetL_on_smooth k m (by omega)]
  rfl

set_option maxHeartbeats 1600000 in
/-- The classical solutions of the zero-Dirichlet problem form a smooth
family of all spatial jets on the closed unit ball. -/
theorem exists_parametric_classical_zeroDirichlet [Nontrivial (Fin dim)]
    {V : Set P} (hV : IsOpen V)
    (a : P × (X dim) → (Mat dim)) (ha : ContDiff ℝ ∞ a)
    (Ka : Set (X dim)) (hKa : IsCompact Ka) (hSa : ∀ p z, z ∉ Ka → a (p,z) = 0)
    (f : P × (X dim) → ℝ) (hf : ContDiff ℝ ∞ f)
    (Kf : Set (X dim)) (hKf : IsCompact Kf) (hSf : ∀ p z, z ∉ Kf → f (p,z) = 0)
    (lo hi : P → ℝ)
    (hEll : ∀ p ∈ V, TauCeti.PDE.UniformlyEllipticOn ((fixedBallOpens dim) : Set (X dim))
      (fun z => a (p,z)) (lo p) (hi p)) :
    ∃ b : P → (X dim) → ℝ, (∀ p, ContDiff ℝ ∞ (b p)) ∧
      (∀ p ∈ V, EqOn (b p) 0 (standardSphere dim) ∧
        EqOn (negativeBallDivergence (fun z => a (p,z)) (b p)) (fun z => f (p,z)) (ball (0 : (X dim)) 1)) ∧
      ∀ k : ℕ, ContDiffOn ℝ ∞ (fun q : P × (X dim) => iteratedFDeriv ℝ k (b q.1) q.2)
        (V ×ˢ closedBall (0 : (X dim)) 1) := by
  obtain ⟨U,hU,hEig⟩ := exists_parametric_ballStrongSolution V a ha Ka hKa hSa f hf Kf hKf hSf lo hi hEll
  obtain ⟨b,hb,hVal,hJet⟩ := exists_parametric_classicalBallRepresentative hV hU
    (fun p hp s => (hEig p hp s).1)
  refine ⟨b,hb,fun p hp => ?_,hJet⟩
  let v := (strongDirichletProjectionL dim) 0 (U 0 p)
  have hA : ContDiff ℝ ∞ (fun z => a (p,z)) := ha.comp (contDiff_const.prodMk contDiff_id)
  have hF : ContDiff ℝ ∞ (fun z => f (p,z)) := hf.comp (contDiff_const.prodMk contDiff_id)
  exact ⟨eqOn_zero_sphere_of_ballH1Zero (hb p) v (hVal p hp),
    negativeBallDivergence_eq_of_ballWeakSolution hA hF (hb p) v (hVal p hp) _
      (ballForcingFamily_value 0 f hf Kf hKf hSf p) (hEig p hp 0).2.1⟩

end CalderonN

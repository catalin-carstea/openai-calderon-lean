module

public import Proof.CalderonN.BallRegularity.BoundedInverse
public import Proof.CalderonN.BallRegularity.StrongOperatorEnergy
public import Proof.CalderonN.BallRegularity.CoefficientMatrixRegularity

import Proof.CalderonN.BallRegularity.DirichletForcingInjectivity
import Mathlib.Analysis.Normed.Operator.Banach

/-! The elliptic inverse is the bounded bijection associated with the
released strong operator. Weak uniqueness identifies the solutions at
different Sobolev orders. -/

public section

noncomputable section
open MeasureTheory Metric TauCeti
open scoped ContDiff ENNReal Matrix.Norms.Elementwise

namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]

local instance : TopologicalSpace.PseudoMetrizableSpace (Mat dim) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (I dim → I dim → ℝ))

theorem existsUnique_fixedBall_weakSolution
    {a : X dim → Mat dim} (ha : Continuous a) {lo hi : ℝ}
    (he : PDE.UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) a lo hi)
    (f : Lp ℝ 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim))) :
    ∃! u : FixedBallH1Zero dim, PDE.IsWeakSolutionDirichlet a 0 0 f u := by
  cases dim with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k =>
    let b : X (k+1) → X (k+1) := 0
    let c : X (k+1) → ℝ := 0
    let μ := (volume : Measure (X (k+1))).restrict (fixedBallOpens (k+1))
    have hb : AEStronglyMeasurable b μ := aestronglyMeasurable_const
    have hc : AEStronglyMeasurable c μ := aestronglyMeasurable_const
    have hsmall : (0 : ℝ) * (2 * 1) < lo := by simpa using he.1
    have hB : (fixedBallOpens (k+1) : Set (X (k+1))) ⊆ ball 0 (1:ℝ) := Set.Subset.rfl
    exact he.existsUnique_isWeakSolutionDirichlet_of_subset_ball
      (b := b) (c := c) (beta := 0) (gamma := 0)
      ha.aestronglyMeasurable hb hc le_rfl (by simp [b]) (by simp [c]) (by simp [c])
      zero_le_one hB hsmall f

set_option maxHeartbeats 4400000 in
/-- The strong fixed-ball operator at an elliptic coefficient has a
bounded inverse from order s to the zero-trace space of order s + 2. -/
theorem strongDirichletOperator_isInvertible_of_elliptic
    (hcalc : FixedSobolevCalculus dim) (hreg : FixedDirichletRegularity dim)
    (s : ℕ) (F : SmoothCoefficientMatrix dim (s+2)) {lo hi : ℝ}
    (hEll : PDE.UniformlyEllipticOn (fixedBallOpens dim : Set (X dim))
      (coefficientMatrixField (s+2) F) lo hi) :
    (strongDirichletOperator hcalc s F).IsInvertible := by
  let L := strongDirichletOperator hcalc s F
  let ρ := strongDirichletProjectionL dim s
  let a := coefficientMatrixField (s+2) F
  have ha : ContDiff ℝ ∞ a := contDiff_coefficientMatrixField _ F
  have hcoeff : MemLp (fun x => PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) :=
    memLp_coefficientMatrixEnergyIntegrand _ F hEll
  have hEq (u : StrongDirichletSpace dim s) :
      PDE.IsWeakSolutionDirichlet a 0 0 (Wkp.value s (L u)) (ρ u) :=
    fun v => (strongCoefficientOperator_energy hcalc s F u v).symm
  have hinj : Function.Injective L := by
    intro u v h
    obtain ⟨w,hw,hu⟩ := existsUnique_fixedBall_weakSolution ha.continuous hEll (Wkp.value s (L v))
    have hU := hu (ρ u) (by simpa only [← h] using hEq u)
    have hV := hu (ρ v) (hEq v)
    exact strongDirichletProjectionL_injective s (hU.trans hV.symm)
  have hsurj : Function.Surjective L := by
    intro f
    obtain ⟨u,hu,_⟩ := existsUnique_fixedBall_weakSolution ha.continuous hEll (Wkp.value s f)
    have hU (v : FixedBallH1Zero dim) :
        PDE.energyFormH1L0 hcoeff u v = PDE.dirichletForcing (mu := (volume : Measure (X dim))) (Omega := fixedBallOpens dim)
          (Wkp.value (mu := (volume : Measure (X dim))) (Omega := fixedBallOpens dim) (p := 2) s f) v :=
      (PDE.energyFormH1L0_apply hcoeff _ _).trans (hu v)
    obtain ⟨C,hC,hLift⟩ := hreg s a lo hi ha.contDiffOn hEll hcoeff
    obtain ⟨U,hproj,_⟩ := hLift (f : BallSobolev dim s) u (fun v => hU v)
    let w : StrongDirichletSpace dim s := ⟨U, (mem_strongDirichletSubmodule s U).mpr (by rw [hproj]; exact u.2)⟩
    have hw : ρ w = u := by
      apply Subtype.ext
      exact (strongDirichletProjectionL_apply s w).trans hproj
    refine ⟨w,Wkp.ext s (unitBallDirichletForcing_eq_of_forall _ _ fun v => ?_)⟩
    rw [← hEq w v, hw]
    exact hu v
  let E : StrongDirichletSpace dim s ≃L[ℝ] BallSobolev dim s :=
    ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
  exact ⟨E, rfl⟩

end CalderonN.BallDirichlet

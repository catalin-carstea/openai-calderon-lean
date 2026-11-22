module

public import Proof.CalderonN.BallRegularity.Spaces
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.Density

/-! From Proof/Archive/DirichletForcingInjectivity.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section

set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]


theorem unitBallDirichletForcing_injective : Function.Injective
    (TauCeti.PDE.dirichletForcing (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim))) := by
  intro f g h
  have he : (fun z : Lp ℝ 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) => ⟪f, z⟫_ℝ) =
      (fun z => ⟪g, z⟫_ℝ) :=
    TauCeti.W1p0.denseRange_valueL_two.equalizer
      (innerSL ℝ f).continuous (innerSL ℝ g).continuous (by
        funext v
        have hv := congrArg (fun ell : StrongDual ℝ (FixedBallH1Zero dim) => ell v) h
        simpa only [Function.comp_apply, TauCeti.W1p0.valueL_apply,
          TauCeti.PDE.dirichletForcing_apply] using hv)
  have hz : ⟪f - g, f - g⟫_ℝ = 0 := by
    rw [inner_sub_left, congrFun he (f - g), sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

theorem unitBallDirichletForcing_eq_of_forall
    (f g : Lp ℝ 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim)))
    (h : ∀ v : (FixedBallH1Zero dim), TauCeti.PDE.dirichletForcing f v =
      TauCeti.PDE.dirichletForcing g v) : f = g :=
  unitBallDirichletForcing_injective (ContinuousLinearMap.ext h)

end CalderonN.BallDirichlet

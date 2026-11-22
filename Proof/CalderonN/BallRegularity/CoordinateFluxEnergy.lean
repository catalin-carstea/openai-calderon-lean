module

public import Proof.CalderonN.BallRegularity.CoordinateWeakIntegration

/-! From Proof/Archive/CoordinateFluxEnergy.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section

set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]


theorem energyFormH1_eq_sum_coordinateFlux_inner
    (a : (X dim) → Matrix (Fin dim) (Fin dim) ℝ) (u v : (FixedBallH1 dim))
    (q : Fin dim → Fin dim → Lp ℝ 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim)))
    (hq : ∀ i j, q i j =ᵐ[((volume : Measure (X dim)).restrict (fixedBallOpens dim))]
      fun x => a x i j * (TauCeti.W1p.gradient u x) j) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim)) a 0 0 u v =
      ∑ i : Fin dim, ∑ j : Fin dim, ⟪q i j, unitBallCoordinateGradientL i v⟫_ℝ := by
  let z := fun (i j : Fin dim) (x : (X dim)) => ⟪q i j x, unitBallCoordinateGradientL i v x⟫_ℝ
  have hi (i j : Fin dim) : Integrable (z i j)
      ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) :=
    L2.integrable_inner (𝕜 := ℝ) (q i j) (unitBallCoordinateGradientL i v)
  have hf : ∀ᵐ x ∂((volume : Measure (X dim)).restrict (fixedBallOpens dim)), ∀ i j : Fin dim,
      q i j x = a x i j * (TauCeti.W1p.gradient u x) j :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hq i j
  have hg : ∀ᵐ x ∂((volume : Measure (X dim)).restrict (fixedBallOpens dim)), ∀ i : Fin dim,
      unitBallCoordinateGradientL i v x = (TauCeti.W1p.gradient v x) i :=
    ae_all_iff.mpr fun i => unitBallCoordinateGradientL_ae i v
  have hs : (∫ x in (fixedBallOpens dim), ∑ i, ∑ j, z i j x) =
      ∑ i, ∑ j, ∫ x in (fixedBallOpens dim), z i j x := by
    rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
      (fun j _ => hi i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum Finset.univ (fun j _ => hi i j)
  calc
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim)) a 0 0 u v =
        ∫ x in (fixedBallOpens dim), ∑ i, ∑ j, z i j x := by
      rw [TauCeti.PDE.energyFormH1_def]
      apply integral_congr_ae
      filter_upwards [hf, hg] with x hx hy
      simp only [TauCeti.PDE.energyIntegrand_apply, TauCeti.PDE.jetField_apply,
        TauCeti.PDE.driftForm_apply, TauCeti.PDE.massForm_apply, Pi.zero_apply, inner_zero_left, zero_mul,
        add_zero, TauCeti.PDE.matrixBilinearForm_apply, Matrix.mulVec, dotProduct,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [z, RCLike.inner_apply, conj_trivial]
      rw [hx i j, hy i]
    _ = ∑ i, ∑ j, ∫ x in (fixedBallOpens dim), z i j x := hs
    _ = ∑ i, ∑ j, ⟪q i j, unitBallCoordinateGradientL i v⟫_ℝ := by
      simp only [L2.inner_def, z]

end CalderonN.BallDirichlet

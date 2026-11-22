module

public import Proof.CalderonN.WeakDirichletCorrection
public import Proof.CalderonN.FactoredPoissonJetBounds

import Mathlib.Tactic

/-! The weak energy restricted to zero-boundary tests is the same
canonical Banach operator used in the rectangular remainder estimate. -/

public section

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {H Z F : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

@[expose] def weakEnergyTestOperatorL (j : Z →L[ℝ] H) :
    (H →L[ℝ] H →L[ℝ] ℝ) →L[ℝ] (H →L[ℝ] Z →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ H (H →L[ℝ] ℝ) (Z →L[ℝ] ℝ))
    ((ContinuousLinearMap.compL ℝ Z H ℝ).flip j)

@[expose] def weakEnergyZeroOperatorL (j : Z →L[ℝ] H) :
    (H →L[ℝ] H →L[ℝ] ℝ) →L[ℝ] (Z →L[ℝ] Z →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ Z H (Z →L[ℝ] ℝ)).flip j).comp (weakEnergyTestOperatorL j)

theorem weakEnergyTestOperatorL_apply (j : Z →L[ℝ] H) (E : H →L[ℝ] H →L[ℝ] ℝ) (u : H) (v : Z) :
    weakEnergyTestOperatorL j E u v = E u (j v) := by
  simp only [weakEnergyTestOperatorL,ContinuousLinearMap.compL_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]

theorem weakEnergyZeroOperatorL_apply (j : Z →L[ℝ] H)
    (E : H →L[ℝ] H →L[ℝ] ℝ) (u v : Z) : weakEnergyZeroOperatorL j E u v = E (j u) (j v) := by
  simp only [weakEnergyZeroOperatorL,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply,weakEnergyTestOperatorL_apply]

private def weakEnergyZeroEquiv (j : Z →L[ℝ] H) (E : H →L[ℝ] H →L[ℝ] ℝ)
    (hE : IsCoercive (zeroDirichletEnergy j E)) : Z ≃L[ℝ] (Z →L[ℝ] ℝ) :=
  hE.continuousLinearEquivOfBilin.trans (InnerProductSpace.toDual ℝ Z).toContinuousLinearEquiv

private theorem weakEnergyZeroEquiv_coe (j : Z →L[ℝ] H) (E : H →L[ℝ] H →L[ℝ] ℝ)
    (hE : IsCoercive (zeroDirichletEnergy j E)) :
    (weakEnergyZeroEquiv j E hE : Z →L[ℝ] Z →L[ℝ] ℝ) = weakEnergyZeroOperatorL j E := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rw [weakEnergyZeroOperatorL_apply]
  change InnerProductSpace.toDual ℝ Z (hE.continuousLinearEquivOfBilin u) v = E (j u) (j v)
  rw [InnerProductSpace.toDual_apply_apply,hE.continuousLinearEquivOfBilin_apply,zeroDirichletEnergy_apply]

theorem weakEnergyZeroOperator_isInvertible (j : Z →L[ℝ] H) (E : H →L[ℝ] H →L[ℝ] ℝ)
    (hE : IsCoercive (zeroDirichletEnergy j E)) : (weakEnergyZeroOperatorL j E).IsInvertible :=
  ⟨weakEnergyZeroEquiv j E hE,weakEnergyZeroEquiv_coe j E hE⟩

@[expose] def weakEnergyPoissonOperatorL (j : Z →L[ℝ] H)
    (E : H →L[ℝ] H →L[ℝ] ℝ) (P₀ : F →L[ℝ] H) : F →L[ℝ] H :=
  P₀-j.comp ((weakEnergyZeroOperatorL j E).inverse.comp ((weakEnergyTestOperatorL j E).comp P₀))

theorem weakEnergyPoissonOperatorL_eq (j : Z →L[ℝ] H) (E : H →L[ℝ] H →L[ℝ] ℝ)
    (hE : IsCoercive (zeroDirichletEnergy j E)) (P₀ : F →L[ℝ] H) :
    weakEnergyPoissonOperatorL j E P₀ = weakDirichletPoissonL j E hE P₀ := by
  have hInv := weakEnergyZeroOperator_isInvertible j E hE
  apply ContinuousLinearMap.ext
  intro f
  apply eq_weakDirichletPoissonL_of_equation (j:=j) (E:=E)
  · refine ⟨-((weakEnergyZeroOperatorL j E).inverse ((weakEnergyTestOperatorL j E) (P₀ f))),?_⟩
    simp only [weakEnergyPoissonOperatorL,ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,map_neg]
    abel
  · intro v
    let w := (weakEnergyZeroOperatorL j E).inverse ((weakEnergyTestOperatorL j E) (P₀ f))
    have h := congrArg (fun l : Z →L[ℝ] ℝ => l v)
      (hInv.self_apply_inverse ((weakEnergyTestOperatorL j E) (P₀ f)))
    change weakEnergyZeroOperatorL j E w v = weakEnergyTestOperatorL j E (P₀ f) v at h
    rw [weakEnergyZeroOperatorL_apply,weakEnergyTestOperatorL_apply] at h
    change E (P₀ f-j w) (j v) = 0
    rw [map_sub,ContinuousLinearMap.sub_apply,h,sub_self]

end CalderonN

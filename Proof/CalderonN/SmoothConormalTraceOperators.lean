module

public import Proof.CalderonN.SmoothSphereTrace
public import Proof.CalderonN.SmoothConormalTaylorSolutions

import Mathlib.Tactic

/-! All three radial responses act linearly on the same sphere trace.
The actual conormal operator then has its exact affine expansion. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private def asSmoothData (u : smoothBallDataSubmodule dim) : SmoothData dim :=
  ⟨u.1,smoothBallData_contDiff u⟩

private def asSmoothSubmodule (u : SmoothData dim) : smoothBallDataSubmodule dim :=
  ⟨u.1,u.2⟩

private def addSmoothData (u v : SmoothData dim) : SmoothData dim := ⟨u.1+v.1,u.2.add v.2⟩
private def smulSmoothData (c : ℝ) (u : SmoothData dim) : SmoothData dim := ⟨c • u.1,u.2.const_smul c⟩

private def ConormalTaylorSolutions.add {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {ell : X dim →L[ℝ] ℝ} {u v : SmoothData dim}
    (U : ConormalTaylorSolutions A ell u) (V : ConormalTaylorSolutions A ell v) :
    ConormalTaylorSolutions A ell (addSmoothData u v) where
  actual := addSmoothData U.actual V.actual
  flat := addSmoothData U.flat V.flat
  first := addSmoothData U.first V.first
  actualTrace := by
    intro z hz
    exact congrArg₂ (· + ·) (U.actualTrace hz) (V.actualTrace hz)
  actualEquation := by
    intro z hz
    exact (negativeBallDivergence_add hA U.actual.2 V.actual.2 z).trans
      (by rw [U.actualEquation hz,V.actualEquation hz,Pi.zero_apply,add_zero])
  flatTrace := by
    intro z hz
    exact congrArg₂ (· + ·) (U.flatTrace hz) (V.flatTrace hz)
  flatEquation := by
    intro z hz
    refine (negativeBallDivergence_add contDiff_const U.flat.2 V.flat.2 z).trans ?_
    rw [U.flatEquation hz,V.flatEquation hz,Pi.zero_apply,add_zero]
  firstTrace := by
    intro z hz
    exact (congrArg₂ (· + ·) (U.firstTrace hz) (V.firstTrace hz)).trans (by simp)
  firstEquation := by
    intro z hz
    have hEll : ContDiff ℝ ∞ (fun z => ell z • (1 : Mat dim)) := ell.contDiff.smul contDiff_const
    change negativeBallDivergence (fun _ => (1 : Mat dim)) (U.first.1+V.first.1) z =
      -negativeBallDivergence (fun x => ell x • (1 : Mat dim)) (U.flat.1+V.flat.1) z
    rw [negativeBallDivergence_add contDiff_const U.first.2 V.first.2,
      negativeBallDivergence_add hEll U.flat.2 V.flat.2,U.firstEquation hz,V.firstEquation hz,neg_add]

private def ConormalTaylorSolutions.smul {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {ell : X dim →L[ℝ] ℝ} {u : SmoothData dim}
    (U : ConormalTaylorSolutions A ell u) (c : ℝ) :
    ConormalTaylorSolutions A ell (smulSmoothData c u) where
  actual := smulSmoothData c U.actual
  flat := smulSmoothData c U.flat
  first := smulSmoothData c U.first
  actualTrace := by
    intro z hz
    exact congrArg (c * ·) (U.actualTrace hz)
  actualEquation := by
    intro z hz
    exact (negativeBallDivergence_const_smul_solution hA U.actual c z).trans
      (by rw [U.actualEquation hz,Pi.zero_apply,mul_zero])
  flatTrace := by
    intro z hz
    exact congrArg (c * ·) (U.flatTrace hz)
  flatEquation := by
    intro z hz
    exact (negativeBallDivergence_const_smul_solution contDiff_const U.flat c z).trans
      (by rw [U.flatEquation hz,Pi.zero_apply,mul_zero])
  firstTrace := by
    intro z hz
    exact (congrArg (c * ·) (U.firstTrace hz)).trans (by simp)
  firstEquation := by
    intro z hz
    have hEll : ContDiff ℝ ∞ (fun z => ell z • (1 : Mat dim)) := ell.contDiff.smul contDiff_const
    change negativeBallDivergence (fun _ => (1 : Mat dim)) (c • U.first.1) z =
      -negativeBallDivergence (fun x => ell x • (1 : Mat dim)) (c • U.flat.1) z
    rw [negativeBallDivergence_const_smul_solution contDiff_const U.first,
      negativeBallDivergence_const_smul_solution hEll U.flat,U.firstEquation hz,mul_neg]

private def conormalSolutionRadialTraces {A : X dim → Mat dim} {ell : X dim →L[ℝ] ℝ}
    {f : SmoothData dim} (U : ConormalTaylorSolutions A ell f) :
    SmoothSphereTrace dim × SmoothSphereTrace dim × SmoothSphereTrace dim :=
  (smoothSphereTrace (smoothBallRadialDerivative U.actual),
   smoothSphereTrace (smoothBallRadialDerivative U.flat),
   smoothSphereTrace (smoothBallRadialDerivative U.first))

private theorem conormalSolutionRadialTraces_eq {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} {u v : SmoothData dim}
    (U : ConormalTaylorSolutions A ell u) (V : ConormalTaylorSolutions A ell v)
    (h : EqOn u.1 v.1 (standardSphere dim)) :
    conormalSolutionRadialTraces U = conormalSolutionRadialTraces V := by
  obtain ⟨hA',hB,hC⟩ := conormalTaylorSolutions_agree_of_trace hA hEll U V h
  exact Prod.ext ((smoothSphereTrace_eq_iff _ _).mpr (eqOn_radialDerivative_of_eqOn_closedUnitBall hA'))
    (Prod.ext ((smoothSphereTrace_eq_iff _ _).mpr (eqOn_radialDerivative_of_eqOn_closedUnitBall hB))
      ((smoothSphereTrace_eq_iff _ _).mpr (eqOn_radialDerivative_of_eqOn_closedUnitBall hC)))

/-- The actual, flat and first-variation radial traces, obtained by uniqueness
on the same smooth sphere data. -/
def smoothSphereTaylorResponses
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f) :
    SmoothSphereTrace dim →ₗ[ℝ] (SmoothSphereTrace dim × SmoothSphereTrace dim × SmoothSphereTrace dim) := by
  let L := (smoothSphereTraceL dim).comp (smoothBallRadialDataL (dim:=dim))
  let B : smoothBallDataSubmodule dim →ₗ[ℝ] (SmoothSphereTrace dim × SmoothSphereTrace dim × SmoothSphereTrace dim) :=
    { toFun := fun f => conormalSolutionRadialTraces (S (asSmoothData f))
      map_add' := by
        intro u v
        let U := S (asSmoothData u)
        let V := S (asSmoothData v)
        have h := conormalSolutionRadialTraces_eq hA hEll (S (asSmoothData (u+v))) (U.add hA V)
          (fun _ _ => rfl)
        change conormalSolutionRadialTraces (S (asSmoothData (u+v))) =
          conormalSolutionRadialTraces U+conormalSolutionRadialTraces V
        rw [h]
        change (L (asSmoothSubmodule U.actual+asSmoothSubmodule V.actual),
          L (asSmoothSubmodule U.flat+asSmoothSubmodule V.flat),
          L (asSmoothSubmodule U.first+asSmoothSubmodule V.first)) = _
        rw [map_add,map_add,map_add]
        rfl
      map_smul' := by
        intro c u
        let U := S (asSmoothData u)
        have h := conormalSolutionRadialTraces_eq hA hEll (S (asSmoothData (c • u))) (U.smul hA c)
          (fun _ _ => rfl)
        change conormalSolutionRadialTraces (S (asSmoothData (c • u))) = c • conormalSolutionRadialTraces U
        rw [h]
        change (L (c • asSmoothSubmodule U.actual),L (c • asSmoothSubmodule U.flat),
          L (c • asSmoothSubmodule U.first)) = _
        rw [map_smul,map_smul,map_smul]
        rfl }
  exact smoothSphereTraceLift B
    (fun u v h => conormalSolutionRadialTraces_eq hA hEll (S (asSmoothData u)) (S (asSmoothData v)) h)

theorem smoothSphereTaylorResponses_apply
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
    (f : SmoothData dim) :
    smoothSphereTaylorResponses hA hEll S (smoothSphereTrace f) =
      (smoothSphereTrace (smoothBallRadialDerivative (S f).actual),
       smoothSphereTrace (S f).degree,
       smoothSphereTrace (smoothBallRadialDerivative (S f).first)) := by
  unfold smoothSphereTaylorResponses smoothSphereTrace
  rw [smoothSphereTraceLift_apply]
  rfl

theorem smoothSphereTaylorResponse_remainder
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
    (W : SmoothData dim) (hW : ∀ u : SmoothData dim,
      EqOn (smoothBallConormal A u.1) (fun z => W.1 z*fderiv ℝ u.1 z z) (standardSphere dim))
    (r : ℝ) (f : SmoothData dim) :
    let p := smoothSphereTrace f
    let R := smoothSphereTaylorResponses hA hEll S p
    smoothSphereTrace ((S f).remainder hA r) =
      smoothSphereTraceMul W R.1 - R.2.1 -
        r • (smoothSphereTraceMul ⟨ell,ell.contDiff⟩ R.2.1+R.2.2) := by
  dsimp only
  rw [smoothSphereTaylorResponses_apply]
  apply Subtype.ext
  funext z
  change smoothBallConormal A (S f).actual.1 z-(S f).degree.1 z-
      r*((S f).affineConormal.1 z) =
    (smoothSphereTraceMul W (smoothSphereTrace (smoothBallRadialDerivative (S f).actual))).1 z-
      (S f).degree.1 z-
      r*((smoothSphereTraceMul ⟨ell,ell.contDiff⟩ (smoothSphereTrace (S f).degree)).1 z+
        fderiv ℝ (S f).first.1 z z)
  rw [smoothSphereTraceMul_apply,smoothSphereTraceMul_apply,smoothSphereTrace_apply,
    smoothSphereTrace_apply,hW (S f).actual z.2]
  rfl

end CalderonN

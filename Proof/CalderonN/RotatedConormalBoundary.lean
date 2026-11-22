module

public import Proof.CalderonN.AngularPoissonEquation
public import Proof.CalderonN.SmoothSphereTrace
public import Proof.CalderonN.MultiplierConormalBoundary
public import Proof.CalderonN.ActualRelativeRotatedWeakEnergy

import Mathlib.Tactic

/-! Rotating the conormal trace gives the radial trace of a zero-boundary
correction and the rotation of the radial Gauss weight. -/

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def smoothRotationData (i j : I dim) (u : SmoothData dim) : SmoothData dim :=
  ⟨sphereRotationDerivative i j u.1,contDiff_sphereRotationDerivative i j u.1 u.2⟩

theorem smoothRotationData_eqOn_sphere (i j : I dim) {u v : SmoothData dim}
    (h : EqOn u.1 v.1 (standardSphere dim)) :
    EqOn (smoothRotationData i j u).1 (smoothRotationData i j v).1 (standardSphere dim) := by
  have hEq := (smoothSphereTrace_eq_iff u v).mpr h
  apply (smoothSphereTrace_eq_iff _ _).mp
  exact (smoothSphereTraceRotation_apply i j u).symm.trans
    ((congrArg (smoothSphereTraceRotation i j) hEq).trans
      (smoothSphereTraceRotation_apply i j v))

theorem sphereRotationDerivative_mul_data (i j : I dim) (a b : SmoothData dim) (z : X dim) :
    sphereRotationDerivative i j (fun x => a.1 x*b.1 x) z =
      sphereRotationDerivative i j a.1 z*b.1 z+a.1 z*sphereRotationDerivative i j b.1 z := by
  unfold sphereRotationDerivative
  rw [fderiv_fun_mul (a.2.differentiable (by simp) z) (b.2.differentiable (by simp) z)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

theorem rotated_affine_solution_equation (i j : I dim)
    {A : X dim → Mat dim} {ell : X dim →L[ℝ] ℝ} {f : SmoothData dim}
    (U : ConormalTaylorSolutions A ell f) (V : ConormalTaylorSolutions A ell (smoothRotationData i j f)) :
    let p := angularBallCorrection i j U.first V.first
    let ell' := ell.comp (ballRotationGeneratorL i j)
    EqOn (angularBallCorrection i j U.flat V.flat).1 0 (closedBall (0:X dim) 1) ∧
    EqOn p.1 0 (standardSphere dim) ∧
    EqOn (negativeBallDivergence (fun _ => (1 : Mat dim)) p.1)
      (-negativeBallDivergence (fun z => ell' z • (1 : Mat dim)) U.flat.1)
      (ball (0:X dim) 1) := by
  dsimp only
  let A₀ : X dim → Mat dim := fun _ => 1
  let A₁ : X dim → Mat dim := fun z => ell z • 1
  let ell' := ell.comp (ballRotationGeneratorL i j)
  let L : X dim → Mat dim := fun z => ell' z • 1
  let F := smoothRotationData i j U.flat
  let w := angularBallCorrection i j U.flat V.flat
  have hA₀ : ContDiff ℝ ∞ A₀ := contDiff_const
  have hA₁ : ContDiff ℝ ∞ A₁ := ell.contDiff.smul contDiff_const
  have hA₀' : ballRotationCoefficient i j A₀ = 0 := by
    funext z
    simp [A₀,ballRotationCoefficient]
  have hFA : ballRotationCoefficient i j A₁ = L := by
    simpa only [A₁,L,ell',one_smul] using
      ballRotationCoefficient_scalarAffine i j ell 1
  have hZero (a : SmoothData dim) (z : X dim) :
      negativeBallDivergence (0 : X dim → Mat dim) a.1 z = 0 := by
    have h := negativeBallDivergence_const_smul_coefficient A₀ a.1 0 z
    simpa only [zero_smul,zero_mul] using h
  have hwT := angularBallCorrection_trace_zero i j U.flat V.flat f U.flatTrace V.flatTrace
  have hwEq (z : X dim) (hz : z ∈ ball (0:X dim) 1) :
      negativeBallDivergence A₀ w.1 z = 0 := by
    have h := negativeBallDivergence_angularBallCorrection i j hA₀ U.flat V.flat
      U.flatEquation V.flatEquation hz
    rw [hA₀'] at h
    simpa only [hZero,neg_zero,Pi.neg_apply] using h
  have hEll := uniformlyEllipticOn_const_one_one (n:=Fin dim) (fixedBallOpens dim : Set (X dim))
  let zeroData : SmoothData dim := ⟨0,contDiff_const⟩
  have hw : EqOn w.1 0 (closedBall (0:X dim) 1) :=
    eqOn_closedUnitBall_of_equal_ball_forcing hA₀ hEll (fun _ _ => rfl) w zeroData
      (fun z hz => (hwEq z hz).trans (by
        have h := negativeBallDivergence_const_smul_solution hA₀ U.flat 0 z
        simpa only [zero_smul,zero_mul,zeroData] using h.symm)) hwT
  refine ⟨hw,?_,?_⟩
  · exact angularBallCorrection_trace_zero i j U.first V.first zeroData U.firstTrace
      (fun z hz => (V.firstTrace hz).trans (by simp [sphereRotationDerivative,zeroData]))
  · intro z hz
    let p := smoothRotationData i j U.first
    have hLHS := sphereRotationDerivative_negativeBallDivergence i j hA₀ U.first z
    have hRHS := sphereRotationDerivative_negativeBallDivergence i j hA₁ U.flat z
    change _ = negativeBallDivergence A₀ p.1 z+negativeBallDivergence (ballRotationCoefficient i j A₀)
      U.first.1 z at hLHS
    change _ = negativeBallDivergence A₁ F.1 z+negativeBallDivergence (ballRotationCoefficient i j A₁)
      U.flat.1 z at hRHS
    have hLoc : negativeBallDivergence A₀ U.first.1 =ᶠ[𝓝 z] -negativeBallDivergence A₁ U.flat.1 := by
      filter_upwards [isOpen_ball.mem_nhds hz] with x hx using U.firstEquation hx
    have hNeg : sphereRotationDerivative i j (negativeBallDivergence A₀ U.first.1) z =
        -sphereRotationDerivative i j (negativeBallDivergence A₁ U.flat.1) z := by
      unfold sphereRotationDerivative
      rw [hLoc.fderiv_eq,fderiv_neg,neg_apply]
    have hLocF : F.1 =ᶠ[𝓝 z] V.flat.1 := by
      filter_upwards [isOpen_ball.mem_nhds hz] with x hx
      exact sub_eq_zero.mp (hw (ball_subset_closedBall hx))
    rw [hA₀',hNeg,hRHS,hFA,negativeBallDivergence_congr_germ EventuallyEq.rfl hLocF] at hLHS
    have hV := V.firstEquation hz
    change negativeBallDivergence A₀ V.first.1 z = -negativeBallDivergence A₁ V.flat.1 z at hV
    change negativeBallDivergence A₀ (p.1-V.first.1) z = -negativeBallDivergence L U.flat.1 z
    rw [negativeBallDivergence_sub_solution hA₀ p V.first,hV]
    rw [hZero,add_zero] at hLHS
    linarith only [hLHS]

theorem rotated_conormal_remainder_boundary (i j : I dim)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) (W : SmoothData dim)
    (hW : ∀ v : SmoothData dim, EqOn (smoothBallConormal A v.1)
      (fun z => W.1 z*fderiv ℝ v.1 z z) (standardSphere dim))
    {ell : X dim →L[ℝ] ℝ} {f : SmoothData dim}
    (U : ConormalTaylorSolutions A ell f) (V : ConormalTaylorSolutions A ell (smoothRotationData i j f))
    (r : ℝ) :
    let p := angularBallCorrection i j U.actual V.actual
    let q := angularBallCorrection i j U.first V.first
    let W' := smoothRotationData i j W
    let ell' := ell.comp (ballRotationGeneratorL i j)
    EqOn (fun z => sphereRotationDerivative i j (U.remainder hA r).1 z-(V.remainder hA r).1 z)
      (fun z => W.1 z*fderiv ℝ p.1 z z+W'.1 z*fderiv ℝ U.actual.1 z z-
        r*(ell' z*fderiv ℝ U.flat.1 z z+fderiv ℝ q.1 z z)) (standardSphere dim) := by
  dsimp only
  let c : SmoothData dim := ⟨_,contDiff_smoothBallConormal hA U.actual⟩
  let v := smoothBallRadialDerivative U.actual
  have hc : EqOn c.1 (smoothDataMul W v).1 (standardSphere dim) := hW U.actual
  have hD := smoothRotationData_eqOn_sphere i j hc
  have hf := (rotated_affine_solution_equation i j U V).1
  have hzD : EqOn (fun z => fderiv ℝ (angularBallCorrection i j U.flat V.flat).1 z z)
      (fun _ => 0) (standardSphere dim) := by
    intro z hz
    simpa only [fderiv_zero,Pi.zero_apply,zero_apply] using
      eqOn_radialDerivative_of_eqOn_closedUnitBall
        (u:=angularBallCorrection i j U.flat V.flat) (v:=⟨0,contDiff_const⟩) hf hz
  intro z hz
  have hv := hD hz
  change sphereRotationDerivative i j (smoothBallConormal A U.actual.1) z =
      sphereRotationDerivative i j (fun x => W.1 x*v.1 x) z at hv
  rw [sphereRotationDerivative_mul_data i j W v z] at hv
  let E : SmoothData dim := ⟨ell,ell.contDiff⟩
  let F := U.degree
  let Q := smoothBallRadialDerivative U.first
  have hDeriv := sphereRotationDerivative_mul_data i j E F z
  have hFlat := angularBallCorrection_radialDerivative i j U.flat V.flat z
  have hFirst := angularBallCorrection_radialDerivative i j U.first V.first z
  have hActual := angularBallCorrection_radialDerivative i j U.actual V.actual z
  have hDeg : sphereRotationDerivative i j F.1 z = fderiv ℝ V.flat.1 z z := by
    change sphereRotationDerivative i j (fun x => fderiv ℝ U.flat.1 x x) z = _
    linarith only [hFlat,hzD hz]
  change sphereRotationDerivative i j
      (c.1-F.1-r • ((smoothDataMul E F).1+Q.1)) z -
      (smoothBallConormal A V.actual.1 z-fderiv ℝ V.flat.1 z z -
        r*(ell z*fderiv ℝ V.flat.1 z z+fderiv ℝ V.first.1 z z)) = _
  let t := (smoothDataMul E F).2.add Q.2
  have h₁ := fderiv_sub ((c.2.sub F.2).differentiable (by simp) z)
    ((t.const_smul r).differentiable (by simp) z)
  have h₂ := fderiv_sub (c.2.differentiable (by simp) z) (F.2.differentiable (by simp) z)
  have h₃ := fderiv_const_smul (t.differentiable (by simp) z) r
  have h₄ := fderiv_add ((smoothDataMul E F).2.differentiable (by simp) z) (Q.2.differentiable (by simp) z)
  change fderiv ℝ (c.1-F.1-r • ((smoothDataMul E F).1+Q.1)) z = _ at h₁
  change fderiv ℝ (fun x => c.1 x-F.1 x) z = _ at h₂
  change fderiv ℝ (fun x => r • ((smoothDataMul E F).1 x+Q.1 x)) z = _ at h₃
  change fderiv ℝ (fun x => (smoothDataMul E F).1 x+Q.1 x) z = _ at h₄
  unfold sphereRotationDerivative at hDeriv hv hDeg ⊢
  rw [h₁,h₂,h₃,h₄]
  simp only [sub_apply,add_apply,smul_apply,smul_eq_mul]
  change fderiv ℝ (smoothDataMul E F).1 z (rotationVector i j z) = _ at hDeriv
  change fderiv ℝ c.1 z (rotationVector i j z) = _ at hv
  rw [hDeriv,hDeg,hv,hW V.actual hz,angularBallCorrection_radialDerivative,
    angularBallCorrection_radialDerivative]
  change _ = W.1 z*(sphereRotationDerivative i j v.1 z-fderiv ℝ V.actual.1 z z)+_ -
    r*((ell.comp (ballRotationGeneratorL i j)) z*fderiv ℝ U.flat.1 z z+_)
  have he : fderiv ℝ E.1 z (rotationVector i j z) = (ell.comp (ballRotationGeneratorL i j)) z := by
    change fderiv ℝ ell z _ = _
    rw [ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply,ballRotationGeneratorL_apply]
  rw [he]
  simp only [E,F,Q,v,smoothRotationData,ConormalTaylorSolutions.degree,
    smoothBallRadialDerivative,sphereRotationDerivative]
  ring

end CalderonN

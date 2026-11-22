module

public import Proof.CalderonN.ParametricBallConormal
public import Proof.CalderonN.ClosedBallJetEvaluation

import Proof.CalderonN.BallRegularity.StrongDerivativeValues
import Proof.CalderonN.EllipticCalculus
import Proof.CalderonN.GreenSourceCutoff
import Mathlib.Tactic

/-! Adapted from `BallPoissonOperator` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
open CalderonN.BallDirichlet

/-- The divergence operator on the full fixed-ball Sobolev space,
including functions with nonzero boundary values. -/
@[expose] def fullBallDivergenceL (s : ℕ) (a : (SmoothCoefficientMatrix dim) (s+2)) :
    (BallSobolev dim) (s+2) →L[ℝ] (BallSobolev dim) s :=
  coefficientDivergenceL (unitBallCoordinateDerivativeL fixedSobolevCalculus s)
    (unitBallCoordinateDerivativeL fixedSobolevCalculus (s+1))
    (coefficientMatrixMultiplierL fixedSobolevCalculus s a)

@[expose] def smoothDataCoordDeriv (i : (I dim)) (f : (SmoothData dim)) : (SmoothData dim) :=
  ⟨coordDeriv i f.1, (f.2.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const⟩

theorem unitBallCoordinateDerivativeL_smooth (s : ℕ) (i : (I dim)) (f : (SmoothData dim)) :
    unitBallCoordinateDerivativeL fixedSobolevCalculus s i (smoothBallSobolev (s+1) f) =
      smoothBallSobolev s (smoothDataCoordDeriv i f) := by
  apply TauCeti.Wkp.ext s
  apply Lp.ext
  have h := unitBallCoordinateDerivativeL_value_ae fixedSobolevCalculus s i (smoothBallSobolev (s+1) f)
  rw [firstOrder_smoothBallSobolev] at h
  exact h.trans (by
    filter_upwards [gradient_smoothSobolev_ae f,value_smoothBallSobolev_ae s (smoothDataCoordDeriv i f)]
      with x hx hy
    change (TauCeti.W1p.gradient (smoothSobolev f) x) i = _
    rw [hx,hy]
    exact gradient_apply_coord x i)

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem contDiff_fullBallDivergence_family (s : ℕ)
    (a : P × (X dim) → (Mat dim)) (ha : ContDiff ℝ ∞ a)
    (K : Set (X dim)) (hK : IsCompact K) (hSupp : ∀ p z, z ∉ K → a (p,z) = 0) :
    ContDiff ℝ ∞ (fun p => fullBallDivergenceL s
      (commonSupportMatrixFamily (s+2) a ha K hK hSupp p)) := by
  have h (i j : (I dim)) : ContDiff ℝ ∞ (fun p => coefficientMatrixMultiplierL fixedSobolevCalculus s
      (commonSupportMatrixFamily (s+2) a ha K hK hSupp p) i j) := by
    simp only [coefficientMatrixMultiplierL_apply]
    exact contDiff_commonSupport_actual_coefficientMultiplier fixedSobolevCalculus (s+1)
      (fun q => a q i j) (contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
      (fun p z hz => by rw [hSupp p z hz]; rfl)
  exact (coefficientDivergenceL (unitBallCoordinateDerivativeL fixedSobolevCalculus s)
    (unitBallCoordinateDerivativeL fixedSobolevCalculus (s+1))).contDiff.comp
    (contDiff_pi.mpr (fun i => contDiff_pi.mpr (h i)))

omit [FiniteDimensional ℝ P] in
private theorem coefficientMultiplier_commonSupport_smooth
    (s : ℕ) (a : P × (X dim) → (Mat dim)) (ha : ContDiff ℝ ∞ a)
    (K : Set (X dim)) (hK : IsCompact K) (hSupp : ∀ p z, z ∉ K → a (p,z) = 0)
    (p : P) (i j : (I dim)) (f : (SmoothData dim)) :
    let F := commonSupportMatrixFamily (s+1) a ha K hK hSupp p
    let hf : ContDiff ℝ ∞ (fun x => a (p,x) i j * f.1 x) :=
      ((contDiff_pi.mp (contDiff_pi.mp ha i) j).comp (contDiff_const.prodMk contDiff_id)).mul f.2
    coefficientMultiplier fixedSobolevCalculus s (F i j) (smoothBallSobolev s f) =
      smoothBallSobolev s ⟨fun x => a (p,x) i j * f.1 x,hf⟩ := by
  dsimp only
  apply TauCeti.Wkp.ext s
  apply Lp.ext
  let A := commonSupportMatrixFamily (s+1) a ha K hK hSupp p
  have he : coefficientMatrixField (s+1) A = fun z => a (p,z) :=
    coefficientMatrixField_commonSupportMatrixFamily _ a ha K hK hSupp p
  refine (coefficientMultiplier_value_ae fixedSobolevCalculus s (A i j) (smoothBallSobolev s f)).trans ?_
  filter_upwards [value_smoothBallSobolev_ae s f,
    value_smoothBallSobolev_ae s (⟨fun x => a (p,x) i j * f.1 x,_⟩ : (SmoothData dim))] with x hx hy
  rw [hx,hy]
  have h := congrArg (fun M : (X dim) → (Mat dim) => M x i j) he
  change coefficientValue (s+1) (A i j) x = a (p,x) i j at h
  rw [h]

set_option maxHeartbeats 1800000 in
omit [FiniteDimensional ℝ P] in
theorem fullBallDivergence_family_smooth (s : ℕ)
    (a : P × (X dim) → (Mat dim)) (ha : ContDiff ℝ ∞ a)
    (K : Set (X dim)) (hK : IsCompact K) (hSupp : ∀ p z, z ∉ K → a (p,z) = 0)
    (p : P) (f : (SmoothData dim)) :
    let A := commonSupportMatrixFamily (s+2) a ha K hK hSupp p
    let D (x : (X dim)) := negativeBallDivergence (fun z => a (p,z)) f.1 x
    let hD : ContDiff ℝ ∞ D :=
      contDiff_negativeBallDivergence (ha.comp (contDiff_const.prodMk contDiff_id)) f.2
    fullBallDivergenceL s A (smoothBallSobolev (s+2) f) = smoothBallSobolev s ⟨D,hD⟩ := by
  let A := commonSupportMatrixFamily (s+2) a ha K hK hSupp p
  let b (i j : (I dim)) : (smoothBallDataSubmodule dim) :=
    ⟨fun x => a (p,x) i j * coordDeriv j f.1 x,
      ((contDiff_pi.mp (contDiff_pi.mp ha i) j).comp (contDiff_const.prodMk contDiff_id)).mul
        (smoothDataCoordDeriv j f).2⟩
  let d (i j : (I dim)) : (smoothBallDataSubmodule dim) :=
    ⟨coordDeriv i ((b i j : (smoothBallDataSubmodule dim)) : (X dim) → ℝ),
      (smoothDataCoordDeriv i ⟨b i j,(smoothBallData_contDiff (b i j))⟩).2⟩
  have hElem (i j : (I dim)) :
      unitBallCoordinateDerivativeL fixedSobolevCalculus s i
        (coefficientMatrixMultiplierL fixedSobolevCalculus s A i j
          (unitBallCoordinateDerivativeL fixedSobolevCalculus (s+1) j (smoothBallSobolev (s+2) f))) =
        (smoothBallSobolevLinear dim) s (d i j) := by
    rw [unitBallCoordinateDerivativeL_smooth,coefficientMatrixMultiplierL_apply]
    have he := coefficientMultiplier_commonSupport_smooth (s+1) a ha K hK hSupp p i j (smoothDataCoordDeriv j f)
    change coefficientMultiplier fixedSobolevCalculus (s+1) (A i j)
      (smoothBallSobolev (s+1) (smoothDataCoordDeriv j f)) =
      smoothBallSobolev (s+1) ⟨b i j,(smoothBallData_contDiff (b i j))⟩ at he
    rw [he,unitBallCoordinateDerivativeL_smooth]
    rfl
  dsimp only
  change fullBallDivergenceL s A (smoothBallSobolev (s+2) f) = _
  rw [fullBallDivergenceL,coefficientDivergenceL_apply_apply]
  simp_rw [hElem,← map_sum,← map_neg]
  apply TauCeti.Wkp.ext s
  apply Lp.ext
  refine (value_smoothBallSobolev_ae _ _).trans ?_
  refine EventuallyEq.trans ?_ (value_smoothBallSobolev_ae _ _).symm
  apply Eventually.of_forall
  intro x
  change (↑(-(∑ i, ∑ j, d i j)) : X dim → ℝ) x =
    negativeBallDivergence (fun z => a (p,z)) f.1 x
  rw [show (↑(-(∑ i, ∑ j, d i j)) : X dim → ℝ) x = -(∑ i, ∑ j, (d i j : X dim → ℝ) x) from by
    change (smoothBallDataSubmodule dim).subtype (-(∑ i, ∑ j, d i j)) x = _
    simp only [map_neg,map_sum,Pi.neg_apply,Finset.sum_apply,Submodule.subtype_apply]]
  change (-(∑ i, ∑ j, coordDeriv i (fun z => a (p,z) i j * coordDeriv j f.1 z) x)) = _
  unfold negativeBallDivergence Elliptic.Lop
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (Elliptic.pd_sum (fun j => (smoothBallData_contDiff (b i j))) x).symm

/-- The projection that sends any Sobolev lift of the boundary datum
to its harmonic replacement. -/
@[expose] def ballPoissonOperatorL (s : ℕ) (A : (SmoothCoefficientMatrix dim) (s+2)) :
    (BallSobolev dim) (s+2) →L[ℝ] (BallSobolev dim) (s+2) :=
  ContinuousLinearMap.id ℝ _ -
    (((strongDirichletSubmodule dim) s).toSubmodule.subtypeL.comp
      (strongDirichletOperator fixedSobolevCalculus s A).inverse).comp (fullBallDivergenceL s A)

theorem contDiffOn_ballPoissonOperator_family (s : ℕ)
    (a : P × (X dim) → (Mat dim)) (ha : ContDiff ℝ ∞ a)
    (K : Set (X dim)) (hK : IsCompact K) (hSupp : ∀ p z, z ∉ K → a (p,z) = 0)
    (V : Set P) (lo hi : P → ℝ)
    (hEll : ∀ p ∈ V, TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens dim : Set (X dim))
      (fun z => a (p,z)) (lo p) (hi p)) :
    ContDiffOn ℝ ∞ (fun p => ballPoissonOperatorL s
      (commonSupportMatrixFamily (s+2) a ha K hK hSupp p)) V := by
  have hI := contDiffOn_commonSupport_actual_strongDirichletInverse fixedSobolevCalculus
    fixedDirichletRegularity s a ha K hK hSupp V lo hi hEll
  exact contDiffOn_const.sub ((contDiffOn_const.clm_comp hI).clm_comp
    (contDiff_fullBallDivergence_family s a ha K hK hSupp).contDiffOn)

set_option maxHeartbeats 2300000 in
/-- The full Sobolev operator agrees at every order with the same
classical harmonic replacement of any smooth lift of the boundary data. -/
theorem exists_smooth_representative_ballPoissonOperator
    (a : P × (X dim) → (Mat dim)) (ha : ContDiff ℝ ∞ a)
    (K : Set (X dim)) (hK : IsCompact K) (hSupp : ∀ p z, z ∉ K → a (p,z) = 0)
    (V : Set P) (lo hi : P → ℝ)
    (hEll : ∀ p ∈ V, TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens dim : Set (X dim))
      (fun z => a (p,z)) (lo p) (hi p))
    (d : P × (X dim) → ℝ) (hd : ContDiff ℝ ∞ d) (p : P) (hp : p ∈ V) :
    let hD : ContDiff ℝ ∞ (fun z => d (p,z)) := hd.comp (contDiff_const.prodMk contDiff_id)
    ∃ (b : (X dim) → ℝ) (hb : ContDiff ℝ ∞ b), EqOn b (fun z => d (p,z)) (standardSphere dim) ∧
      EqOn (negativeBallDivergence (fun z => a (p,z)) b) 0 (ball (0:(X dim)) 1) ∧
      ∀ s : ℕ, ballPoissonOperatorL s (commonSupportMatrixFamily (s+2) a ha K hK hSupp p)
        (smoothBallSobolev (s+2) ⟨fun z => d (p,z),hD⟩) = smoothBallSobolev (s+2) ⟨b,hb⟩ := by
  let f (q : P × (X dim)) := -negativeBallDivergence (fun z => a (q.1,z)) (fun z => d (q.1,z)) q.2
  have hf : ContDiff ℝ ∞ f := (contDiff_negativeBallDivergence_family ha hd).neg
  have hfSupp (q : P) (z : (X dim)) (hz : z ∉ K) : f (q,z) = 0 := by
    have he : (fun x => a (q,x)) =ᶠ[𝓝 z] fun _ => (0:(Mat dim)) :=
      Filter.mem_of_superset (hK.isClosed.isOpen_compl.mem_nhds hz) (fun x hx => hSupp q x hx)
    have h' := negativeBallDivergence_congr_germ he (EventuallyEq.rfl (f := fun v => d (q,v)))
    change f (q,z) = _
    dsimp only [f]
    rw [h']
    simp [negativeBallDivergence,Elliptic.Lop,Elliptic.pd_const]
  obtain ⟨U,_,hU⟩ := exists_parametric_ballStrongSolution V a ha K hK hSupp f hf K hK hfSupp lo hi hEll
  obtain ⟨u,hu,hVal⟩ := exists_smooth_strongBallRepresentative (U := fun s => U s p) (fun s => (hU p hp s).1)
  let v := (strongDirichletProjectionL dim) 0 (U 0 p)
  let b (z : (X dim)) := u z + d (p,z)
  let A := fun z => a (p,z)
  have hA : ContDiff ℝ ∞ A := ha.comp (contDiff_const.prodMk contDiff_id)
  have hD : ContDiff ℝ ∞ (fun z => d (p,z)) := hd.comp (contDiff_const.prodMk contDiff_id)
  have hF : ContDiff ℝ ∞ (fun z => f (p,z)) := hf.comp (contDiff_const.prodMk contDiff_id)
  have hEq := negativeBallDivergence_eq_of_ballWeakSolution hA hF hu v hVal _
    (ballForcingFamily_value 0 f hf K hK hfSupp p) (hU p hp 0).2.1
  have hb : ContDiff ℝ ∞ b := hu.add hD
  dsimp only
  refine ⟨b,hb,?_,?_,?_⟩
  · intro z hz
    change u z + d (p,z) = d (p,z)
    rw [show u z = 0 from eqOn_zero_sphere_of_ballH1Zero hu v hVal hz,zero_add]
  · intro z hz
    change negativeBallDivergence A (u + fun w => d (p,w)) z = 0
    rw [negativeBallDivergence_add hA hu hD,hEq hz]
    exact neg_add_cancel _
  intro s
  let C := commonSupportMatrixFamily (s+2) a ha K hK hSupp p
  let J := (strongDirichletOperator fixedSobolevCalculus s C).inverse
  let D : (SmoothData dim) := ⟨fun z => d (p,z),hD⟩
  have hForce : ballForcingFamily s f hf K hK hfSupp p =
      -(fullBallDivergenceL s C (smoothBallSobolev (s+2) D)) := by
    have h := fullBallDivergence_family_smooth s a ha K hK hSupp p D
    change fullBallDivergenceL s C (smoothBallSobolev (s+2) D) = _ at h
    rw [h]
    apply TauCeti.Wkp.ext s
    simp only [← TauCeti.Wkp.valueL_apply, map_neg]
    apply Lp.ext
    refine (ballForcingFamily_value s f hf K hK hfSupp p).trans ?_
    have hD' : ContDiff ℝ ∞ (negativeBallDivergence A D.1) := contDiff_negativeBallDivergence hA hD
    have hFi := value_smoothBallSobolev_ae s (⟨negativeBallDivergence A D.1,hD'⟩ : (SmoothData dim))
    filter_upwards [hFi,Lp.coeFn_neg (TauCeti.Wkp.value s (smoothBallSobolev s
      (⟨negativeBallDivergence A D.1,hD'⟩ : (SmoothData dim))))] with z hz hz'
    simp only [TauCeti.Wkp.valueL_apply]
    exact (congrArg Neg.neg hz.symm).trans hz'.symm
  have hUS : (U s p : (BallSobolev dim) (s+2)) = smoothBallSobolev (s+2) ⟨u,hu⟩ := by
    apply TauCeti.Wkp.ext (s+2)
    apply Lp.ext
    have he := congrArg (fun t : (FixedBallH1Zero dim) => TauCeti.W1p.value (t : (FixedBallH1 dim))) (hU p hp s).1
    rw [strongDirichletProjectionL_apply,TauCeti.Wkp.value_firstOrder] at he
    change TauCeti.Wkp.value (s+2) (U s p : (BallSobolev dim) (s+2)) = TauCeti.W1p.value (v : (FixedBallH1 dim)) at he
    rw [he]
    exact hVal.trans (value_smoothBallSobolev_ae (s+2) ⟨u,hu⟩).symm
  have hSF : (U s p : (BallSobolev dim) (s+2)) =
      -(((strongDirichletSubmodule dim) s).toSubmodule.subtypeL.comp J)
        (fullBallDivergenceL s C (smoothBallSobolev (s+2) D)) := by
    have h := (hU p hp s).2.2
    change U s p = J (ballForcingFamily s f hf K hK hfSupp p) at h
    rw [h,hForce,map_neg]
    rfl
  change ballPoissonOperatorL s C (smoothBallSobolev (s+2) D) = _
  simp only [ballPoissonOperatorL,sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply]
  change smoothBallSobolev (s+2) D - (((strongDirichletSubmodule dim) s).toSubmodule.subtypeL.comp J)
    (fullBallDivergenceL s C (smoothBallSobolev (s+2) D)) = _
  rw [sub_eq_add_neg,← hSF,hUS]
  let d' : (smoothBallDataSubmodule dim) := ⟨D.1,D.2⟩
  let u' : (smoothBallDataSubmodule dim) := ⟨u,hu⟩
  change (smoothBallSobolevLinear dim) (s+2) d' + (smoothBallSobolevLinear dim) (s+2) u' =
    (smoothBallSobolevLinear dim) (s+2) (u'+d')
  exact (add_comm _ _).trans (map_add _ _ _).symm

end CalderonN

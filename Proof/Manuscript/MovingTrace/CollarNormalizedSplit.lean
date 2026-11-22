module

public import Proof.Manuscript.MovingTrace.RadializedCollar
public import Proof.CalderonN.MetricCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section
set_option maxHeartbeats 2800000

open CalderonN CalderonPatch CalderonPatch.BoundaryLayer Set Matrix
open scoped ContDiff

namespace CalderonPaper

variable {n : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "Z" => X (n+1)

def collarInverseRadial (g : MetricField (n+1)) (q : X n × ℝ) : ℝ :=
  (g (signedLayerCoordinates q))⁻¹ 0 0

def collarTangential (g : MetricField (n+1)) (q : X n × ℝ) : Mat n :=
  fun i j => (g (signedLayerCoordinates q))⁻¹ i.succ j.succ / collarInverseRadial g q

def collarNormalDrift (g : MetricField (n+1)) (q : X n × ℝ) : ℝ :=
  -2 * laplaceFirstCoeff g (signedLayerCoordinates q) 0 / collarInverseRadial g q

def collarTangentDrift (g : MetricField (n+1)) (q : X n × ℝ) (i : I n) : ℝ :=
  laplaceFirstCoeff g (signedLayerCoordinates q) i.succ / collarInverseRadial g q

private theorem joint_coordDeriv_slice_eq
    {O : Set (P × Z)} (hO : IsOpen O) {f : P × Z → ℝ}
    (hf : ContDiffOn ℝ ∞ f O) {q : P × Z} (hq : q ∈ O) (i : I (n+1)) :
    coordDeriv i (fun z => f (q.1,z)) q.2 = fderiv ℝ f q (0,axis i) := by
  have hD := ((hf.contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
  have hS : HasFDerivAt (fun z : Z => (q.1,z)) (ContinuousLinearMap.inr ℝ P Z) q.2 :=
    hasFDerivAt_prodMk_right q.1 q.2
  have h := (hD.comp q.2 hS).fderiv
  exact congrArg (fun L : Z →L[ℝ] ℝ => L (axis i)) h

theorem contDiffOn_joint_laplaceFirstCoeff
    {O : Set (P × Z)} (hO : IsOpen O) {g : P × Z → Mat (n+1)}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) O)
    (hPos : ∀ q ∈ O, (g q).PosDef) (k : I (n+1)) :
    ContDiffOn ℝ ∞ (fun q => laplaceFirstCoeff (fun z => g (q.1,z)) q.2 k) O := by
  let Q (i j : I (n+1)) (q : P × Z) := (g q)⁻¹ i j
  let D (a b c : I (n+1)) (q : P × Z) := fderiv ℝ (fun q => g q b c) q (0,axis a)
  have hQ (i j : I (n+1)) : ContDiffOn ℝ ∞ (Q i j) O :=
    contDiffOn_inv_entry_of_entries hg (fun q hq => (hPos q hq).det_pos.ne') i j
  have hD (a b c : I (n+1)) : ContDiffOn ℝ ∞ (D a b c) O :=
    ((hg b c).fderiv_of_isOpen (m := ∞) hO (by simp)).clm_apply contDiffOn_const
  let Γ (i j : I (n+1)) (q : P × Z) := (∑ l, Q k l q * (D i l j q + D j i l q - D l i j q))/2
  have hΓ (i j : I (n+1)) : ContDiffOn ℝ ∞ (Γ i j) O :=
    (ContDiffOn.sum fun l _ => (hQ k l).mul (((hD i l j).add (hD j i l)).sub (hD l i j))).div_const 2
  have hL : ContDiffOn ℝ ∞ (fun q => -(∑ i, ∑ j, Q i j q * Γ i j q)) O :=
    (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => (hQ i j).mul (hΓ i j)).neg
  apply hL.congr
  intro q hq
  simp only [laplaceFirstCoeff,christoffel,Q,Γ,D,
    fun a b c : I (n+1) => joint_coordDeriv_slice_eq hO (hg b c) hq a]

theorem inverseRadial_pos_of_posDef {g : MetricField (n+1)} {q : X n × ℝ}
    (hg : (g (signedLayerCoordinates q)).PosDef) : 0 < collarInverseRadial g q := by
  change 0 < (g (signedLayerCoordinates q))⁻¹ 0 0
  have h := metricPair_pos_of_posDef (g := fun _ => (g (signedLayerCoordinates q))⁻¹)
    (y := 0) hg.inv (v := axis 0) (by simp [axis])
  rw [metricPair_axis_left] at h
  simpa [axis] using h

theorem collarTangential_posDef {g : MetricField (n+1)} {q : X n × ℝ}
    (hg : (g (signedLayerCoordinates q)).PosDef) : (collarTangential g q).PosDef := by
  let A := (g (signedLayerCoordinates q))⁻¹
  have h : (A.submatrix Fin.succ Fin.succ).PosDef := hg.inv.submatrix (Fin.succ_injective n)
  have hEq : collarTangential g q = (collarInverseRadial g q)⁻¹ • (A.submatrix Fin.succ Fin.succ) := by
    ext i j
    simp [collarTangential,A,div_eq_mul_inv,mul_comm]
  rw [hEq]
  exact h.smul (inv_pos.mpr (inverseRadial_pos_of_posDef hg))

theorem collarTangential_symm {g : MetricField (n+1)} {q : X n × ℝ}
    (hg : (g (signedLayerCoordinates q)).PosDef) (i j : I n) :
    collarTangential g q i j = collarTangential g q j i := by
  have h := congrFun (congrFun hg.inv.isHermitian.isSymm.eq j.succ) i.succ
  exact congrArg (fun a : ℝ => a / collarInverseRadial g q) h

theorem inverseMixed_zero_of_metric_mixed_zero
    {g : MetricField (n+1)} {z : Z} (hg : (g z).PosDef)
    (hMixed : ∀ j : I n, g z 0 j.succ = 0) :
    ∀ i : I n, (g z)⁻¹ 0 i.succ = 0 ∧ (g z)⁻¹ i.succ 0 = 0 := by
  have hDiag : 0 < g z 0 0 := by
    have h := metricPair_pos_of_posDef hg (v := axis 0) (by simp [axis])
    rw [metricPair_axis_left] at h
    simpa [axis] using h
  intro i
  have h := congrArg (fun M : Mat (n+1) => M 0 i.succ)
    (Matrix.mul_nonsing_inv (g z) (isUnit_iff_ne_zero.mpr hg.det_pos.ne'))
  change (∑ j, g z 0 j * (g z)⁻¹ j i.succ) = (1 : Mat (n+1)) 0 i.succ at h
  rw [Fin.sum_univ_succ] at h
  have hO : (1 : Mat (n+1)) 0 i.succ = 0 := Matrix.one_apply_ne (Fin.succ_ne_zero i).symm
  simp only [hMixed,zero_mul,Finset.sum_const_zero,add_zero,hO] at h
  have hZ := (mul_eq_zero.mp h).resolve_left hDiag.ne'
  have hSym := congrFun (congrFun hg.inv.isHermitian.isSymm.eq 0) i.succ
  exact ⟨hZ,hSym.trans hZ⟩

theorem collarNormalizedSplit_contDiffOn
    {O : Set (P × Z)} (hO : IsOpen O) {g : P × Z → Mat (n+1)}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) O)
    (hPos : ∀ q ∈ O, (g q).PosDef) :
    let map (q : (P × X n) × ℝ) := (q.1.1,signedLayerCoordinates (q.1.2,q.2))
    let T := map ⁻¹' O
    (∀ i j, ContDiffOn ℝ ∞ (fun q => collarTangential (fun z => g (q.1.1,z)) (q.1.2,q.2) i j) T) ∧
    ContDiffOn ℝ ∞ (fun q => collarNormalDrift (fun z => g (q.1.1,z)) (q.1.2,q.2)) T ∧
    ∀ i, ContDiffOn ℝ ∞ (fun q => collarTangentDrift (fun z => g (q.1.1,z)) (q.1.2,q.2) i) T := by
  dsimp only
  let map (q : (P × X n) × ℝ) := (q.1.1,signedLayerCoordinates (q.1.2,q.2))
  have hmap : ContDiff ℝ ∞ map := contDiff_fst.fst.prodMk
    (signedLayerCoordinates.contDiff.comp (contDiff_fst.snd.prodMk contDiff_snd))
  have hT (i j : I (n+1)) : ContDiffOn ℝ ∞ (fun q => (g (map q))⁻¹ i j) (map ⁻¹' O) :=
    (contDiffOn_inv_entry_of_entries hg (fun q hq => (hPos q hq).det_pos.ne') i j).comp
      hmap.contDiffOn (mapsTo_preimage map O)
  have hL (k : I (n+1)) : ContDiffOn ℝ ∞
      (fun q => laplaceFirstCoeff (fun z => g ((map q).1,z)) (map q).2 k) (map ⁻¹' O) :=
    (contDiffOn_joint_laplaceFirstCoeff hO hg hPos k).comp hmap.contDiffOn (mapsTo_preimage map O)
  have hDet (q : (P × X n) × ℝ) (hq : q ∈ map ⁻¹' O) : (g (map q))⁻¹ 0 0 ≠ 0 :=
    (inverseRadial_pos_of_posDef (q := (q.1.2,q.2)) (g := fun z => g (q.1.1,z))
      (hPos (map q) hq)).ne'
  refine ⟨fun i j => (hT i.succ j.succ).div (hT 0 0) hDet,
    (contDiffOn_const.mul (hL 0)).div (hT 0 0) hDet,
    fun i => (hL i.succ).div (hT 0 0) hDet⟩

end CalderonPaper

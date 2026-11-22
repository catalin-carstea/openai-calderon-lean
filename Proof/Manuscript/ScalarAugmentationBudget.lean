module

public import Proof.Manuscript.ScalarHarmonicLift
public import Proof.Manuscript.NumericHarmonicJets

import all Proof.Manuscript.ScalarHarmonicLift
import Proof.CalderonN.CompactLocalJetBounds
import Proof.CalderonN.UniformCanonicalFrameJets
import Proof.CalderonN.LocalSmoothJetBudget
import Proof.CalderonN.FiniteJetBudgetAlgebra
import Proof.CalderonN.CoordinateJets
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic

public section

noncomputable section
open Set Filter Matrix Metric CalderonN
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ}

private abbrev LiftInput (n : ℕ) := Mat n × (I n → ℝ) × ℝ

private def inputMixed (p : LiftInput n) : Matrix (I n) (I 3) ℝ :=
  fun i k => if k = 0 then p.2.1 i else 0

private def inputDriftSquare (p : LiftInput n) : ℝ :=
  ((inputMixed p)ᴴ * p.1⁻¹ * inputMixed p) 0 0

private def inputSchurT (p : LiftInput n) : ℝ :=
  p.2.2^2 + (inputDriftSquare p)^2 + 2

private def inputAuxS (p : LiftInput n) : ℝ :=
  inputDriftSquare p + inputSchurT p - p.2.2

private theorem inputSchurT_pos (p : LiftInput n) : 0 < inputSchurT p := by
  unfold inputSchurT
  positivity

private theorem inputAuxS_pos (p : LiftInput n) : 0 < inputAuxS p := by
  unfold inputAuxS inputSchurT
  nlinarith [sq_nonneg (inputDriftSquare p + 1/2), sq_nonneg (p.2.2 - 1/2)]

private def augmentFromInput (p : LiftInput n) : Mat (n+3) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (schurDetOne p.1 (inputMixed p) (inputSchurT p) (inputAuxS p))

private def liftInput (L : ScalarElliptic n) (x : X n) : LiftInput n :=
  (L.principalMatrix x, fun i => L.halfDrift i x, L.remainingPotential x)

private theorem augmentFromInput_liftInput (L : ScalarElliptic n) (x : X n) :
    augmentFromInput (liftInput L x) = L.augmentedInverse x := rfl

private theorem augmentFromInput_posDef (p : LiftInput n) (hp : p.1.PosDef) :
    (augmentFromInput p).PosDef :=
  (schurDetOne_posDef_and_det p.1 hp (inputMixed p)
    (inputSchurT_pos p) (inputAuxS_pos p)).1.submatrix finSumFinEquiv.symm.injective

private theorem augmentFromInput_contDiffAt (p : LiftInput n) (hp : p.1.PosDef)
    (i j : I (n+3)) : ContDiffAt ℝ ∞ (fun q => augmentFromInput q i j) p := by
  let Hd : Set (LiftInput n) := {q | q.1.det ≠ 0}
  have hEntry (i j : I n) : ContDiff ℝ ∞ (fun q : LiftInput n => q.1 i j) :=
    (matrixEntryL i j).contDiff.comp contDiff_fst
  have hDet : ContDiff ℝ ∞ (fun q : LiftInput n => q.1.det) :=
    contDiffOn_univ.mp (contDiffOn_det_of_entries fun i j => (hEntry i j).contDiffOn)
  have hOpen : IsOpen Hd := isOpen_ne.preimage hDet.continuous
  have hpH : p ∈ Hd := hp.det_pos.ne'
  have hInv (i j : I n) : ContDiffAt ℝ ∞ (fun q : LiftInput n => q.1⁻¹ i j) p :=
    (contDiffOn_inv_entry_of_entries (fun i j => (hEntry i j).contDiffOn)
      (show ∀ q ∈ Hd, q.1.det ≠ 0 from fun _ hq => hq) i j).contDiffAt (hOpen.mem_nhds hpH)
  have hQ (i : I n) (j : I 3) : ContDiffAt ℝ ∞ (fun q => inputMixed q i j) p := by
    by_cases hj : j = 0
    · have hi : ContDiff ℝ ∞ (fun q : LiftInput n => q.2.1 i) := by
        let ev : (I n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) i
        change ContDiff ℝ ∞ (ev ∘ Prod.fst ∘ Prod.snd)
        exact ev.contDiff.comp (contDiff_fst.comp contDiff_snd)
      simpa only [inputMixed,ite_eq_left hj] using hi.contDiffAt (x := p)
    · simp only [inputMixed,ite_eq_right hj,contDiffAt_const]
  have hquad (i j : I 3) :
      ContDiffAt ℝ ∞ (fun q => ((inputMixed q)ᴴ * q.1⁻¹ * inputMixed q) i j) p := by
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial]
    exact ContDiffAt.sum fun k _ => (ContDiffAt.sum fun l _ =>
      (hQ l i).mul (hInv l k)).mul (hQ k j)
  have hB : ContDiffAt ℝ ∞ (fun q : LiftInput n => q.2.2) p :=
    (contDiff_snd.comp contDiff_snd).contDiffAt
  have hSc : ContDiffAt ℝ ∞ inputSchurT p :=
    ((hB.pow 2).add ((hquad 0 0).pow 2)).add contDiffAt_const
  have hS : ContDiffAt ℝ ∞ inputAuxS p :=
    ((hquad 0 0).add hSc).sub hB
  have haux (k : I 3) : ContDiffAt ℝ ∞ (fun q : LiftInput n =>
      ![inputSchurT q, inputAuxS q, (q.1.det * inputSchurT q * inputAuxS q)⁻¹] k) p := by
    fin_cases k
    · exact hSc
    · exact hS
    · exact ((hDet.contDiffAt.mul hSc).mul hS).inv
        (mul_ne_zero (mul_ne_zero hpH (inputSchurT_pos p).ne') (inputAuxS_pos p).ne')
  change ContDiffAt ℝ ∞ (fun q =>
    schurDetOne q.1 (inputMixed q) (inputSchurT q) (inputAuxS q)
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) p
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j
  · exact (hEntry i j).contDiffAt
  · exact hQ i j
  · simpa only [schurDetOne,fromBlocks_apply₂₁,conjTranspose_apply,star_trivial] using hQ j i
  · apply (hquad i j).add
    by_cases hij : i = j
    · subst j
      simpa only [diagonal_apply_eq] using haux i
    · simp [diagonal_apply_ne _ hij,contDiffAt_const]


private theorem scalarBudget_sub {f g : X n → ℝ} {x : X n} {N : ℕ} {A B : ℝ}
    (hf : LocalSmoothJetBudget f x N A) (hg : LocalSmoothJetBudget g x N B) :
    LocalSmoothJetBudget (fun y => f y - g y) x N (A+B) :=
  ⟨hf.smooth.sub hg.smooth,fun k hk =>
    (ShrinkingSpheres.norm_iteratedFDeriv_sub_at_le f g x hf.smooth hg.smooth k).trans
      (add_le_add (hf.bound k hk) (hg.bound k hk))⟩

private theorem scalarBudget_coordDeriv {f : X n → ℝ} {x : X n} {N : ℕ} {A : ℝ}
    (hf : LocalSmoothJetBudget f x (N+1) A) (i : I n) :
    LocalSmoothJetBudget (coordDeriv i f) x N A :=
  ⟨(hf.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const,fun k hk =>
    (norm_iteratedFDeriv_coordDeriv_le hf.smooth i k).trans (hf.bound (k+1) (Nat.succ_le_succ hk))⟩

private theorem scalarBudget_pi {f : X n → I n → ℝ} {x : X n} {N : ℕ} {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ i, LocalSmoothJetBudget (fun y => f y i) x N A) :
    LocalSmoothJetBudget f x N A := by
  have hs : ContDiffAt ℝ ∞ f x := contDiffAt_pi.mpr fun i => (h i).smooth
  refine ⟨hs,fun k hk => ?_⟩
  apply ContinuousMultilinearMap.opNorm_le_bound hA
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hA (Finset.prod_nonneg (fun j _ => norm_nonneg (v j))))).2
  intro i
  let r : (I n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) i
  have hr := r.iteratedFDeriv_comp_left (hs.of_le (by simp : (k : ℕ∞ω) ≤ ∞)) (n := k) le_rfl
  have he := congrArg (fun T : X n [×k]→L[ℝ] ℝ => T v) hr
  change iteratedFDeriv ℝ k (fun y => f y i) x v = (iteratedFDeriv ℝ k f x v) i at he
  rw [← he]
  exact (ContinuousMultilinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right ((h i).bound k hk) (Finset.prod_nonneg fun _ _ => norm_nonneg _))

private def halfDriftBudget (n : ℕ) (A : ℝ) : ℝ := A + n*A

private def potentialBudget (n : ℕ) (A : ℝ) : ℝ := A + n*halfDriftBudget n A

private theorem liftInput_budget {L : ScalarElliptic n} {D : Set (X n)}
    (hD : IsOpen D) (hL : L.SmoothOn D) {x : X n} (hx : x ∈ D)
    {a A : ℝ} (hA : 0 < A) (N : ℕ) (hb : L.CoefficientBound D a A (N+2)) :
    LocalSmoothJetBudget (liftInput L) x N
      (max A (max (halfDriftBudget n A) (potentialBudget n A))) := by
  have hPrincipal (i j : I n) :
      LocalSmoothJetBudget (fun y => L.principalMatrix y i j) x (N+2) A :=
    ⟨(contDiffOn_metric_inv_entry hL.1 i j).contDiffAt (hD.mem_nhds hx),fun k hk => (hb.2 x hx k hk).1 i j⟩
  have hFirst (j : I n) :
      LocalSmoothJetBudget (fun y => L.first y j) x (N+1) A :=
    ⟨(hL.2.1 j).contDiffAt (hD.mem_nhds hx),fun k hk => (hb.2 x hx k (by omega)).2.1 j⟩
  have hZeroth : LocalSmoothJetBudget L.zeroth x N A :=
    ⟨hL.2.2.contDiffAt (hD.mem_nhds hx),fun k hk => (hb.2 x hx k (by omega)).2.2⟩
  have hDiv (j : I n) :
      LocalSmoothJetBudget (L.matrixDiv j) x (N+1) (n*A) := by
    change LocalSmoothJetBudget (fun y => ∑ i, coordDeriv i (fun y => L.principalMatrix y i j) y) x (N+1) _
    simpa using (LocalSmoothJetBudget.finite_sum Finset.univ
      (fun i => coordDeriv i (fun y => L.principalMatrix y i j)) (fun _ => A)
      (fun i _ => scalarBudget_coordDeriv (hPrincipal i j) i))
  have hQ (j : I n) :
      LocalSmoothJetBudget (L.halfDrift j) x (N+1) (halfDriftBudget n A) := by
    let f : X n → ℝ := fun y => L.first y j - L.matrixDiv j y
    have hf := scalarBudget_sub (hFirst j) (hDiv j)
    refine ⟨by exact hf.smooth.div_const 2,fun k hk => ?_⟩
    change ‖iteratedFDeriv ℝ k (fun y => f y / 2) x‖ ≤ _
    simp_rw [div_eq_inv_mul, ← smul_eq_mul]
    rw [ShrinkingSpheres.norm_iteratedFDeriv_const_smul_at f x hf.smooth]
    norm_num only [abs_of_nonneg (by norm_num : 0 ≤ (2:ℝ)⁻¹)]
    exact (mul_le_mul_of_nonneg_left (hf.bound k hk) (by norm_num)).trans
      (by have h := hf.nonneg; unfold halfDriftBudget; linarith)
  have hQsum : LocalSmoothJetBudget (fun y => ∑ i, coordDeriv i (L.halfDrift i) y) x N
      (n*halfDriftBudget n A) := by
    simpa using (LocalSmoothJetBudget.finite_sum Finset.univ (fun i => coordDeriv i (L.halfDrift i))
      (fun _ => halfDriftBudget n A) (fun i _ => scalarBudget_coordDeriv (hQ i) i))
  have hB : LocalSmoothJetBudget L.remainingPotential x N (potentialBudget n A) :=
    scalarBudget_sub hZeroth hQsum
  have hMat : LocalSmoothJetBudget L.principalMatrix x N A := by
    refine ⟨contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => (hPrincipal i j).smooth,?_⟩
    intro k hk
    exact norm_iteratedFDeriv_matrix_le_of_entries L.principalMatrix x k
      (contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => (hPrincipal i j).smooth)
      hA.le (fun i j => (hPrincipal i j).bound k (by omega))
  have hq0 : 0 ≤ halfDriftBudget n A := by unfold halfDriftBudget; positivity
  have hq : LocalSmoothJetBudget (fun y i => L.halfDrift i y) x N (halfDriftBudget n A) :=
    scalarBudget_pi hq0 (fun i => (hQ i).mono_order (Nat.le_succ _))
  exact hMat.prod (hq.prod hB)

private theorem abs_wordDeriv_le_jet {U : Set (X n)} (hU : IsOpen U)
    {f : X n → ℝ} (hf : ContDiffOn ℝ ∞ f U) (w : List (I n)) {x : X n} (hx : x ∈ U) :
    |wordDeriv w f x| ≤ ‖iteratedFDeriv ℝ w.length f x‖ := by
  have h (w : List (I n)) (k : ℕ) :
      ContDiffOn ℝ ∞ (wordDeriv w f) U ∧
        ‖iteratedFDeriv ℝ k (wordDeriv w f) x‖ ≤ ‖iteratedFDeriv ℝ (k + w.length) f x‖ := by
    induction w generalizing k with
    | nil => simpa [wordDeriv] using And.intro hf (le_refl (‖iteratedFDeriv ℝ k f x‖))
    | cons i w ih =>
      refine ⟨contDiffOn_coordDeriv (ih k).1 hU i,?_⟩
      refine (norm_iteratedFDeriv_coordDeriv_le ((ih k).1.contDiffAt (hU.mem_nhds hx)) i k).trans ?_
      rw [show k + (i :: w).length = k + 1 + w.length by simp; omega]
      exact (ih (k+1)).2
  have hw := (h w 0).2
  rw [show (0 : ℕ) + w.length = w.length from Nat.zero_add _,norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hw
  exact hw


set_option maxHeartbeats 3800000 in
/-- Any fixed finite budget on the scalar coefficients yields a common
divergence ellipticity floor and finite word budget on the lifted equations.
The input of the Schur construction ranges over a compact finite-dimensional
elliptic matrix locus times a drift and a potential ball. -/
theorem exists_numeric_augmented_divergence_budget [NeZero n]
    (a A : ℝ) (ha : 0 < a) (hA : 0 < A) (N : ℕ) :
    ∃ lam Ma : ℝ, 0 < lam ∧ 0 ≤ Ma ∧
      ∀ {D : Set (X n)} (L : ScalarElliptic n), IsOpen D → L.SmoothOn D →
        L.CoefficientBound D a A (N+2) →
        Elliptic.HasEllipticityFloor (fun i j z => divergenceCoeff L.augmentedMetric z i j)
          (baseProjection ⁻¹' D) lam ∧
        Elliptic.HasWordBudget (fun i j z => divergenceCoeff L.augmentedMetric z i j)
          (baseProjection ⁻¹' D) Ma N := by
  let R := max 1 (max A (max (halfDriftBudget n A) (potentialBudget n A)))
  have hR : 1 ≤ R := le_max_left _ _
  let J : Set (LiftInput n) := (ellipticMatrixLocus n a⁻¹ R) ×ˢ
    (closedBall (0 : I n → ℝ) R ×ˢ closedBall (0 : ℝ) R)
  have hJ : IsCompact J := (isCompact_ellipticMatrixLocus n a⁻¹ R).prod
    ((isCompact_closedBall (0 : I n → ℝ) R).prod (isCompact_closedBall (0 : ℝ) R))
  have hPos (p : LiftInput n) (hp : p ∈ J) : p.1.PosDef :=
    ellipticMatrixLocus_posDef (inv_pos.mpr ha) hp.1
  have hSmooth (p : LiftInput n) (hp : p ∈ J) i j :=
    augmentFromInput_contDiffAt p (hPos p hp) i j
  have hContinuous : ContinuousOn augmentFromInput J :=
    fun p hp => (contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j =>
      hSmooth p hp i j).continuousAt.continuousWithinAt
  obtain ⟨lam,hlam,hEll⟩ := Elliptic.lower_ellipticity_on_compact
    (a := fun i j (Q : Mat (n+3)) => Q i j) (fun i j => (matrixEntryL i j).continuous)
    (hJ.image_of_continuousOn hContinuous) (by
      rintro _ ⟨p,hp,rfl⟩
      exact augmentFromInput_posDef p (hPos p hp))
  choose B hB hJet using (fun i j : I (n+3) => exists_uniform_local_finite_jet_bound hJ
    (fun p hp => hSmooth p hp i j) N)
  let B₀ := 1 + ∑ i : I (n+3), ∑ j : I (n+3), B i j
  have hB₀ : 1 ≤ B₀ := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => zero_le_one.trans (hB i j))
  have hBbound (i j : I (n+3)) : B i j ≤ B₀ :=
    ((Finset.single_le_sum (fun k _ => zero_le_one.trans (hB i k)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => zero_le_one.trans (hB k l))
        (Finset.mem_univ i))).trans (le_add_of_nonneg_left zero_le_one)
  let C := N.factorial * B₀ * R^N
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let Ma := (N.factorial : ℝ) * C * (max 1 ‖(baseProjection : X (n+3) →L[ℝ] X n)‖)^N
  refine ⟨lam,Ma,hlam,by dsimp [Ma]; positivity,?_⟩
  intro D L hD hL hb
  have hU : IsOpen (baseProjection ⁻¹' D : Set (X (n+3))) := hD.preimage baseProjection.continuous
  have hInput (x : X n) (hx : x ∈ D) : LocalSmoothJetBudget (liftInput L) x N R :=
    (liftInput_budget hD hL hx hA N hb).enlarge (le_max_right 1 _)
  have hMem (x : X n) (hx : x ∈ D) : liftInput L x ∈ J := by
    have hin := (hInput x hx).value_norm_le
    rw [Prod.norm_def,Prod.norm_def,max_le_iff,max_le_iff] at hin
    refine ⟨⟨mem_closedBall_zero_iff.mpr hin.1, (hL.1.2 x hx).inv.1,?_⟩,
      mem_closedBall_zero_iff.mpr hin.2.1,mem_closedBall_zero_iff.mpr hin.2.2⟩
    intro u
    simpa only [inv_inv,metricPair,liftInput] using hb.1 x hx u
  have hEq (z : X (n+3)) (hz : z ∈ baseProjection ⁻¹' D) (i j : I (n+3)) :
      divergenceCoeff L.augmentedMetric z i j =
        augmentFromInput (liftInput L (baseProjection z)) i j := by
    rw [augmentFromInput_liftInput,divergenceCoeff,augmentedMetric_volume hL hz,
      augmentedMetric_inverse hL hz,one_mul]
  constructor
  · intro z hz p
    simp only [hEq z hz]
    exact hEll _ ⟨liftInput L (baseProjection z),hMem (baseProjection z) hz,rfl⟩ p
  · intro z hz i j w hw
    have hP := hMem (baseProjection z) hz
    have hout : LocalSmoothJetBudget (fun p => augmentFromInput p i j)
        (liftInput L (baseProjection z)) N B₀ :=
      ⟨hSmooth _ hP i j,fun k hk => (hJet i j _ hP k hk).trans (hBbound i j)⟩
    have hlift : LocalSmoothJetBudget (fun x => L.augmentedInverse x i j) (baseProjection z) N C := by
      simpa only [Function.comp_def,augmentFromInput_liftInput] using (hInput (baseProjection z) hz).comp hout hR
    have hUp := hlift.linear_precomp baseProjection z
    have hN : ∀ᶠ y in 𝓝 z, y ∈ baseProjection ⁻¹' D := hU.mem_nhds hz
    have he : (fun z => divergenceCoeff L.augmentedMetric z i j) =ᶠ[𝓝 z]
        (fun z => L.augmentedInverse (baseProjection z) i j) :=
      hN.mono fun z hz => (hEq z hz i j).trans (congrFun (congrFun
        (augmentFromInput_liftInput L (baseProjection z)) i) j)
    have hjetEq := (he.iteratedFDeriv (𝕜 := ℝ) w.length).eq_of_nhds
    calc
      _ ≤ ‖iteratedFDeriv ℝ w.length (fun z => divergenceCoeff L.augmentedMetric z i j) z‖ :=
        abs_wordDeriv_le_jet hU (contDiffOn_divergenceCoeff
          (augmentedMetric_smooth hD hL) i j) w hz
      _ = _ := congrArg norm hjetEq
      _ ≤ Ma := hUp.bound w.length hw

end CalderonPaper.ScalarElliptic

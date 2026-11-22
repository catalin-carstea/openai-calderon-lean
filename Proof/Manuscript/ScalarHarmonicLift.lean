module

public import Proof.Manuscript.ScalarElliptic

public import Proof.Manuscript.ScalarSchurCompletion
import Proof.CalderonN.MetricDivergence
import Proof.CalderonN.MetricCalculus
import Proof.CalderonN.ChartGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

@[expose] public section

open Set Matrix CalderonN
open scoped ContDiff

noncomputable section

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ}

abbrev splitAux : X (n + 3) ≃L[ℝ] X n × X 3 := EuclideanSpace.finAddEquivProd
abbrev baseProjection : X (n+3) →L[ℝ] X n :=
  (ContinuousLinearMap.fst ℝ (X n) (X 3)).comp splitAux.toContinuousLinearMap
abbrev auxiliaryProjection : X (n+3) →L[ℝ] X 3 :=
  (ContinuousLinearMap.snd ℝ (X n) (X 3)).comp splitAux.toContinuousLinearMap

private theorem splitAux_axis_base (i : I n) :
    splitAux (axis (i.castAdd 3)) = (axis i,0) := by
  apply Prod.ext <;> ext j <;> simp [axis, PiLp.single_apply]

private theorem splitAux_axis_auxiliary (i : I 3) :
    splitAux (axis (i.natAdd n)) = (0,axis i) := by
  apply Prod.ext <;> ext j <;> simp [axis, PiLp.single_apply]

def matrixDiv (L : ScalarElliptic n) (j : I n) (x : X n) : ℝ :=
  ∑ i, coordDeriv i (fun z => L.principalMatrix z i j) x

def halfDrift (L : ScalarElliptic n) (j : I n) (x : X n) : ℝ :=
  (L.first x j - L.matrixDiv j x) / 2

def remainingPotential (L : ScalarElliptic n) (x : X n) : ℝ :=
  L.zeroth x - ∑ i, coordDeriv i (L.halfDrift i) x

def mixedBlock (L : ScalarElliptic n) (x : X n) : Matrix (I n) (I 3) ℝ :=
  fun i k => if k = 0 then L.halfDrift i x else 0

def driftSquare (L : ScalarElliptic n) (x : X n) : ℝ :=
  ((L.mixedBlock x)ᴴ * (L.principalMatrix x)⁻¹ * L.mixedBlock x) 0 0

def schurT (L : ScalarElliptic n) (x : X n) : ℝ :=
  (L.remainingPotential x)^2 + (L.driftSquare x)^2 + 2

def auxT (L : ScalarElliptic n) (x : X n) : ℝ :=
  L.driftSquare x + L.schurT x

def auxS (L : ScalarElliptic n) (x : X n) : ℝ :=
  L.auxT x - L.remainingPotential x

theorem schurT_pos (L : ScalarElliptic n) (x : X n) : 0 < L.schurT x := by
  unfold schurT
  positivity

theorem auxS_pos (L : ScalarElliptic n) (x : X n) : 0 < L.auxS x := by
  unfold auxS auxT schurT
  nlinarith [sq_nonneg (L.driftSquare x + 1/2), sq_nonneg (L.remainingPotential x - 1/2)]

def augmentedInverse (L : ScalarElliptic n) (x : X n) : Mat (n+3) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (schurDetOne (L.principalMatrix x) (L.mixedBlock x) (L.schurT x) (L.auxS x))

def augmentedMetric (L : ScalarElliptic n) : MetricField (n+3) :=
  fun z => (L.augmentedInverse (baseProjection z))⁻¹

theorem augmentedInverse_posDef_det {L : ScalarElliptic n} {D : Set (X n)}
    (hL : L.SmoothOn D) {x : X n} (hx : x ∈ D) :
    (L.augmentedInverse x).PosDef ∧ (L.augmentedInverse x).det = 1 := by
  obtain ⟨hpos,hdet⟩ := schurDetOne_posDef_and_det (L.principalMatrix x)
    (hL.1.2 x hx).inv (L.mixedBlock x) (L.schurT_pos x) (L.auxS_pos x)
  exact ⟨hpos.submatrix finSumFinEquiv.symm.injective,
    (Matrix.det_reindex_self _ _).trans hdet⟩

private theorem matrixDiv_smooth {L : ScalarElliptic n} {D : Set (X n)}
    (hD : IsOpen D) (hL : L.SmoothOn D) (j : I n) :
    ContDiffOn ℝ ∞ (L.matrixDiv j) D :=
  ContDiffOn.sum fun i _ => contDiffOn_coordDeriv (contDiffOn_metric_inv_entry hL.1 i j) hD i

private theorem halfDrift_smooth {L : ScalarElliptic n} {D : Set (X n)}
    (hD : IsOpen D) (hL : L.SmoothOn D) (j : I n) :
    ContDiffOn ℝ ∞ (L.halfDrift j) D :=
  ((hL.2.1 j).sub (matrixDiv_smooth hD hL j)).div_const 2

private theorem remainingPotential_smooth {L : ScalarElliptic n} {D : Set (X n)}
    (hD : IsOpen D) (hL : L.SmoothOn D) :
    ContDiffOn ℝ ∞ L.remainingPotential D :=
  hL.2.2.sub (ContDiffOn.sum fun i _ => contDiffOn_coordDeriv (halfDrift_smooth hD hL i) hD i)

private theorem mixedBlock_smooth {L : ScalarElliptic n} {D : Set (X n)}
    (hD : IsOpen D) (hL : L.SmoothOn D) (i : I n) (j : I 3) :
    ContDiffOn ℝ ∞ (fun x => L.mixedBlock x i j) D := by
  by_cases hj : j = 0
  · simpa only [mixedBlock, ite_eq_left hj] using halfDrift_smooth hD hL i
  · simp only [mixedBlock, ite_eq_right hj, contDiffOn_const]

private theorem mixedQuadratic_smooth {L : ScalarElliptic n} {D : Set (X n)}
    (hD : IsOpen D) (hL : L.SmoothOn D) (i j : I 3) :
    ContDiffOn ℝ ∞ (fun x => ((L.mixedBlock x)ᴴ * (L.principalMatrix x)⁻¹ * L.mixedBlock x) i j) D := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial]
  have hA (k l : I n) : ContDiffOn ℝ ∞ (fun x => (L.principalMatrix x)⁻¹ k l) D := by
    refine (hL.1.1 k l).congr fun x hx => ?_
    rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hL.1.2 x hx).det_pos.ne')]
  exact ContDiffOn.sum fun k _ =>
    (ContDiffOn.sum fun l _ => (mixedBlock_smooth hD hL l i).mul (hA l k)).mul (mixedBlock_smooth hD hL k j)

private theorem schurT_smooth {L : ScalarElliptic n} {D : Set (X n)}
    (hD : IsOpen D) (hL : L.SmoothOn D) :
    ContDiffOn ℝ ∞ L.schurT D :=
  (((remainingPotential_smooth hD hL).pow 2).add ((mixedQuadratic_smooth hD hL 0 0).pow 2)).add
    contDiffOn_const

private theorem auxS_smooth {L : ScalarElliptic n} {D : Set (X n)}
    (hD : IsOpen D) (hL : L.SmoothOn D) :
    ContDiffOn ℝ ∞ L.auxS D :=
  ((mixedQuadratic_smooth hD hL 0 0).add (schurT_smooth hD hL)).sub (remainingPotential_smooth hD hL)

theorem augmentedInverse_smooth {L : ScalarElliptic n} {D : Set (X n)}
    (hD : IsOpen D) (hL : L.SmoothOn D) (i j : I (n+3)) :
    ContDiffOn ℝ ∞ (fun x => L.augmentedInverse x i j) D := by
  have haux (k : I 3) :
      ContDiffOn ℝ ∞ (fun x => ![L.schurT x, L.auxS x,
          ((L.principalMatrix x).det * L.schurT x * L.auxS x)⁻¹] k) D := by
    fin_cases k
    · exact schurT_smooth hD hL
    · exact auxS_smooth hD hL
    · apply ((contDiffOn_det_of_entries fun i j => contDiffOn_metric_inv_entry hL.1 i j).mul
        (schurT_smooth hD hL) |>.mul (auxS_smooth hD hL)).inv
      intro x hx
      exact mul_ne_zero (mul_ne_zero (hL.1.2 x hx).inv.det_pos.ne'
        (L.schurT_pos x).ne') (L.auxS_pos x).ne'
  change ContDiffOn ℝ ∞ (fun x =>
    schurDetOne (L.principalMatrix x) (L.mixedBlock x) (L.schurT x) (L.auxS x)
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) D
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j
  · exact contDiffOn_metric_inv_entry hL.1 i j
  · exact mixedBlock_smooth hD hL i j
  · simpa only [schurDetOne, fromBlocks_apply₂₁, conjTranspose_apply, star_trivial]
      using mixedBlock_smooth hD hL j i
  · apply (mixedQuadratic_smooth hD hL i j).add
    by_cases hij : i = j
    · subst j
      simpa only [diagonal_apply_eq] using haux i
    · simp [diagonal_apply_ne _ hij, contDiffOn_const]

theorem augmentedMetric_smooth {L : ScalarElliptic n} {D : Set (X n)}
    (hD : IsOpen D) (hL : L.SmoothOn D) :
    SmoothMetric (baseProjection ⁻¹' D) L.augmentedMetric := by
  refine ⟨fun i j => ?_, fun z hz => (augmentedInverse_posDef_det hL hz).1.inv⟩
  exact (contDiffOn_inv_entry_of_entries (augmentedInverse_smooth hD hL)
    (fun x hx => (augmentedInverse_posDef_det hL hx).1.det_pos.ne') i j).comp
      baseProjection.contDiff.contDiffOn (fun _ hz => hz)

theorem augmentedMetric_volume {L : ScalarElliptic n} {D : Set (X n)}
    (hL : L.SmoothOn D) {z : X (n+3)} (hz : baseProjection z ∈ D) :
    chartVolume L.augmentedMetric z = 1 := by
  unfold chartVolume augmentedMetric
  rw [Matrix.det_nonsing_inv, (augmentedInverse_posDef_det hL hz).2, Ring.inverse_one, Real.sqrt_one]

theorem augmentedMetric_inverse {L : ScalarElliptic n} {D : Set (X n)}
    (hL : L.SmoothOn D) {z : X (n+3)} (hz : baseProjection z ∈ D) :
    (L.augmentedMetric z)⁻¹ = L.augmentedInverse (baseProjection z) :=
  Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr (augmentedInverse_posDef_det hL hz).1.det_pos.ne')

private theorem coordDeriv_linearComp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} (A : X d →L[ℝ] E) {f : E → ℝ} {z : X d}
    (hf : DifferentiableAt ℝ f (A z)) (i : I d) :
    coordDeriv i (f ∘ A) z = fderiv ℝ f (A z) (A (axis i)) := by
  rw [coordDeriv, fderiv_comp z hf A.differentiableAt, ContinuousLinearMap.fderiv]
  rfl

private theorem coordDeriv_mul_at {d : ℕ} {f h : X d → ℝ} {z : X d}
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) (i : I d) :
    coordDeriv i (fun z => f z * h z) z =
      coordDeriv i f z * h z + f z * coordDeriv i h z := by
  rw [coordDeriv, fderiv_fun_mul hf hh]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, coordDeriv]
  ring

private theorem coordDeriv_baseComp_base {u : X n → ℝ} {z : X (n+3)}
    (hu : DifferentiableAt ℝ u (baseProjection z)) (i : I n) :
    coordDeriv (i.castAdd 3) (u ∘ baseProjection) z = coordDeriv i u (baseProjection z) := by
  rw [coordDeriv_linearComp baseProjection hu]
  have h : baseProjection (axis (i.castAdd 3)) = axis i := congrArg Prod.fst (splitAux_axis_base i)
  rw [h]
  rfl

private theorem coordDeriv_baseComp_aux {u : X n → ℝ} {z : X (n+3)}
    (hu : DifferentiableAt ℝ u (baseProjection z)) (i : I 3) :
    coordDeriv (i.natAdd n) (u ∘ baseProjection) z = 0 := by
  rw [coordDeriv_linearComp baseProjection hu]
  have h : baseProjection (axis (i.natAdd n)) = (0 : X n) :=
    congrArg Prod.fst (splitAux_axis_auxiliary i)
  rw [h, map_zero]

private theorem coordDeriv_auxComp_base {f : X 3 → ℝ} {z : X (n+3)}
    (hf : DifferentiableAt ℝ f (auxiliaryProjection z)) (i : I n) :
    coordDeriv (i.castAdd 3) (f ∘ auxiliaryProjection) z = 0 := by
  rw [coordDeriv_linearComp auxiliaryProjection hf]
  have h : auxiliaryProjection (axis (i.castAdd 3)) = 0 :=
    congrArg Prod.snd (splitAux_axis_base i)
  rw [h, map_zero]

private theorem coordDeriv_auxComp_aux {f : X 3 → ℝ} {z : X (n+3)}
    (hf : DifferentiableAt ℝ f (auxiliaryProjection z)) (i : I 3) :
    coordDeriv (i.natAdd n) (f ∘ auxiliaryProjection) z = coordDeriv i f (auxiliaryProjection z) := by
  rw [coordDeriv_linearComp auxiliaryProjection hf]
  have h : auxiliaryProjection (axis (i.natAdd n)) = axis i :=
    congrArg Prod.snd (splitAux_axis_auxiliary (n := n) i)
  rw [h]
  rfl

/-- Fixed real profile on the three added coordinates. -/
def auxProfile (z : X 3) : ℝ := Real.exp (z 0) * Real.cos (z 1)

private def auxProfileS (z : X 3) : ℝ := Real.exp (z 0) * (-Real.sin (z 1))

private abbrev pcoord (i : I 3) : X 3 →L[ℝ] ℝ := EuclideanSpace.proj i

theorem auxProfile_smooth : ContDiff ℝ ∞ auxProfile :=
  (Real.contDiff_exp.comp (pcoord 0).contDiff).mul
    (Real.contDiff_cos.comp (pcoord 1).contDiff)

private theorem auxProfileS_smooth : ContDiff ℝ ∞ auxProfileS :=
  (Real.contDiff_exp.comp (pcoord 0).contDiff).mul
    ((Real.contDiff_sin.comp (pcoord 1).contDiff).neg)

private theorem coordDeriv_realCompose {f : ℝ → ℝ} {a : ℝ} {z : X 3} (i j : I 3)
    (hf : HasDerivAt f a (z j)) :
    coordDeriv i (fun z : X 3 => f (z j)) z = a * (if i = j then 1 else 0) := by
  have h := hf.hasFDerivAt.comp z (pcoord j).hasFDerivAt
  change coordDeriv i (f ∘ pcoord j) z = _
  rw [coordDeriv, h.fderiv]
  change (axis i) j • a = _
  simp [axis, PiLp.single_apply, smul_eq_mul, eq_comm, mul_comm]

private theorem coordDeriv_auxProfile (i : I 3) (z : X 3) :
    coordDeriv i auxProfile z =
      ![auxProfile z, auxProfileS z, 0] i := by
  let f : X 3 → ℝ := Real.exp ∘ pcoord 0
  let h : X 3 → ℝ := Real.cos ∘ pcoord 1
  change coordDeriv i (fun w => f w * h w) z = _
  have h₀ := ((Real.hasDerivAt_exp (z 0)).hasFDerivAt.comp z (pcoord 0).hasFDerivAt).differentiableAt
  have h₁ := ((Real.hasDerivAt_cos (z 1)).hasFDerivAt.comp z (pcoord 1).hasFDerivAt).differentiableAt
  rw [coordDeriv_mul_at (f := f) (h := h) h₀ h₁]
  change coordDeriv i (fun w : X 3 => Real.exp (w 0)) z * Real.cos (z 1) +
    Real.exp (z 0) * coordDeriv i (fun w : X 3 => Real.cos (w 1)) z = _
  rw [coordDeriv_realCompose i 0 (Real.hasDerivAt_exp _),
    coordDeriv_realCompose i 1 (Real.hasDerivAt_cos _)]
  fin_cases i <;> simp [auxProfile, auxProfileS]

private theorem coordDeriv_auxProfileS_one (z : X 3) :
    coordDeriv 1 auxProfileS z = -auxProfile z := by
  let f : X 3 → ℝ := Real.exp ∘ pcoord 0
  let h : X 3 → ℝ := (-Real.sin) ∘ pcoord 1
  change coordDeriv 1 (fun w => f w * h w) z = _
  have h₀ := ((Real.hasDerivAt_exp (z 0)).hasFDerivAt.comp z (pcoord 0).hasFDerivAt).differentiableAt
  have h₁ := (((Real.hasDerivAt_sin (z 1)).neg).hasFDerivAt.comp z (pcoord 1).hasFDerivAt).differentiableAt
  rw [coordDeriv_mul_at (f := f) (h := h) h₀ h₁]
  change coordDeriv 1 (fun w : X 3 => Real.exp (w 0)) z * (-Real.sin (z 1)) +
    Real.exp (z 0) * coordDeriv 1 (fun w : X 3 => -Real.sin (w 1)) z = _
  have hs : HasDerivAt (fun v : ℝ => -Real.sin v) (-Real.cos (z 1)) (z 1) :=
    (Real.hasDerivAt_sin (z 1)).neg
  rw [coordDeriv_realCompose 1 0 (Real.hasDerivAt_exp _), coordDeriv_realCompose 1 1 hs]
  simp [auxProfile]

def liftedFunction (u : X n → ℝ) (z : X (n+3)) : ℝ :=
  u (baseProjection z) * auxProfile (auxiliaryProjection z)

theorem liftedFunction_smooth {D : Set (X n)} {u : X n → ℝ}
    (hu : ContDiffOn ℝ ∞ u D) :
    ContDiffOn ℝ ∞ (liftedFunction u) (baseProjection ⁻¹' D) :=
  (hu.comp baseProjection.contDiff.contDiffOn (fun _ hz => hz)).mul
    ((auxProfile_smooth.comp auxiliaryProjection.contDiff).contDiffOn)

private theorem coordDeriv_lifted_base {u : X n → ℝ} {z : X (n+3)}
    (hu : DifferentiableAt ℝ u (baseProjection z)) (i : I n) :
    coordDeriv (i.castAdd 3) (liftedFunction u) z =
      coordDeriv i u (baseProjection z) * auxProfile (auxiliaryProjection z) := by
  have hφ : DifferentiableAt ℝ auxProfile (auxiliaryProjection z) :=
    (auxProfile_smooth.differentiable (by simp)).differentiableAt
  change coordDeriv _ (fun w => (u ∘ baseProjection) w * (auxProfile ∘ auxiliaryProjection) w) z = _
  rw [coordDeriv_mul_at (hu.comp z baseProjection.differentiableAt)
    (hφ.comp z auxiliaryProjection.differentiableAt),
    coordDeriv_baseComp_base hu i, coordDeriv_auxComp_base hφ i, mul_zero, add_zero]
  rfl

private theorem coordDeriv_lifted_aux {u : X n → ℝ} {z : X (n+3)}
    (hu : DifferentiableAt ℝ u (baseProjection z)) (i : I 3) :
    coordDeriv (i.natAdd n) (liftedFunction u) z =
      u (baseProjection z) * ![auxProfile (auxiliaryProjection z),
        auxProfileS (auxiliaryProjection z), 0] i := by
  have hφ : DifferentiableAt ℝ auxProfile (auxiliaryProjection z) :=
    (auxProfile_smooth.differentiable (by simp)).differentiableAt
  change coordDeriv _ (fun w => (u ∘ baseProjection) w * (auxProfile ∘ auxiliaryProjection) w) z = _
  rw [coordDeriv_mul_at (hu.comp z baseProjection.differentiableAt)
    (hφ.comp z auxiliaryProjection.differentiableAt),
    coordDeriv_baseComp_aux hu i, coordDeriv_auxComp_aux hφ i, coordDeriv_auxProfile, zero_mul, zero_add]
  rfl

private theorem augmentedInverse_base_base (L : ScalarElliptic n) (x : X n) (i j : I n) :
    L.augmentedInverse x (i.castAdd 3) (j.castAdd 3) = L.principalMatrix x i j := by
  change schurDetOne _ _ _ _ (finSumFinEquiv.symm (i.castAdd 3))
    (finSumFinEquiv.symm (j.castAdd 3)) = _
  simp only [finSumFinEquiv_symm_apply_castAdd, schurDetOne, fromBlocks_apply₁₁]

private theorem augmentedInverse_base_aux (L : ScalarElliptic n) (x : X n) (i : I n) (k : I 3) :
    L.augmentedInverse x (i.castAdd 3) (k.natAdd n) = L.mixedBlock x i k := by
  change schurDetOne _ _ _ _ (finSumFinEquiv.symm (i.castAdd 3))
    (finSumFinEquiv.symm (k.natAdd n)) = _
  simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    schurDetOne, fromBlocks_apply₁₂]

private theorem augmentedInverse_aux_base (L : ScalarElliptic n) (x : X n) (i : I 3) (k : I n) :
    L.augmentedInverse x (i.natAdd n) (k.castAdd 3) = L.mixedBlock x k i := by
  change schurDetOne _ _ _ _ (finSumFinEquiv.symm (i.natAdd n))
    (finSumFinEquiv.symm (k.castAdd 3)) = _
  simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    schurDetOne, fromBlocks_apply₂₁, conjTranspose_apply, star_trivial]

private theorem mixedQuadratic_aux (L : ScalarElliptic n) (x : X n) (i j : I 3) :
    ((L.mixedBlock x)ᴴ * (L.principalMatrix x)⁻¹ * L.mixedBlock x) i j =
      if i = 0 ∧ j = 0 then L.driftSquare x else 0 := by
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      simp [driftSquare]
    · simp [Matrix.mul_apply, mixedBlock, hj]
  · simp [Matrix.mul_apply, mixedBlock, hi]

private theorem augmentedInverse_aux_aux (L : ScalarElliptic n) (x : X n) (i j : I 3) :
    L.augmentedInverse x (i.natAdd n) (j.natAdd n) =
      Matrix.diagonal ![L.auxT x, L.auxS x,
        ((L.principalMatrix x).det * L.schurT x * L.auxS x)⁻¹] i j := by
  change schurDetOne _ _ _ _ (finSumFinEquiv.symm (i.natAdd n))
    (finSumFinEquiv.symm (j.natAdd n)) = _
  simp only [finSumFinEquiv_symm_apply_natAdd, schurDetOne, fromBlocks_apply₂₂,
    Matrix.add_apply, mixedQuadratic_aux]
  fin_cases i <;> fin_cases j <;> simp [auxT]

private def baseFlux (L : ScalarElliptic n) (u : X n → ℝ) (i : I n) (x : X n) : ℝ :=
  (∑ j, L.principalMatrix x i j * coordDeriv j u x) + L.halfDrift i x * u x

private def tFlux (L : ScalarElliptic n) (u : X n → ℝ) (x : X n) : ℝ :=
  (∑ j, L.halfDrift j x * coordDeriv j u x) + L.auxT x * u x

private def sFlux (L : ScalarElliptic n) (u : X n → ℝ) (x : X n) : ℝ :=
  L.auxS x * u x

private theorem augmented_flux_base {L : ScalarElliptic n} {D : Set (X n)}
    (hL : L.SmoothOn D) {u : X n → ℝ} {z : X (n+3)} (hz : baseProjection z ∈ D)
    (hu : DifferentiableAt ℝ u (baseProjection z)) (i : I n) :
    divergenceFlux L.augmentedMetric (liftedFunction u) z (i.castAdd 3) =
      baseFlux L u i (baseProjection z) * auxProfile (auxiliaryProjection z) := by
  simp only [divergenceFlux, divergenceCoeff, augmentedMetric_volume hL hz, one_mul,
    augmentedMetric_inverse hL hz]
  rw [Fin.sum_univ_add]
  simp_rw [coordDeriv_lifted_base hu, coordDeriv_lifted_aux hu, augmentedInverse_base_base,
    augmentedInverse_base_aux]
  rw [Fin.sum_univ_three]
  simp only [mixedBlock, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Fin.isValue, Fin.reduceEq, zero_mul, add_zero, baseFlux, add_mul, Finset.sum_mul, mul_assoc]

private theorem augmented_flux_aux {L : ScalarElliptic n} {D : Set (X n)}
    (hL : L.SmoothOn D) {u : X n → ℝ} {z : X (n+3)} (hz : baseProjection z ∈ D)
    (hu : DifferentiableAt ℝ u (baseProjection z)) (i : I 3) :
    divergenceFlux L.augmentedMetric (liftedFunction u) z (i.natAdd n) =
      ![tFlux L u (baseProjection z) * auxProfile (auxiliaryProjection z),
        sFlux L u (baseProjection z) * auxProfileS (auxiliaryProjection z), 0] i := by
  simp only [divergenceFlux, divergenceCoeff, augmentedMetric_volume hL hz, one_mul,
    augmentedMetric_inverse hL hz]
  rw [Fin.sum_univ_add]
  simp_rw [coordDeriv_lifted_base hu, coordDeriv_lifted_aux hu, augmentedInverse_aux_base,
    augmentedInverse_aux_aux]
  rw [Fin.sum_univ_three]
  fin_cases i <;> simp [mixedBlock, tFlux, sFlux, add_mul, Finset.sum_mul, mul_assoc]

private theorem coordDeriv_baseFlux {L : ScalarElliptic n} {D : Set (X n)} (hD : IsOpen D)
    (hL : L.SmoothOn D) {u : X n → ℝ} (hu : ContDiffOn ℝ ∞ u D) {x : X n}
    (hx : x ∈ D) (i : I n) :
    coordDeriv i (baseFlux L u i) x =
      (∑ j, L.principalMatrix x i j * coordDeriv i (coordDeriv j u) x) +
      (∑ j, coordDeriv i (fun z => L.principalMatrix z i j) x * coordDeriv j u x) +
      (L.halfDrift i x * coordDeriv i u x + coordDeriv i (L.halfDrift i) x * u x) := by
  have hu₀ := (hu.differentiableOn (by simp)).differentiableAt (hD.mem_nhds hx)
  have hu₁ (j : I n) :=
    ((contDiffOn_coordDeriv hu hD j).differentiableOn (by simp)).differentiableAt (hD.mem_nhds hx)
  have hA (j : I n) :=
    ((contDiffOn_metric_inv_entry hL.1 i j).differentiableOn (by simp)).differentiableAt
      (hD.mem_nhds hx)
  have hq := ((halfDrift_smooth hD hL i).differentiableOn (by simp)).differentiableAt
    (hD.mem_nhds hx)
  let f (j : I n) (z : X n) := L.principalMatrix z i j * coordDeriv j u z
  let g (z : X n) := L.halfDrift i z * u z
  have hf (j : I n) : DifferentiableAt ℝ (f j) x := (hA j).mul (hu₁ j)
  have hg : DifferentiableAt ℝ g x := hq.mul hu₀
  have hDeriv (j : I n) : coordDeriv i (f j) x =
      L.principalMatrix x i j * coordDeriv i (coordDeriv j u) x +
        coordDeriv i (fun z => L.principalMatrix z i j) x * coordDeriv j u x := by
    exact (coordDeriv_mul_at (hA j) (hu₁ j) i).trans (add_comm _ _)
  have hDerivG : coordDeriv i g x =
      L.halfDrift i x * coordDeriv i u x + coordDeriv i (L.halfDrift i) x * u x :=
    (coordDeriv_mul_at hq hu₀ i).trans (add_comm _ _)
  change fderiv ℝ (fun z => (∑ j, f j z) + g z) x (axis i) = _
  rw [fderiv_fun_add (DifferentiableAt.fun_sum fun j _ => hf j) hg,
    fderiv_fun_sum (fun j _ => hf j)]
  simp only [_root_.add_apply, _root_.sum_apply]
  change (∑ j, coordDeriv i (f j) x) + coordDeriv i g x = _
  simp only [hDeriv, hDerivG, Finset.sum_add_distrib]

private theorem divergence_baseAux {L : ScalarElliptic n} {D : Set (X n)} (hD : IsOpen D)
    (hL : L.SmoothOn D) {u : X n → ℝ} (hu : ContDiffOn ℝ ∞ u D) {x : X n}
    (hx : x ∈ D) :
    (∑ i, coordDeriv i (baseFlux L u i) x) + tFlux L u x - sFlux L u x = L.apply u x := by
  have hdiv : (∑ i : I n, ∑ j, coordDeriv i (fun z => L.principalMatrix z i j) x *
      coordDeriv j u x) = ∑ j, L.matrixDiv j x * coordDeriv j u x := by
    rw [Finset.sum_comm]
    simp only [matrixDiv, Finset.sum_mul]
  have hdrift : (∑ j, L.matrixDiv j x * coordDeriv j u x) +
      (∑ j, L.halfDrift j x * coordDeriv j u x) +
      (∑ j, L.halfDrift j x * coordDeriv j u x) =
      ∑ j, L.first x j * coordDeriv j u x := by
    simp_rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by unfold halfDrift; ring
  have hzero : (∑ j, coordDeriv j (L.halfDrift j) x * u x) +
      L.auxT x * u x - L.auxS x * u x = L.zeroth x * u x := by
    rw [← Finset.sum_mul]
    unfold auxS remainingPotential
    ring
  calc
    _ = (∑ i, ∑ j, L.principalMatrix x i j * coordDeriv i (coordDeriv j u) x) +
        (∑ i, L.first x i * coordDeriv i u x) + L.zeroth x * u x := by
      simp only [coordDeriv_baseFlux hD hL hu hx, Finset.sum_add_distrib, hdiv, tFlux, sFlux]
      linarith only [hdrift, hzero]
    _ = L.apply u x := by rfl

/-- The determinant-one auxiliary metric realizes the full scalar
operator, including its independent first and zeroth order terms. -/
theorem laplace_liftedFunction {L : ScalarElliptic n} {D : Set (X n)}
    (hD : IsOpen D) (hL : L.SmoothOn D) {u : X n → ℝ} (hu : ContDiffOn ℝ ∞ u D)
    {z : X (n+3)} (hz : baseProjection z ∈ D) :
    laplace L.augmentedMetric (liftedFunction u) z =
      L.apply u (baseProjection z) * auxProfile (auxiliaryProjection z) := by
  have hU : IsOpen (baseProjection ⁻¹' D) := hD.preimage baseProjection.continuous
  have hu₀ (w : X (n+3)) (hw : w ∈ baseProjection ⁻¹' D) :
      DifferentiableAt ℝ u (baseProjection w) :=
    (hu.differentiableOn (by simp)).differentiableAt (hD.mem_nhds hw)
  have hu₁ (j : I n) := contDiffOn_coordDeriv hu hD j
  have hφ : DifferentiableAt ℝ auxProfile (auxiliaryProjection z) :=
    (auxProfile_smooth.differentiable (by simp)).differentiableAt
  have hψ : DifferentiableAt ℝ auxProfileS (auxiliaryProjection z) :=
    (auxProfileS_smooth.differentiable (by simp)).differentiableAt
  have hb (i : I n) : DifferentiableAt ℝ (baseFlux L u i) (baseProjection z) := by
    apply (ContDiffOn.differentiableOn (n := ∞) (by
      unfold baseFlux
      exact (ContDiffOn.sum fun j _ => (contDiffOn_metric_inv_entry hL.1 i j).mul (hu₁ j)).add
        ((halfDrift_smooth hD hL i).mul hu)) (by simp)).differentiableAt (hD.mem_nhds hz)
  have ht : DifferentiableAt ℝ (tFlux L u) (baseProjection z) := by
    apply (ContDiffOn.differentiableOn (n := ∞) (by
      unfold tFlux auxT
      exact (ContDiffOn.sum fun j _ => (halfDrift_smooth hD hL j).mul (hu₁ j)).add
        (((mixedQuadratic_smooth hD hL 0 0).add (schurT_smooth hD hL)).mul hu))
      (by simp)).differentiableAt (hD.mem_nhds hz)
  have hs : DifferentiableAt ℝ (sFlux L u) (baseProjection z) :=
    (((auxS_smooth hD hL).mul hu).differentiableOn (by simp)).differentiableAt (hD.mem_nhds hz)
  let Φ := auxProfile ∘ auxiliaryProjection (n := n)
  let Ψ := auxProfileS ∘ auxiliaryProjection (n := n)
  have hbase (i : I n) :
      coordDeriv (i.castAdd 3) (fun w => divergenceFlux L.augmentedMetric (liftedFunction u) w
          (i.castAdd 3)) z =
        coordDeriv i (baseFlux L u i) (baseProjection z) * Φ z := by
    have heq : EqOn (fun w => divergenceFlux L.augmentedMetric (liftedFunction u) w (i.castAdd 3))
        (fun w => (baseFlux L u i ∘ baseProjection) w * Φ w) (baseProjection ⁻¹' D) :=
      fun w hw => augmented_flux_base hL hw (hu₀ w hw) i
    rw [eqOn_coordDeriv hU heq _ hz, coordDeriv_mul_at ((hb i).comp z baseProjection.differentiableAt)
      (hφ.comp z auxiliaryProjection.differentiableAt),
      coordDeriv_baseComp_base (hb i), coordDeriv_auxComp_base hφ, mul_zero, add_zero]
  have haux (i : I 3) :
      coordDeriv (i.natAdd n) (fun w => divergenceFlux L.augmentedMetric (liftedFunction u) w
          (i.natAdd n)) z =
        ![tFlux L u (baseProjection z) * Φ z, -(sFlux L u (baseProjection z) * Φ z), 0] i := by
    have heq : EqOn (fun w => divergenceFlux L.augmentedMetric (liftedFunction u) w (i.natAdd n))
        (fun w => ![(tFlux L u ∘ baseProjection) w * Φ w,
          (sFlux L u ∘ baseProjection) w * Ψ w, 0] i) (baseProjection ⁻¹' D) :=
      fun w hw => augmented_flux_aux hL hw (hu₀ w hw) i
    rw [eqOn_coordDeriv hU heq _ hz]
    fin_cases i
    · change coordDeriv ((0 : I 3).natAdd n) (fun w => (tFlux L u ∘ baseProjection) w * Φ w) z = _
      rw [coordDeriv_mul_at (ht.comp z baseProjection.differentiableAt)
        (hφ.comp z auxiliaryProjection.differentiableAt),
        coordDeriv_baseComp_aux ht, coordDeriv_auxComp_aux hφ, zero_mul, zero_add,
        coordDeriv_auxProfile]
      rfl
    · change coordDeriv ((1 : I 3).natAdd n) (fun w => (sFlux L u ∘ baseProjection) w * Ψ w) z = _
      rw [coordDeriv_mul_at (hs.comp z baseProjection.differentiableAt)
        (hψ.comp z auxiliaryProjection.differentiableAt),
        coordDeriv_baseComp_aux hs, coordDeriv_auxComp_aux hψ, zero_mul, zero_add,
        coordDeriv_auxProfileS_one]
      simp [Φ, mul_neg]
    · change coordDeriv ((2 : I 3).natAdd n) (fun _ => (0 : ℝ)) z = 0
      simp [coordDeriv]
  have hLap := chartVolume_mul_laplace_eq_divergence hU (augmentedMetric_smooth hD hL)
    (liftedFunction_smooth hu) (y := z) hz
  rw [augmentedMetric_volume hL hz, one_mul, Fin.sum_univ_add] at hLap
  simp_rw [hbase, haux] at hLap
  rw [Fin.sum_univ_three] at hLap
  rw [hLap]
  change (∑ i, coordDeriv i (baseFlux L u i) (baseProjection z) * Φ z) +
      (tFlux L u (baseProjection z) * Φ z + -(sFlux L u (baseProjection z) * Φ z) + 0) = _
  rw [← Finset.sum_mul]
  change _ = L.apply u (baseProjection z) * Φ z
  calc
    _ = ((∑ i, coordDeriv i (baseFlux L u i) (baseProjection z)) +
        tFlux L u (baseProjection z) - sFlux L u (baseProjection z)) * Φ z := by ring
    _ = _ := congrArg (fun a : ℝ => a * Φ z) (divergence_baseAux hD hL hu hz)

end CalderonPaper.ScalarElliptic

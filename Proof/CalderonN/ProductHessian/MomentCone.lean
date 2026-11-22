module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Topology.Algebra.Module.Star
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact

/-! Adapted from `Calderon/StrictWeightMomentCone.lean` at d6704c49395a38eb07e0249afeb8ea83d67971cc
in the earlier anisotropic Calderón formalization. -/

@[expose] public section

/-! Native physical-coordinate factor moment cones for the original product Hessian split.
The product covariance/rank-one/K/native endpoint remains a separate explicit remainder. -/
set_option autoImplicit false
noncomputable section
open Set Metric Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
namespace CalderonN.ProductHessianSeparation

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

local notation "FactorVector" => (Fin dim → ℝ)
local notation "FactorMatrix" => Matrix (Fin dim) (Fin dim) ℝ
local notation "FactorSelfAdjoint" => selfAdjoint (Matrix (Fin dim) (Fin dim) ℝ)

def metricTangentSphere (G : FactorMatrix) (ell a : FactorVector) : Set FactorVector :=
  {v | dotProduct ell v = 0 ∧
    dotProduct v (G *ᵥ v) = dotProduct a (G *ᵥ a)}

def strictSphereCone (G : FactorMatrix) (ell a : FactorVector) : Set FactorSelfAdjoint :=
  {P | ∀ v ∈ metricTangentSphere G ell a,
    0 < dotProduct a ((P : FactorMatrix) *ᵥ a) + dotProduct v ((P : FactorMatrix) *ᵥ v)}

def metricMomentCondition (G : FactorMatrix) (ell a : FactorVector) (D : FactorMatrix) : Prop :=
  let d : ℝ := dotProduct ell (D *ᵥ ell)
  let S : FactorMatrix := D - d • Matrix.vecMulVec a a
  D.IsHermitian ∧ 0 ≤ d ∧ S.PosSemidef ∧ S *ᵥ ell = 0 ∧
    Matrix.trace (G * S) = d * dotProduct a (G *ᵥ a)

theorem exists_unique_selfAdjoint_trace_pairing
    {n : Type*} [Fintype n] [DecidableEq n]
    (f : selfAdjoint (Matrix n n ℝ) →L[ℝ] ℝ) :
    ∃! D : selfAdjoint (Matrix n n ℝ),
      ∀ P : selfAdjoint (Matrix n n ℝ),
        f P = Matrix.trace ((P : Matrix n n ℝ) * (D : Matrix n n ℝ)) := by
  classical
  let q : Matrix n n ℝ →L[ℝ] selfAdjoint (Matrix n n ℝ) :=
    selfAdjointPartL ℝ (Matrix n n ℝ)
  let F : Matrix n n ℝ →L[ℝ] ℝ := f.comp q
  let c : Matrix n n ℝ := Matrix.of fun i j => F (Matrix.single i j 1)
  have hq (A : Matrix n n ℝ) :
      (q A : Matrix n n ℝ) = (2 : ℝ)⁻¹ • (A + Aᴴ) := by
    change (selfAdjointPart ℝ A : Matrix n n ℝ) = (2 : ℝ)⁻¹ • (A+Aᴴ)
    simp only [selfAdjointPart_apply_coe,invOf_eq_inv,Matrix.star_eq_conjTranspose]
  have hqSingle (i j : n) : q (Matrix.single i j 1) = q (Matrix.single j i 1) := by
    apply Subtype.ext
    rw [hq,hq,Matrix.conjTranspose_single,Matrix.conjTranspose_single]
    simp only [star_one]
    rw [add_comm]
  have hc (i j : n) : c j i = c i j := by
    change f (q (Matrix.single j i 1)) = f (q (Matrix.single i j 1))
    rw [hqSingle j i]
  have hcHermitian : c.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simpa only [star_trivial] using hc i j
  let D : selfAdjoint (Matrix n n ℝ) := ⟨c,hcHermitian⟩
  have hF (A : Matrix n n ℝ) :
      F A = ∑ i : n, ∑ j : n, A i j * F (Matrix.single i j 1) := by
    calc
      F A = F (∑ i : n, ∑ j : n, Matrix.single i j (A i j)) := by
        rw [← Matrix.matrix_eq_sum_single A]
      _ = ∑ i : n, ∑ j : n, A i j * F (Matrix.single i j 1) := by
        simp only [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        have hSingle : Matrix.single i j (A i j) =
            (A i j) • Matrix.single i j (1 : ℝ) := by
          rw [Matrix.smul_single]
          simp only [smul_eq_mul,mul_one]
        rw [hSingle,map_smul]
        rfl
  have hRep (P : selfAdjoint (Matrix n n ℝ)) :
      f P = Matrix.trace ((P : Matrix n n ℝ) * c) := by
    have hqP : q (P : Matrix n n ℝ) = P := P.2.selfAdjointPart_apply ℝ
    calc
      f P = F (P : Matrix n n ℝ) := by
        change f P = f (q (P : Matrix n n ℝ))
        rw [hqP]
      _ = ∑ i : n, ∑ j : n, (P : Matrix n n ℝ) i j * c i j := hF _
      _ = Matrix.trace ((P : Matrix n n ℝ) * c) := by
        simp only [Matrix.trace,Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change (P : Matrix n n ℝ) i j*c i j = (P : Matrix n n ℝ) i j*c j i
        rw [hc i j]
  have hTraceSingle (P : selfAdjoint (Matrix n n ℝ)) (i j : n) :
      Matrix.trace ((q (Matrix.single i j 1) : Matrix n n ℝ) * (P : Matrix n n ℝ)) =
        (P : Matrix n n ℝ) i j := by
    rw [hq,Matrix.conjTranspose_single]
    simp only [star_one,Matrix.smul_mul,Matrix.add_mul,Matrix.trace_smul,
      Matrix.trace_add,Matrix.trace_single_mul,smul_eq_mul,one_mul]
    have hSym : (P : Matrix n n ℝ) j i = (P : Matrix n n ℝ) i j := by
      exact P.2.isHermitian.isSymm.apply i j
    rw [hSym]
    ring
  refine ⟨D,hRep,?_⟩
  intro D' hD'
  apply Subtype.ext
  ext i j
  have h := (hD' (q (Matrix.single i j 1))).symm.trans (hRep (q (Matrix.single i j 1)))
  change Matrix.trace ((q (Matrix.single i j 1) : Matrix n n ℝ)*(D' : Matrix n n ℝ)) =
    Matrix.trace ((q (Matrix.single i j 1) : Matrix n n ℝ)*(D : Matrix n n ℝ)) at h
  rw [hTraceSingle D' i j,hTraceSingle D i j] at h
  exact h

private theorem quadratic_smul (G : FactorMatrix) (t : ℝ) (v : FactorVector) :
    dotProduct (t • v) (G *ᵥ (t • v)) = t^2 * dotProduct v (G *ᵥ v) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, dotProduct_comm (t • v) (G *ᵥ v),
    dotProduct_smul, dotProduct_comm (G *ᵥ v) v]
  ring

private theorem vecMulVec_self_quad (ell v : FactorVector) :
    dotProduct ell (Matrix.vecMulVec v v *ᵥ ell) = (dotProduct ell v)^2 := by
  simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, pow_two, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem vecMulVec_self_kernel (ell v : FactorVector)
    (hv : dotProduct ell v = 0) : Matrix.vecMulVec v v *ᵥ ell = 0 := by
  ext i
  have he : (Matrix.vecMulVec v v *ᵥ ell) i = v i * dotProduct ell v := by
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [he, hv, mul_zero]
  rfl

theorem metricMomentCondition_iff_sum_generators
    (G : FactorMatrix) (hG : G.PosDef) (ell a : FactorVector) (ha : dotProduct ell a = 1) (D : FactorMatrix) :
    metricMomentCondition G ell a D ↔
      ∃ (w : Fin dim → ℝ) (v : Fin dim → FactorVector),
        (∀ j, 0 ≤ w j) ∧ (∀ j, v j ∈ metricTangentSphere G ell a) ∧
        (∑ j, w j) = dotProduct ell (D *ᵥ ell) ∧
        D = ∑ j, w j • (Matrix.vecMulVec a a + Matrix.vecMulVec (v j) (v j)) := by
  classical
  let A : ℝ := dotProduct a (G *ᵥ a)
  have haNe : a ≠ 0 := by
    intro h
    simp only [h,dotProduct_zero] at ha
    norm_num at ha
  have hA : 0 < A := by
    simpa only [A,star_trivial] using hG.dotProduct_mulVec_pos haNe
  have hRankPSD (v : FactorVector) : (Matrix.vecMulVec v v).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star v
  have hRankTrace (v : FactorVector) :
      Matrix.trace (G * Matrix.vecMulVec v v) = dotProduct v (G *ᵥ v) := by
    rw [Matrix.mul_vecMulVec,Matrix.trace_vecMulVec]
    exact dotProduct_comm _ _
  have hRankQuad (v : FactorVector) :
      dotProduct ell (Matrix.vecMulVec v v *ᵥ ell) = (dotProduct ell v)^2 :=
    vecMulVec_self_quad ell v
  have hRankKer (v : FactorVector) (hv : dotProduct ell v = 0) :
      Matrix.vecMulVec v v *ᵥ ell = 0 := vecMulVec_self_kernel ell v hv
  constructor
  · intro hMoment
    let d : ℝ := dotProduct ell (D *ᵥ ell)
    let S : FactorMatrix := D - d • Matrix.vecMulVec a a
    change D.IsHermitian ∧ 0 ≤ d ∧ S.PosSemidef ∧ S *ᵥ ell = 0 ∧
      Matrix.trace (G*S) = d*A at hMoment
    obtain ⟨hDH,hd,hS,hKer,hTrace⟩ := hMoment
    have hEllNe : ell ≠ 0 := by
      intro h
      simp only [h,zero_dotProduct] at ha
      norm_num at ha
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hEllNe
    have hi' : ell i ≠ 0 := hi
    obtain ⟨j,hji⟩ := exists_ne i
    let e : FactorVector := fun k => if k=j then ell i else if k=i then -ell j else 0
    have heEll : dotProduct ell e = 0 := by
      have hE : e = ell i • Pi.single j (1 : ℝ) - ell j • Pi.single i 1 := by
        ext k
        by_cases hkj : k=j
        · subst k
          simp [e,hji,hji.symm]
        · by_cases hki : k=i
          · subst k
            simp [e,hji,hji.symm]
          · simp [e,hkj,hki]
      rw [hE]
      simp only [dotProduct_sub,dotProduct_smul,dotProduct_single_one,smul_eq_mul]
      ring
    have heNe : e ≠ 0 := by
      intro h
      have hj : ell i = 0 := by
        simpa only [e,if_pos rfl,Pi.zero_apply] using congrFun h j
      exact hi' hj
    have heG : 0 < dotProduct e (G *ᵥ e) := by
      simpa only [star_trivial] using hG.dotProduct_mulVec_pos heNe
    let vstar : FactorVector := Real.sqrt (A/dotProduct e (G *ᵥ e)) • e
    have hVstar : vstar ∈ metricTangentSphere G ell a := by
      refine ⟨?_,?_⟩
      · simp only [vstar,dotProduct_smul,smul_eq_mul,heEll,mul_zero]
      · have hScale : dotProduct vstar (G *ᵥ vstar) =
            (Real.sqrt (A/dotProduct e (G *ᵥ e)))^2 * dotProduct e (G *ᵥ e) := by
          exact quadratic_smul G _ e
        rw [hScale,Real.sq_sqrt (div_nonneg hA.le heG.le),div_mul_cancel₀ _ heG.ne']
    let lam : Fin dim → ℝ := hS.isHermitian.eigenvalues
    let u : Fin dim → FactorVector := fun k => (hS.isHermitian.eigenvectorBasis k : FactorVector)
    have hLam (k : Fin dim) : 0 ≤ lam k := hS.eigenvalues_nonneg k
    have hUne (k : Fin dim) : u k ≠ 0 := by
      intro h
      apply hS.isHermitian.eigenvectorBasis.orthonormal.ne_zero k
      apply PiLp.ext
      intro i
      exact congrFun h i
    have hEig (k : Fin dim) : S *ᵥ u k = lam k • u k :=
      hS.isHermitian.mulVec_eigenvectorBasis k
    have hUG (k : Fin dim) : 0 < dotProduct (u k) (G *ᵥ u k) := by
      simpa only [star_trivial] using hG.dotProduct_mulVec_pos (hUne k)
    have hUEll (k : Fin dim) (hk : 0 < lam k) : dotProduct ell (u k) = 0 := by
      have hComm := hS.isHermitian.star_dotProduct_mulVec_comm ell (u k)
      simp only [star_trivial,hKer,dotProduct_zero] at hComm
      rw [hEig,dotProduct_smul,smul_eq_mul] at hComm
      exact (mul_eq_zero.mp hComm).resolve_left hk.ne'
    have hSEntry (i j : Fin dim) : S i j = ∑ k, lam k * u k i * u k j := by
      have hSpec := hS.isHermitian.spectral_theorem
      rw [hSpec]
      simp only [Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
        Matrix.mul_apply,Matrix.diagonal_apply,Matrix.of_apply,Matrix.conjTranspose_apply,star_trivial,
        Matrix.IsHermitian.eigenvectorUnitary_apply,RCLike.ofReal_real_eq_id,
        Function.comp_apply,id_eq,lam,u]
      norm_num
      exact Finset.sum_congr rfl fun k _ => by ring
    have hSpectral : S = ∑ k, lam k • Matrix.vecMulVec (u k) (u k) := by
      ext i j
      simpa only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
        Matrix.vecMulVec_apply,mul_assoc] using hSEntry i j
    have hTraceSpectral : Matrix.trace (G*S) =
        ∑ k, lam k * dotProduct (u k) (G *ᵥ u k) := by
      rw [hSpectral]
      simp only [Matrix.mul_sum,Matrix.mul_smul,Matrix.trace_sum,
        Matrix.trace_smul,smul_eq_mul,hRankTrace]
    let w : Fin dim → ℝ := fun k => lam k * dotProduct (u k) (G *ᵥ u k) / A
    let v : Fin dim → FactorVector := fun k => if 0 < lam k then
      Real.sqrt (A/dotProduct (u k) (G *ᵥ u k)) • u k else vstar
    have hw (k : Fin dim) : 0 ≤ w k :=
      div_nonneg (mul_nonneg (hLam k) (hUG k).le) hA.le
    have hv (k : Fin dim) : v k ∈ metricTangentSphere G ell a := by
      by_cases hk : 0 < lam k
      · rw [show v k = Real.sqrt (A/dotProduct (u k) (G *ᵥ u k)) • u k from if_pos hk]
        refine ⟨?_,?_⟩
        · simp only [dotProduct_smul,smul_eq_mul,hUEll k hk,mul_zero]
        · have hScale (t : ℝ) : dotProduct (t • u k) (G *ᵥ (t • u k)) =
              t^2 * dotProduct (u k) (G *ᵥ u k) := by
            exact quadratic_smul G t (u k)
          rw [hScale,Real.sq_sqrt (div_nonneg hA.le (hUG k).le),
            div_mul_cancel₀ _ (hUG k).ne']
      · simpa only [v,if_neg hk] using hVstar
    have hCov (k : Fin dim) :
        w k • Matrix.vecMulVec (v k) (v k) = lam k • Matrix.vecMulVec (u k) (u k) := by
      by_cases hk : 0 < lam k
      · have hFactor : w k * (Real.sqrt (A/dotProduct (u k) (G *ᵥ u k)))^2 = lam k := by
          rw [Real.sq_sqrt (div_nonneg hA.le (hUG k).le)]
          dsimp only [w]
          field_simp [hA.ne',(hUG k).ne']
          <;> ring
        ext i j
        change w k * (v k i * v k j) = lam k * (u k i * u k j)
        rw [show v k = Real.sqrt (A/dotProduct (u k) (G *ᵥ u k)) • u k from if_pos hk]
        simp only [Pi.smul_apply,smul_eq_mul]
        calc
          w k * ((Real.sqrt (A/dotProduct (u k) (G *ᵥ u k)) * u k i) *
              (Real.sqrt (A/dotProduct (u k) (G *ᵥ u k)) * u k j)) =
              (w k * (Real.sqrt (A/dotProduct (u k) (G *ᵥ u k)))^2) * (u k i*u k j) := by ring
          _ = lam k * (u k i*u k j) := by rw [hFactor]
      · have hZero : lam k = 0 := le_antisymm (le_of_not_gt hk) (hLam k)
        simp only [w,hZero,zero_mul,zero_div,zero_smul]
    have hWeights : ∑ k, w k = d := by
      calc
        ∑ k, w k = (∑ k, lam k * dotProduct (u k) (G *ᵥ u k))/A := by
          simp only [w,Finset.sum_div]
        _ = (d*A)/A := by rw [← hTraceSpectral,hTrace]
        _ = d := mul_div_cancel_right₀ _ hA.ne'
    have hWsum : ∑ k, w k • Matrix.vecMulVec (v k) (v k) = S := by
      rw [hSpectral]
      apply Finset.sum_congr rfl
      intro k _
      exact hCov k
    refine ⟨w,v,hw,hv,hWeights,?_⟩
    rw [show D = d • Matrix.vecMulVec a a + S by dsimp only [S]; abel]
    symm
    calc
      (∑ k, w k • (Matrix.vecMulVec a a + Matrix.vecMulVec (v k) (v k))) =
          (∑ k, w k) • Matrix.vecMulVec a a + ∑ k, w k • Matrix.vecMulVec (v k) (v k) := by
        simp only [smul_add,Finset.sum_add_distrib,Finset.sum_smul]
      _ = d • Matrix.vecMulVec a a + S := by rw [hWeights,hWsum]
  · rintro ⟨w,v,hw,hv,hWeights,hDecomp⟩
    let d : ℝ := dotProduct ell (D *ᵥ ell)
    let S : FactorMatrix := D - d • Matrix.vecMulVec a a
    have hd : d = ∑ k, w k := hWeights.symm
    have hSdecomp : S = ∑ k, w k • Matrix.vecMulVec (v k) (v k) := by
      dsimp only [S]
      rw [hDecomp,hd]
      simp only [smul_add, Finset.sum_add_distrib, Finset.sum_smul]
      abel
    have hPSDsum (f : Fin dim → FactorMatrix) (hf : ∀ k, (f k).PosSemidef)
        (s : Finset (Fin dim)) : (∑ k ∈ s, f k).PosSemidef := by
      classical
      induction s using Finset.induction_on with
      | empty => simpa only [Finset.sum_empty] using Matrix.PosSemidef.zero
      | insert j s hj ih =>
        rw [Finset.sum_insert hj]
        exact (hf j).add ih
    have hDpsd : D.PosSemidef := by
      rw [hDecomp]
      exact hPSDsum _ (fun k => ((hRankPSD a).add (hRankPSD (v k))).smul (hw k)) _
    have hSpsd : S.PosSemidef := by
      rw [hSdecomp]
      exact hPSDsum _ (fun k => (hRankPSD (v k)).smul (hw k)) _
    have hSk : S *ᵥ ell = 0 := by
      rw [hSdecomp, Matrix.sum_mulVec]
      simp_rw [Matrix.smul_mulVec, fun k => hRankKer (v k) (hv k).1, smul_zero]
      simp
    have hSt : Matrix.trace (G*S) = d*A := by
      rw [hSdecomp, Matrix.mul_sum, Matrix.trace_sum, hd, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, hRankTrace, (hv k).2]
    have hdNonneg : 0 ≤ d := by
      rw [hd]
      exact Finset.sum_nonneg (fun k _ => hw k)
    change D.IsHermitian ∧ 0 ≤ d ∧ S.PosSemidef ∧ S *ᵥ ell = 0 ∧
      Matrix.trace (G*S) = d*A
    exact ⟨hDpsd.isHermitian,hdNonneg,hSpsd,hSk,hSt⟩

theorem metricMomentCondition_closed_convex_dual
    (G : FactorMatrix) (hG : G.PosDef) (ell a : FactorVector) (ha : dotProduct ell a = 1) :
    IsClosed {D : FactorSelfAdjoint | metricMomentCondition G ell a (D : FactorMatrix)} ∧
    Convex ℝ {D : FactorSelfAdjoint | metricMomentCondition G ell a (D : FactorMatrix)} ∧
    IsOpen (strictSphereCone G ell a) ∧ Convex ℝ (strictSphereCone G ell a) ∧
    (strictSphereCone G ell a).Nonempty ∧
    (∀ D : FactorSelfAdjoint,
      (∀ P ∈ strictSphereCone G ell a, 0 ≤ Matrix.trace ((P : FactorMatrix) * (D : FactorMatrix))) ↔
        metricMomentCondition G ell a (D : FactorMatrix)) := by
  classical
  letI : ContinuousSMul ℝ FactorSelfAdjoint :=
    Topology.IsInducing.continuousSMul
      (M := ℝ) (X := FactorMatrix) (Y := FactorSelfAdjoint)
      (g := fun D : FactorSelfAdjoint => (D : FactorMatrix)) (f := fun t : ℝ => t)
      Topology.IsInducing.subtypeVal continuous_id (fun {_ _} => rfl)
  letI : LocallyConvexSpace ℝ FactorMatrix :=
    inferInstanceAs (LocallyConvexSpace ℝ (Fin dim → Fin dim → ℝ))
  let coeL : FactorSelfAdjoint →ₗ[ℝ] FactorMatrix :=
    { toFun := fun D : FactorSelfAdjoint => (D : FactorMatrix)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  letI : LocallyConvexSpace ℝ FactorSelfAdjoint :=
    Topology.IsInducing.locallyConvexSpace (f := coeL)
      Topology.IsInducing.subtypeVal
  let A : ℝ := dotProduct a (G *ᵥ a)
  let d : FactorSelfAdjoint → ℝ := fun D => dotProduct ell ((D : FactorMatrix) *ᵥ ell)
  let S : FactorSelfAdjoint → FactorMatrix := fun D => (D : FactorMatrix) - d D • Matrix.vecMulVec a a
  have haNe : a ≠ 0 := by
    intro h
    simp only [h,dotProduct_zero] at ha
    norm_num at ha
  have hA : 0 < A := by
    simpa only [A,star_trivial] using hG.dotProduct_mulVec_pos haNe
  have hRankPSD (v : FactorVector) : (Matrix.vecMulVec v v).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star v
  have hTraceRank (P : FactorMatrix) (v : FactorVector) :
      Matrix.trace (P * Matrix.vecMulVec v v) = dotProduct v (P *ᵥ v) := by
    rw [Matrix.mul_vecMulVec,Matrix.trace_vecMulVec]
    exact dotProduct_comm _ _
  have hMom (D : FactorSelfAdjoint) : metricMomentCondition G ell a (D : FactorMatrix) ↔
      0 ≤ d D ∧ (S D).PosSemidef ∧ S D *ᵥ ell = 0 ∧ Matrix.trace (G*S D) = d D*A := by
    have hHermitian : (D : FactorMatrix).IsHermitian := D.2
    simp only [metricMomentCondition,d,S,A,hHermitian,true_and]
  have hEntry (i j : Fin dim) : Continuous (fun D : FactorSelfAdjoint => (D : FactorMatrix) i j) :=
    Continuous.comp (f := fun D : FactorSelfAdjoint => (D : FactorMatrix))
      (g := fun B : FactorMatrix => B i j) (continuous_apply_apply i j) continuous_subtype_val
  have hdContinuous : Continuous d := by
    have hRow (i : Fin dim) : Continuous (fun D : FactorSelfAdjoint => ∑ j : Fin dim, (D : FactorMatrix) i j*ell j) :=
      continuous_finsetSum Finset.univ (fun j _ => (hEntry i j).mul_const (ell j))
    change Continuous (fun D : FactorSelfAdjoint => ∑ i : Fin dim, ell i*(∑ j : Fin dim, (D : FactorMatrix) i j*ell j))
    exact continuous_finsetSum Finset.univ (fun i _ => (hRow i).const_mul (ell i))
  have hSContinuous : Continuous S := by
    exact continuous_subtype_val.sub (hdContinuous.smul continuous_const)
  have hPSDClosed : IsClosed {T : FactorMatrix | T.PosSemidef} := by
    have hSet : {T : FactorMatrix | T.PosSemidef} =
        {T : FactorMatrix | T.IsHermitian} ∩ ⋂ v : FactorVector, {T : FactorMatrix | 0 ≤ dotProduct v (T *ᵥ v)} := by
      ext T
      simp only [mem_setOf_eq,mem_inter_iff,mem_iInter,
        Matrix.posSemidef_iff_dotProduct_mulVec,star_trivial]
    rw [hSet]
    apply IsClosed.inter
    · change IsClosed {T : FactorMatrix | Tᴴ = T}
      exact isClosed_eq (by fun_prop) continuous_id
    · apply isClosed_iInter
      intro v
      apply isClosed_le continuous_const
      simp only [dotProduct,Matrix.mulVec]
      fun_prop
  have hClosed : IsClosed {D : FactorSelfAdjoint | metricMomentCondition G ell a (D : FactorMatrix)} := by
    have hKernel : IsClosed {D : FactorSelfAdjoint | S D *ᵥ ell = 0} :=
      isClosed_eq (by
        change Continuous (fun D : FactorSelfAdjoint => S D *ᵥ ell)
        apply continuous_pi
        intro i
        have hSentry (j : Fin dim) : Continuous (fun D : FactorSelfAdjoint => S D i j) :=
          Continuous.comp (f := S) (g := fun B : FactorMatrix => B i j)
            (continuous_apply_apply i j) hSContinuous
        change Continuous (fun D : FactorSelfAdjoint => ∑ j, S D i j*ell j)
        fun_prop) continuous_const
    have hTrace : IsClosed {D : FactorSelfAdjoint | Matrix.trace (G*S D) = d D*A} := by
      apply isClosed_eq
      · simp only [Matrix.trace,Matrix.mul_apply]
        fun_prop
      · exact hdContinuous.mul_const A
    have hdNonneg : IsClosed {D : FactorSelfAdjoint | (0 : ℝ) ≤ d D} :=
      isClosed_le (f := fun _ : FactorSelfAdjoint => (0 : ℝ)) (g := d)
        continuous_const hdContinuous
    have hResult := (hdNonneg.inter (hPSDClosed.preimage hSContinuous)).inter
      (hKernel.inter hTrace)
    convert hResult using 1
    ext D
    simp only [mem_setOf_eq,mem_inter_iff,mem_preimage,hMom,and_assoc]
  have hdAdd (D E : FactorSelfAdjoint) : d (D+E) = d D+d E := by
    change dotProduct ell (((D : FactorMatrix)+(E : FactorMatrix))*ᵥ ell) = _
    simp only [Matrix.add_mulVec,dotProduct_add]
    rfl
  have hdSmul (t : ℝ) (D : FactorSelfAdjoint) : d (t • D) = t*d D := by
    change dotProduct ell ((t • (D : FactorMatrix))*ᵥ ell) = _
    simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
    rfl
  have hSAdd (D E : FactorSelfAdjoint) : S (D+E) = S D+S E := by
    dsimp only [S]
    rw [hdAdd]
    ext i j
    change (D : FactorMatrix) i j+(E : FactorMatrix) i j-(d D+d E)*(a i*a j) =
      ((D : FactorMatrix) i j-d D*(a i*a j))+((E : FactorMatrix) i j-d E*(a i*a j))
    ring
  have hSSmul (t : ℝ) (D : FactorSelfAdjoint) : S (t • D) = t • S D := by
    dsimp only [S]
    rw [hdSmul]
    ext i j
    change t*(D : FactorMatrix) i j-(t*d D)*(a i*a j) = t*((D : FactorMatrix) i j-d D*(a i*a j))
    ring
  have hScaleMom (t : ℝ) (ht : 0 ≤ t) (D : FactorSelfAdjoint)
      (hD : metricMomentCondition G ell a (D : FactorMatrix)) :
      metricMomentCondition G ell a ((t • D : FactorSelfAdjoint) : FactorMatrix) := by
    obtain ⟨hd,hPSD,hKer,hTrace⟩ := (hMom D).mp hD
    apply (hMom (t • D)).mpr
    rw [hdSmul,hSSmul]
    refine ⟨mul_nonneg ht hd,hPSD.smul ht,?_,?_⟩
    · simp only [Matrix.smul_mulVec,hKer,smul_zero]
    · rw [Matrix.mul_smul,Matrix.trace_smul,hTrace]
      change t*(d D*A) = (t*d D)*A
      ring
  have hConvex : Convex ℝ {D : FactorSelfAdjoint | metricMomentCondition G ell a (D : FactorMatrix)} := by
    intro D hD E hE t s ht hs hts
    obtain ⟨hdD,hPSDd,hKd,hTd⟩ := (hMom D).mp hD
    obtain ⟨hdE,hPSDe,hKe,hTe⟩ := (hMom E).mp hE
    apply (hMom (t • D+s • E)).mpr
    rw [hdAdd,hdSmul,hdSmul,hSAdd,hSSmul,hSSmul]
    refine ⟨add_nonneg (mul_nonneg ht hdD) (mul_nonneg hs hdE),
      (hPSDd.smul ht).add (hPSDe.smul hs),?_,?_⟩
    · simp only [Matrix.add_mulVec,Matrix.smul_mulVec,hKd,hKe,smul_zero,add_zero]
    · rw [Matrix.mul_add,Matrix.mul_smul,Matrix.mul_smul,Matrix.trace_add,
        Matrix.trace_smul,Matrix.trace_smul,hTd,hTe]
      change t*(d D*A)+s*(d E*A) = (t*d D+s*d E)*A
      ring
  have hZeroMom : metricMomentCondition G ell a ((0 : FactorSelfAdjoint) : FactorMatrix) := by
    simp [metricMomentCondition,Matrix.PosSemidef.zero]
  have hCompactSphere : IsCompact (metricTangentSphere G ell a) := by
    have hQuadContinuous : Continuous (fun v : FactorVector => dotProduct v (G *ᵥ v)) := by
      simp only [dotProduct,Matrix.mulVec]
      fun_prop
    have hPositive (v : FactorVector) (hv : v ≠ 0) : 0 < dotProduct v (G *ᵥ v) := by
      simpa only [star_trivial] using hG.dotProduct_mulVec_pos hv
    obtain ⟨beta,hbeta,hMin⟩ := (isCompact_sphere (0 : FactorVector) 1).exists_forall_le'
      hQuadContinuous.continuousOn (fun v hv => hPositive v (by
        have hn : ‖v‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hv
        intro h
        simp only [h,norm_zero] at hn
        norm_num at hn))
    have hLower (v : FactorVector) : beta*‖v‖^2 ≤ dotProduct v (G *ᵥ v) := by
      by_cases hv : v=0
      · subst v
        simp
      have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
      let w : FactorVector := ‖v‖⁻¹ • v
      have hw : ‖w‖ = 1 := by
        simp only [w,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),
          inv_mul_cancel₀ hn.ne']
      have hMinw := hMin w (by simpa only [Metric.mem_sphere,dist_zero_right] using hw)
      have hBack : ‖v‖ • w = v := by
        simp only [w,smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
      have hScale : dotProduct v (G *ᵥ v) = ‖v‖^2 * dotProduct w (G *ᵥ w) := by
        calc
          _ = dotProduct (‖v‖ • w) (G *ᵥ (‖v‖ • w)) := by rw [hBack]
          _ = _ := quadratic_smul G _ w
      rw [hScale,mul_comm beta (‖v‖^2)]
      exact mul_le_mul_of_nonneg_left hMinw (sq_nonneg ‖v‖)
    have hClosedSphere : IsClosed (metricTangentSphere G ell a) := by
      apply IsClosed.inter
      · apply isClosed_eq
        · change Continuous (fun v : FactorVector => dotProduct ell v)
          simp only [dotProduct]
          fun_prop
        · exact continuous_const
      · exact isClosed_eq hQuadContinuous continuous_const
    have hBound (v : FactorVector) (hv : v ∈ metricTangentSphere G ell a) : ‖v‖ ≤ A/beta+1 := by
      have hL := hLower v
      rw [hv.2] at hL
      have hSq : ‖v‖^2 ≤ A/beta := by
        apply (le_div_iff₀ hbeta).mpr
        simpa only [mul_comm] using hL
      nlinarith only [hSq,sq_nonneg (‖v‖-(1/2 : ℝ))]
    apply isCompact_iff_isClosed_bounded.mpr
    refine ⟨hClosedSphere,?_⟩
    apply (Metric.isBounded_closedBall (x := (0 : FactorVector)) (r := A/beta+1)).subset
    intro v hv
    apply Metric.mem_closedBall.mpr
    simpa only [dist_zero_right] using hBound v hv
  let phi : FactorSelfAdjoint → FactorVector → ℝ := fun P v =>
    dotProduct a ((P : FactorMatrix)*ᵥ a)+dotProduct v ((P : FactorMatrix)*ᵥ v)
  have hJoint : Continuous (fun z : FactorSelfAdjoint × FactorVector => phi z.1 z.2) := by
    have hPentry (i j : Fin dim) : Continuous (fun z : FactorSelfAdjoint × FactorVector => (z.1 : FactorMatrix) i j) :=
      Continuous.comp (f := fun z : FactorSelfAdjoint × FactorVector => z.1)
        (g := fun P : FactorSelfAdjoint => (P : FactorMatrix) i j) (hEntry i j) continuous_fst
    have hVentry (i : Fin dim) : Continuous (fun z : FactorSelfAdjoint × FactorVector => z.2 i) :=
      Continuous.comp (f := fun z : FactorSelfAdjoint × FactorVector => z.2)
        (g := fun v : FactorVector => v i) (continuous_apply i) continuous_snd
    have hFixedRow (i : Fin dim) : Continuous (fun z : FactorSelfAdjoint × FactorVector =>
        ∑ j : Fin dim, (z.1 : FactorMatrix) i j*a j) :=
      continuous_finsetSum Finset.univ (fun j _ => (hPentry i j).mul_const (a j))
    have hMovingRow (i : Fin dim) : Continuous (fun z : FactorSelfAdjoint × FactorVector =>
        ∑ j : Fin dim, (z.1 : FactorMatrix) i j*z.2 j) :=
      continuous_finsetSum Finset.univ (fun j _ => (hPentry i j).mul (hVentry j))
    have hFixed : Continuous (fun z : FactorSelfAdjoint × FactorVector =>
        ∑ i : Fin dim, a i*(∑ j : Fin dim, (z.1 : FactorMatrix) i j*a j)) :=
      continuous_finsetSum Finset.univ (fun i _ => (hFixedRow i).const_mul (a i))
    have hMoving : Continuous (fun z : FactorSelfAdjoint × FactorVector =>
        ∑ i : Fin dim, z.2 i*(∑ j : Fin dim, (z.1 : FactorMatrix) i j*z.2 j)) :=
      continuous_finsetSum Finset.univ (fun i _ => (hVentry i).mul (hMovingRow i))
    change Continuous (fun z : FactorSelfAdjoint × FactorVector =>
      (∑ i : Fin dim, a i*(∑ j : Fin dim, (z.1 : FactorMatrix) i j*a j))+
        ∑ i : Fin dim, z.2 i*(∑ j : Fin dim, (z.1 : FactorMatrix) i j*z.2 j))
    exact hFixed.add hMoving
  have hOpen : IsOpen (strictSphereCone G ell a) := by
    apply isOpen_iff_mem_nhds.mpr
    intro P hP
    have hEach (v : FactorVector) (hv : v ∈ metricTangentSphere G ell a) :
        ∀ᶠ z : FactorSelfAdjoint × FactorVector in 𝓝 (P,v), 0 < phi z.1 z.2 :=
      hJoint.continuousAt.eventually (lt_mem_nhds (hP v hv))
    exact hCompactSphere.eventually_forall_of_forall_eventually hEach
  have hConeConvex : Convex ℝ (strictSphereCone G ell a) := by
    intro P hP Q hQ t s ht hs hts v hv
    have hLinear : phi (t • P+s • Q) v = t*phi P v+s*phi Q v := by
      dsimp only [phi]
      change dotProduct a ((t • (P : FactorMatrix)+s • (Q : FactorMatrix))*ᵥ a)+
        dotProduct v ((t • (P : FactorMatrix)+s • (Q : FactorMatrix))*ᵥ v) = _
      simp only [Matrix.add_mulVec,Matrix.smul_mulVec,dotProduct_add,
        dotProduct_smul,smul_eq_mul]
      ring
    change 0 < phi (t • P+s • Q) v
    rw [hLinear]
    by_cases ht0 : t=0
    · have hs1 : s=1 := by linarith only [hts,ht0]
      simpa only [ht0,hs1,zero_mul,one_mul,zero_add] using hQ v hv
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (lt_of_le_of_ne ht (Ne.symm ht0)) (hP v hv))
        (mul_nonneg hs (hQ v hv).le)
  let I : FactorSelfAdjoint := 1
  have hIdPositive (v : FactorVector) : 0 < phi I v := by
    have hPa : 0 < dotProduct a a := by
      simpa only [star_trivial,Matrix.one_mulVec] using
        (show (1 : FactorMatrix).PosDef from Matrix.PosDef.one).dotProduct_mulVec_pos haNe
    have hPv : 0 ≤ dotProduct v v := by
      simpa only [star_trivial,Matrix.one_mulVec] using
        (show (1 : FactorMatrix).PosSemidef from Matrix.PosSemidef.one).dotProduct_mulVec_nonneg v
    have hI : (I : FactorMatrix) = (1 : FactorMatrix) := rfl
    change 0 < dotProduct a ((I : FactorMatrix) *ᵥ a)+dotProduct v ((I : FactorMatrix) *ᵥ v)
    rw [hI,Matrix.one_mulVec,Matrix.one_mulVec]
    exact add_pos_of_pos_of_nonneg hPa hPv
  have hConeNonempty : (strictSphereCone G ell a).Nonempty :=
    ⟨I,fun v _ => hIdPositive v⟩
  refine ⟨hClosed,hConvex,hOpen,hConeConvex,hConeNonempty,?_⟩
  intro D
  constructor
  · intro hDual
    by_contra hNotMoment
    obtain ⟨f,b,hDb,hSep⟩ := geometric_hahn_banach_point_closed hConvex hClosed hNotMoment
    have hb : b < 0 := by
      simpa only [map_zero] using hSep 0 hZeroMom
    have hfD : f D < 0 := hDb.trans hb
    have hfMoment (E : FactorSelfAdjoint) (hE : metricMomentCondition G ell a (E : FactorMatrix)) : 0 ≤ f E := by
      by_contra h
      have hneg : f E < 0 := lt_of_not_ge h
      let t : ℝ := (b-1)/(f E)
      have ht : 0 < t := div_pos_of_neg_of_neg (by linarith only [hb]) hneg
      have hScaled := hSep (t • E) (hScaleMom t ht.le E hE)
      rw [map_smul] at hScaled
      change b < t*f E at hScaled
      have heq : t*f E = b-1 := div_mul_cancel₀ _ hneg.ne
      rw [heq] at hScaled
      linarith only [hScaled]
    obtain ⟨P,hPair,_⟩ := exists_unique_selfAdjoint_trace_pairing f
    have hTraceD : Matrix.trace ((P : FactorMatrix)*(D : FactorMatrix)) < 0 := by
      rw [Matrix.trace_mul_comm,← hPair D]
      exact hfD
    have hGenMoment (v : FactorVector) (hv : v ∈ metricTangentSphere G ell a) :
        metricMomentCondition G ell a
          (Matrix.vecMulVec a a+Matrix.vecMulVec v v) := by
      have hQ : dotProduct ell ((Matrix.vecMulVec a a+Matrix.vecMulVec v v)*ᵥ ell) = 1 := by
        have hRaw : dotProduct ell ((Matrix.vecMulVec a a+Matrix.vecMulVec v v)*ᵥ ell) =
            (dotProduct ell a)^2+(dotProduct ell v)^2 := by
          rw [Matrix.add_mulVec, dotProduct_add, vecMulVec_self_quad, vecMulVec_self_quad]
        rw [hRaw,ha,hv.1]
        norm_num
      unfold metricMomentCondition
      simp only [hQ,one_smul,add_sub_cancel_left]
      refine ⟨(hRankPSD a).isHermitian.add (hRankPSD v).isHermitian,by norm_num,
        hRankPSD v,?_,?_⟩
      · exact vecMulVec_self_kernel ell v hv.1
      · rw [hTraceRank,hv.2,one_mul]
    have hPnonneg (v : FactorVector) (hv : v ∈ metricTangentSphere G ell a) : 0 ≤ phi P v := by
      let E : FactorSelfAdjoint := ⟨Matrix.vecMulVec a a+Matrix.vecMulVec v v,
        (hRankPSD a).isHermitian.add (hRankPSD v).isHermitian⟩
      have h := hfMoment E (hGenMoment v hv)
      rw [hPair E,Matrix.trace_mul_comm] at h
      simpa only [E,Matrix.mul_add,Matrix.trace_add,hTraceRank,phi] using h
    let eps : ℝ := (-Matrix.trace ((P : FactorMatrix)*(D : FactorMatrix))) /
      (2*(|Matrix.trace (D : FactorMatrix)|+1))
    have hden : 0 < 2*(|Matrix.trace (D : FactorMatrix)|+1) := by positivity
    have heps : 0 < eps := div_pos (neg_pos.mpr hTraceD) hden
    have hEpsEq : eps*(2*(|Matrix.trace (D : FactorMatrix)|+1)) =
        -Matrix.trace ((P : FactorMatrix)*(D : FactorMatrix)) := div_mul_cancel₀ _ hden.ne'
    let Q : FactorSelfAdjoint := P+eps • I
    have hQin : Q ∈ strictSphereCone G ell a := by
      intro v hv
      have hPairQ : phi Q v = phi P v+eps*phi I v := by
        dsimp only [phi,Q]
        change dotProduct a (((P : FactorMatrix)+eps • (I : FactorMatrix))*ᵥ a)+
          dotProduct v (((P : FactorMatrix)+eps • (I : FactorMatrix))*ᵥ v) = _
        simp only [Matrix.add_mulVec,Matrix.smul_mulVec,dotProduct_add,
          dotProduct_smul,smul_eq_mul]
        ring
      change 0 < phi Q v
      rw [hPairQ]
      exact add_pos_of_nonneg_of_pos (hPnonneg v hv) (mul_pos heps (hIdPositive v))
    have hQtrace : Matrix.trace ((Q : FactorMatrix)*(D : FactorMatrix)) =
        Matrix.trace ((P : FactorMatrix)*(D : FactorMatrix))+eps*Matrix.trace (D : FactorMatrix) := by
      change Matrix.trace (((P : FactorMatrix)+eps • (1 : FactorMatrix))*(D : FactorMatrix)) = _
      rw [Matrix.add_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.trace_add,Matrix.trace_smul]
      rfl
    have hAbs : eps*Matrix.trace (D : FactorMatrix) ≤ eps*|Matrix.trace (D : FactorMatrix)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) heps.le
    have hNeg : Matrix.trace ((P : FactorMatrix)*(D : FactorMatrix))+eps*Matrix.trace (D : FactorMatrix) < 0 := by
      have hNonneg := mul_nonneg heps.le (abs_nonneg (Matrix.trace (D : FactorMatrix)))
      nlinarith only [hEpsEq,hAbs,hNonneg,heps]
    have hContradiction := hDual Q hQin
    rw [hQtrace] at hContradiction
    exact (not_lt_of_ge hContradiction) hNeg
  · intro hMoment P hP
    obtain ⟨w,v,hw,hv,hWeights,hDsum⟩ :=
      (metricMomentCondition_iff_sum_generators G hG ell a ha (D : FactorMatrix)).mp hMoment
    rw [hDsum]
    simp only [Matrix.mul_sum,Matrix.mul_smul,Matrix.trace_sum,Matrix.trace_smul,
      smul_eq_mul]
    apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg (hw k)
    simpa only [Matrix.mul_add,Matrix.trace_add,hTraceRank] using (hP (v k) (hv k)).le


end CalderonN.ProductHessianSeparation

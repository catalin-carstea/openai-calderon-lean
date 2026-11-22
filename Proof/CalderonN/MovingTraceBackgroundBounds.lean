module

public import Proof.CalderonN.MovingBallFamilies

import Proof.CalderonN.BackgroundBounds
import Proof.CalderonN.NormalizedMetric
import Proof.CalderonN.ScaledGreenDatumJets
import Proof.CalderonN.MetricCalculus
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic

/-! Adapted from `MovingTraceBackgroundBounds` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1800000

noncomputable section
open Set Metric
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem compact_finite_norm_bound {A F J : Type*} [TopologicalSpace A]
    [NormedAddCommGroup F] [Fintype J] {K : Set A} (hK : IsCompact K)
    (f : J → A → F) (hf : ∀ j, ContinuousOn (f j) K) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ z ∈ K, ∀ j, ‖f j z‖ ≤ B := by
  let L (z : A) := ∑ j, ‖f j z‖
  have hL : ContinuousOn L K := continuousOn_finsetSum _ fun j _ => (hf j).norm
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hL
  refine ⟨max 1 B,le_max_left _ _,fun z hz j => ?_⟩
  have hterm : ‖f j z‖ ≤ L z := Finset.single_le_sum (f := fun j => ‖f j z‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  exact hterm.trans ((le_abs_self _).trans ((hB z hz).trans (le_max_right _ _)))

/-- Uniform principal, Christoffel and drift coefficients for the moving
trace operator on a compact family of centers. -/
theorem exists_uniform_movingTrace_coefficients
    {γ k : ℝ → (MetricField dim)} {S : Set ℝ} {K : Set (X dim)} (hS : IsCompact S) (hK : IsCompact K)
    (hγ : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × (X dim) => γ p.1 p.2 i j))
    (hγPos : ∀ a y, (γ a y).PosDef)
    (hk : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × (X dim) => k p.1 p.2 i j))
    (hkPos : ∀ a y, (k a y).PosDef) :
    ∃ P Γ D : ℝ, 0 ≤ P ∧ 0 ≤ Γ ∧ 0 ≤ D ∧
      ∀ a ∈ S, ∀ y ∈ K,
        (∀ i j, |principal (γ a) (k a) y i j| ≤ P) ∧
        (∀ l i j, |christoffel (γ a) y l i j| ≤ Γ) ∧
        (∀ l, |drift (γ a) (k a) y l| ≤ D) := by
  let C := S ×ˢ K
  have hC : IsCompact C := hS.prod hK
  let P₀ (i : (I dim) × (I dim)) (q : ℝ × (X dim)) := principal (γ q.1) (k q.1) q.2 i.1 i.2
  let Γ₀ (i : (I dim) × ((I dim) × (I dim))) (q : ℝ × (X dim)) := christoffel (γ q.1) q.2 i.1 i.2.1 i.2.2
  let D₀ (i : (I dim)) (q : ℝ × (X dim)) := drift (γ q.1) (k q.1) q.2 i
  have hP₀ (i : (I dim) × (I dim)) : ContDiff ℝ ∞ (P₀ i) := by
    have hkInv (a b : I dim) : ContDiff ℝ ∞ (fun q : ℝ × X dim => (k q.1 q.2)⁻¹ a b) :=
      contDiffOn_univ.mp (contDiffOn_inv_entry_of_entries (fun a b => (hk a b).contDiffOn)
        (fun q _ => (hkPos q.1 q.2).det_pos.ne') a b)
    have hTrace : ContDiff ℝ ∞ (fun q : ℝ × X dim => (γ q.1 q.2 * (k q.1 q.2)⁻¹).trace) := by
      simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
      exact ContDiff.sum fun a _ => ContDiff.sum fun b _ => (hγ a b).mul (hkInv b a)
    change ContDiff ℝ ∞ (fun q : ℝ × X dim =>
      ((dim:ℝ)/(γ q.1 q.2 * (k q.1 q.2)⁻¹).trace) * (k q.1 q.2)⁻¹ i.1 i.2)
    exact (contDiff_const.div hTrace
      (fun q => (trace_mul_pos_of_posDef (hγPos q.1 q.2) (hkPos q.1 q.2).inv).ne')).mul (hkInv i.1 i.2)
  obtain ⟨P,hP,hPb⟩ := compact_finite_norm_bound hC P₀ (fun i => (hP₀ i).continuous.continuousOn)
  obtain ⟨Γ,hΓ,hΓb⟩ := compact_finite_norm_bound hC Γ₀ (fun i =>
    (contDiff_family_christoffel hγ hγPos i.1 i.2.1 i.2.2).continuous.continuousOn)
  obtain ⟨D,hD,hDb⟩ := compact_finite_norm_bound hC D₀ (fun i =>
    (contDiff_family_drift hγ hk hγPos hkPos i).continuous.continuousOn)
  refine ⟨P,Γ,D,zero_le_one.trans hP,zero_le_one.trans hΓ,zero_le_one.trans hD,?_⟩
  intro a ha y hy
  refine ⟨fun i j => ?_,fun l i j => ?_,fun l => ?_⟩
  · simpa only [Real.norm_eq_abs,P₀] using hPb (a,y) ⟨ha,hy⟩ (i,j)
  · simpa only [Real.norm_eq_abs,Γ₀] using hΓb (a,y) ⟨ha,hy⟩ (l,i,j)
  · simpa only [Real.norm_eq_abs,D₀] using hDb (a,y) ⟨ha,hy⟩ l

/-- The horizontal connection direction and the derivatives of the
angular frame are uniformly bounded on the framed compact bundle. -/
theorem exists_uniform_movingTrace_frame_geometry
    {γ : ℝ → (MetricField dim)} {e : ℝ → (Frame dim)} {S : Set ℝ} {K : Set (X dim)}
    (hS : IsCompact S) (hK : IsCompact K)
    (hγ : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × (X dim) => γ p.1 p.2 i j))
    (hγPos : ∀ a y, (γ a y).PosDef)
    (he : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (X dim) => e p.1 p.2 i)) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ a ∈ S, ∀ y ∈ K, ∀ w ∈ (standardSphere dim),
      (∀ i, ‖connection (γ a) y (axis i) (frameVector (e a) y w)‖ ≤ M) ∧
      ‖fderiv ℝ (fun z => (movingBallToFrame (γ a) (e a) z).2)
        (y,frameVector (e a) y w)‖ ≤ M := by
  let H := ℝ × ((X dim) × (X dim))
  let Z := S ×ˢ (K ×ˢ (standardSphere dim))
  have hZ : IsCompact Z := hS.prod (hK.prod (isCompact_sphere (0 : (X dim)) 1))
  let A (q : H) := frameVector (e q.1) q.2.1 q.2.2
  let Φ (q : H) : H := (q.1,(q.2.1,A q))
  let F (q : H) := frameCoordinates (γ q.1) q.2.1 (e q.1 q.2.1) q.2.2
  let U (i : (I dim)) (q : H) := connection (γ q.1) q.2.1 (axis i) (A q)
  have hBase : ContDiff ℝ ∞ (fun q : H => (q.1,q.2.1)) := contDiff_fst.prodMk contDiff_snd.fst
  have hA : ContDiff ℝ ∞ A :=
    contDiff_family_frameVector (fun i => (he i).comp hBase) contDiff_snd.snd
  have hΦ : ContDiff ℝ ∞ Φ := contDiff_fst.prodMk (contDiff_snd.fst.prodMk hA)
  have hF : ContDiff ℝ ∞ F := contDiff_family_frameCoordinates hγ he
  have hU (i : (I dim)) : ContDiff ℝ ∞ (U i) := by
    apply (contDiff_piLp 2).mpr
    intro l
    change ContDiff ℝ ∞ (fun q : H => ∑ j : (I dim), ∑ t : (I dim),
      christoffel (γ q.1) q.2.1 l j t * (axis i) j * A q t)
    exact ContDiff.sum fun j _ => ContDiff.sum fun t _ =>
      (((contDiff_family_christoffel hγ hγPos l j t).comp hBase).mul contDiff_const).mul
        ((EuclideanSpace.proj (𝕜 := ℝ) t).contDiff.comp hA)
  obtain ⟨M,hM,hMb⟩ := compact_finite_norm_bound hZ U (fun i => (hU i).continuous.continuousOn)
  obtain ⟨B,hB⟩ := hZ.exists_bound_of_continuousOn
    (((hF.fderiv_right (m := ∞) (by simp)).continuous.comp hΦ.continuous).continuousOn)
  refine ⟨max M B,hM.trans (le_max_left _ _),fun a ha y hy w hw => ⟨?_,?_⟩⟩
  · exact fun i => (hMb (a,(y,w)) ⟨ha,hy,hw⟩ i).trans (le_max_left _ _)
  · let q := (y,A (a,(y,w)))
    let L := ContinuousLinearMap.inr ℝ ℝ ((X dim) × (X dim))
    have hDer : fderiv ℝ (fun z => (movingBallToFrame (γ a) (e a) z).2) q =
        (fderiv ℝ F (a,q)).comp L := by
      exact (((hF.differentiable (by simp) (a,q)).hasFDerivAt).comp q
        (hasFDerivAt_prodMk_right a q)).fderiv
    change ‖fderiv ℝ (fun z => (movingBallToFrame (γ a) (e a) z).2) q‖ ≤ _
    rw [hDer]
    have hNormL : ‖L‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one _ _ _
    calc
      _ ≤ ‖fderiv ℝ F (a,q)‖ * ‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ F (a,q)‖ := mul_le_of_le_one_right (norm_nonneg _) hNormL
      _ ≤ B := hB (a,(y,w)) ⟨ha,hy,hw⟩
      _ ≤ _ := le_max_right _ _

end CalderonN

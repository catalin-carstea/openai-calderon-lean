module

public import Proof.CalderonN.SmoothNormalJetExtension

import Proof.CalderonN.TaylorJetSymmetry
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Tactic

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The domain for the one-sided Taylor jets in the collar. -/
@[expose] def lowerHalfSpace (P : Type*) : Set (P × ℝ) := univ ×ˢ Iic 0

theorem uniqueDiffOn_lowerHalfSpace : UniqueDiffOn ℝ (lowerHalfSpace P) :=
  UniqueDiffOn.prod (uniqueDiffOn_univ : UniqueDiffOn ℝ (univ : Set P)) (uniqueDiffOn_Iic 0)

omit [NormedSpace ℝ P] in
private theorem lowerHalfSpace_subset_closure_interior :
    lowerHalfSpace P ⊆ closure (interior (lowerHalfSpace P)) := by
  rw [lowerHalfSpace,interior_prod_eq,interior_univ,interior_Iic,closure_prod_eq,closure_univ,closure_Iio]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem mem_lowerHalfSpace (p : P) : (p,0) ∈ lowerHalfSpace P := by
  simp [lowerHalfSpace]

/-- A one-sided Taylor series is zero on the boundary if all its pure
normal jets are zero there. Tangential differentiation of the preceding
jet kills each term containing a tangent vector. -/
private theorem jet_zero_of_normalJets_zero {f : P × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (lowerHalfSpace P))
    (hZero : ∀ (k : ℕ) p,
      iteratedFDerivWithin ℝ k f (lowerHalfSpace P) (p,0) (fun _ => (0,1)) = 0) :
    ∀ (k : ℕ) p, iteratedFDerivWithin ℝ k f (lowerHalfSpace P) (p,0) = 0 := by
  let S := lowerHalfSpace P
  have hS := uniqueDiffOn_lowerHalfSpace (P := P)
  let J (k : ℕ) := iteratedFDerivWithin ℝ k f S
  intro k
  induction k with
  | zero =>
    intro p
    ext v
    have he : v = fun _ => (0,1) := Subsingleton.elim _ _
    rw [he]
    exact hZero 0 p
  | succ k ih =>
    intro p
    have hMem := mem_lowerHalfSpace p
    have hTangent (v : Fin (k+1) → P × ℝ) (hv : (v 0).2 = 0) :
        J (k+1) (p,0) v = 0 := by
      let L := ContinuousLinearMap.inl ℝ P ℝ
      have hL : MapsTo L univ S := fun z _ => mem_lowerHalfSpace z
      have hSeries : HasFTaylorSeriesUpToOn (⊤ : ℕ∞) f (ftaylorSeriesWithin ℝ f S) S :=
        hf.ftaylorSeriesWithin hS
      have hJ : HasFDerivWithinAt (J k) ((J (k+1) (p,0)).curryLeft) S (p,0) :=
        hSeries.fderivWithin k (by exact_mod_cast WithTop.coe_lt_top k) (p,0) hMem
      have hD := (hJ.comp p L.hasFDerivWithinAt hL).hasFDerivAt (by simp)
      have hE : J k ∘ L = 0 := funext ih
      rw [hE] at hD
      have hZ := hD.fderiv
      rw [fderiv_zero] at hZ
      have hApply := congrArg (fun T : P →L[ℝ] ((P × ℝ) [×k]→L[ℝ] ℝ) =>
        T (v 0).1 (Fin.tail v)) hZ
      have hvE : L (v 0).1 = v 0 := Prod.ext rfl hv.symm
      simpa only [ContinuousLinearMap.comp_apply,hvE,ContinuousMultilinearMap.curryLeft_apply,
        Fin.cons_self_tail,Pi.zero_apply,zero_apply] using hApply.symm
    have hAnyTangent (v : Fin (k+1) → P × ℝ) (i : Fin (k+1)) (hv : (v i).2 = 0) :
        J (k+1) (p,0) v = 0 := by
      have he := iteratedFDerivWithin_perm hS lowerHalfSpace_subset_closure_interior hf
        (k+1) (p,0) hMem v (Equiv.swap 0 i)
      apply he.symm.trans (hTangent _ _)
      simpa only [Function.comp_apply,Equiv.swap_apply_left] using hv
    ext v
    let t (i : Fin (k+1)) : P × ℝ := ((v i).1,0)
    let n (i : Fin (k+1)) : P × ℝ := (v i).2 • ((0,1) : P × ℝ)
    have hv : v = t+n := by
      funext i
      simp [t,n,Prod.smul_mk]
    change J (k+1) (p,0) v = 0
    rw [hv]
    change (J (k+1) (p,0)).toMultilinearMap (t+n) = 0
    rw [MultilinearMap.map_add_univ]
    apply Finset.sum_eq_zero
    intro A _
    by_cases hA : A = ∅
    · rw [hA]
      change J (k+1) (p,0) ((∅ : Finset (Fin (k+1))).piecewise t n) = 0
      rw [Finset.piecewise_empty]
      change (J (k+1) (p,0)).toMultilinearMap (fun i => (v i).2 • ((0,1) : P × ℝ)) = 0
      rw [MultilinearMap.map_smul_univ]
      change _ • J (k+1) (p,0) (fun _ => (0,1)) = 0
      rw [hZero (k+1) p,smul_zero]
    · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hA
      exact hAnyTangent _ i (by simp [Finset.piecewise,hi,t])

set_option maxHeartbeats 1400000 in
/-- One-sided smooth functions with compactly supported boundary jets have
a smooth ambient extension. The normal jets are realized by the smooth
series, and the preceding lemma ensures agreement of all mixed jets. -/
theorem exists_contDiff_extension_lowerHalfSpace {f : P × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (lowerHalfSpace P))
    (hSupp : ∀ k : ℕ, HasCompactSupport (fun p : P =>
      iteratedFDerivWithin ℝ k f (lowerHalfSpace P) (p,0) (fun _ => (0,1)))) :
    ∃ F : P × ℝ → ℝ, ContDiff ℝ ∞ F ∧ EqOn F f (lowerHalfSpace P) := by
  let S := lowerHalfSpace P
  let T : Set (P × ℝ) := univ ×ˢ Ici 0
  let a (k : ℕ) (p : P) := iteratedFDerivWithin ℝ k f S (p,0) (fun _ => (0,1))
  have hS := uniqueDiffOn_lowerHalfSpace (P := P)
  have ha (k : ℕ) : ContDiff ℝ ∞ (a k) := by
    rw [← contDiffOn_univ]
    let L := ContinuousLinearMap.inl ℝ P ℝ
    let eval := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => P × ℝ) ℝ (fun _ => (0,1))
    exact eval.contDiff.comp_contDiffOn ((contDiffOn_iteratedFDerivWithin_top hf hS k).comp
      L.contDiff.contDiffOn (fun p _ => mem_lowerHalfSpace p))
  obtain ⟨U,hU,hJet⟩ := exists_smooth_realization_of_transverse_jets a ha hSupp
  have hSub (k : ℕ) (p : P) :
      iteratedFDerivWithin ℝ k (f-U) S (p,0) =
        iteratedFDerivWithin ℝ k f S (p,0) - iteratedFDeriv ℝ k U (p,0) := by
    rw [iteratedFDerivWithin_sub_apply ((hf (p,0) (mem_lowerHalfSpace p)).of_le (by simp))
      (hU.contDiffWithinAt.of_le (by simp)) hS (mem_lowerHalfSpace p)]
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hS (hU.contDiffAt.of_le (by simp)) (mem_lowerHalfSpace p)]
  have hMixed (k : ℕ) (p : P) :
      iteratedFDerivWithin ℝ k f S (p,0) = iteratedFDeriv ℝ k U (p,0) := by
    have hZero := jet_zero_of_normalJets_zero (hf.sub hU.contDiffOn) (fun l z => by
      change iteratedFDerivWithin ℝ l (f-U) S (z,0) (fun _ => (0,1)) = 0
      rw [hSub]
      change a l z - iteratedFDeriv ℝ l U (z,0) (fun _ => (0,1)) = 0
      rw [← iteratedDeriv_transverse_eq hU, hJet,sub_self]) k p
    exact sub_eq_zero.mp ((hSub k p).symm.trans hZero)
  classical
  let F := S.piecewise f U
  let J := S.piecewise (ftaylorSeriesWithin ℝ f S) (ftaylorSeries ℝ U)
  have hSU : IsClosed S := isClosed_univ.prod isClosed_Iic
  have hTU : IsClosed T := isClosed_univ.prod isClosed_Ici
  have hCover : S ∪ T = univ := by
    ext q
    simp only [S,T,lowerHalfSpace,mem_union,mem_prod,mem_univ,true_and,mem_Iic,mem_Ici,iff_true]
    exact le_total q.2 0
  have hJS : ∀ k, EqOn (fun q => J q k) (fun q => ftaylorSeriesWithin ℝ f S q k) S :=
    fun k q hq => by simp [J,Set.piecewise_eq_of_mem _ _ _ hq]
  have hJT : ∀ k, EqOn (fun q => J q k) (fun q => ftaylorSeries ℝ U q k) T := by
    intro k q hq
    by_cases hqS : q ∈ S
    · have hz : q.2 = 0 := le_antisymm hqS.2 hq.2
      rw [show q = (q.1,0) from Prod.ext rfl hz]
      exact (hJS k (mem_lowerHalfSpace q.1)).trans (hMixed k q.1)
    · simp [J,Set.piecewise_eq_of_notMem _ _ _ hqS]
  have hFS : EqOn F f S := fun q hq => Set.piecewise_eq_of_mem _ _ _ hq
  have hFT : EqOn F U T := by
    intro q hq
    by_cases hqS : q ∈ S
    · have hz : q.2 = 0 := le_antisymm hqS.2 hq.2
      rw [show q = (q.1,0) from Prod.ext rfl hz]
      rw [hFS (mem_lowerHalfSpace q.1)]
      simpa only [iteratedFDerivWithin_zero_apply,iteratedFDeriv_zero_apply] using
        congrArg (fun m : (P × ℝ) [×0]→L[ℝ] ℝ => m (fun _ => 0)) (hMixed 0 q.1)
    · exact Set.piecewise_eq_of_notMem _ _ _ hqS
  have hLo : HasFTaylorSeriesUpToOn (⊤ : ℕ∞) f (ftaylorSeriesWithin ℝ f S) S :=
    hf.ftaylorSeriesWithin hS
  have hFJS : HasFTaylorSeriesUpToOn (⊤ : ℕ∞) F J S :=
    (hLo.congr hFS).congr_series (fun k _ => (hJS k).symm)
  have hFJT : HasFTaylorSeriesUpToOn (⊤ : ℕ∞) F J T :=
    (((contDiff_iff_ftaylorSeries.mp hU).hasFTaylorSeriesUpToOn T).congr hFT).congr_series (fun k _ => (hJT k).symm)
  have hFJ : HasFTaylorSeriesUpToOn (⊤ : ℕ∞) F J (S ∪ T) := by
    refine ⟨fun q hq => hq.elim (hFJS.zero_eq q) (hFJT.zero_eq q),fun k hk q hq => ?_,
      fun k hk => (hFJS.cont k hk).union_of_isClosed (hFJT.cont k hk) hSU hTU⟩
    by_cases hs : q ∈ S
    · by_cases ht : q ∈ T
      · exact (hFJS.fderivWithin k hk q hs).union (hFJT.fderivWithin k hk q ht)
      · exact (hFJS.fderivWithin k hk q hs).mono_of_mem_nhdsWithin (by
          filter_upwards [eventually_mem_nhdsWithin,nhdsWithin_le_nhds (hTU.isOpen_compl.mem_nhds ht)] with z hz hn
          exact hz.resolve_right hn)
    · have ht := hq.resolve_left hs
      exact (hFJT.fderivWithin k hk q ht).mono_of_mem_nhdsWithin (by
        filter_upwards [eventually_mem_nhdsWithin,nhdsWithin_le_nhds (hSU.isOpen_compl.mem_nhds hs)] with z hz hn
        exact hz.resolve_left hn)
  rw [hCover] at hFJ
  exact ⟨F,contDiffOn_univ.mp hFJ.contDiffOn,hFS⟩

end CalderonN

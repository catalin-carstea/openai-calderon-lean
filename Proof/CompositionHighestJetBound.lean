import Mathlib.Analysis.Calculus.ContDiff.Bounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma orderedFinpartition_sum_partSize {n : ℕ} (c : OrderedFinpartition n) :
    (∑ i,c.partSize i) = n := by
  have ht := Fintype.card_congr c.equivSigma
  simpa only [Fintype.card_sigma,Fintype.card_fin] using ht

lemma orderedFinpartition_partSize_lt_of_length {n : ℕ} (c : OrderedFinpartition n)
    (hLength : 2 ≤ c.length) (i : Fin c.length) : c.partSize i < n := by
  have hExists : ∃ j : Fin c.length,j ≠ i := by
    by_cases hi : i.val = 0
    · refine ⟨⟨1,by omega⟩,?_⟩
      intro hh
      have hv := congrArg Fin.val hh
      change 1 = i.val at hv
      omega
    · refine ⟨⟨0,by omega⟩,?_⟩
      intro hh
      have hv := congrArg Fin.val hh
      change 0 = i.val at hv
      omega
  obtain ⟨j,hji⟩ := hExists
  have hOther : c.partSize j ≤ ∑ k ∈ (Finset.univ : Finset (Fin c.length)).erase i,c.partSize k :=
    Finset.single_le_sum (fun k _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hji,Finset.mem_univ j⟩)
  have hPos := c.partSize_pos j
  have hSum := orderedFinpartition_sum_partSize c
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hSum
  omega

/-- Faa di Bruno with the highest input jet kept linear. This is the
estimate needed for a higher variational equation followed by Gronwall;
all nonlinear forcing depends only on lower input jets. -/
theorem norm_iteratedFDeriv_comp_highest_linear
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → F) (g : F → G) (x : E) (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x))
    (n : ℕ) (hn : 1 ≤ n) (A C D : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hg1 : ‖iteratedFDeriv ℝ 1 g (f x)‖ ≤ A)
    (hgHigher : ∀ j : ℕ,2 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j g (f x)‖ ≤ C)
    (hfLower : ∀ j : ℕ,1 ≤ j → j < n → ‖iteratedFDeriv ℝ j f x‖ ≤ D) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ (Fintype.card (OrderedFinpartition n):ℝ)*
      (A*‖iteratedFDeriv ℝ n f x‖+A*D+C*(D+1)^n) := by
  let U := ‖iteratedFDeriv ℝ n f x‖
  have hU : 0 ≤ U := norm_nonneg _
  have hD1 : 1 ≤ D+1 := by linarith
  have hAll (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) : ‖iteratedFDeriv ℝ j f x‖ ≤ U+D := by
    by_cases he : j = n
    · subst j
      change U ≤ U+D
      linarith only [hD]
    · exact (hfLower j hj (by omega)).trans (by linarith only [hU])
  have hTerm (c : OrderedFinpartition n) :
      ‖(ftaylorSeries ℝ g (f x)).compAlongOrderedFinpartition (ftaylorSeries ℝ f x) c‖ ≤
        A*U+A*D+C*(D+1)^n := by
    have hBasic := c.norm_compAlongOrderedFinpartition_le
      ((ftaylorSeries ℝ g (f x)) c.length) (fun i => (ftaylorSeries ℝ f x) (c.partSize i))
    change ‖(ftaylorSeries ℝ g (f x)).compAlongOrderedFinpartition (ftaylorSeries ℝ f x) c‖ ≤
      ‖iteratedFDeriv ℝ c.length g (f x)‖*∏ i,‖iteratedFDeriv ℝ (c.partSize i) f x‖ at hBasic
    by_cases hOne : c.length = 1
    · have hOuter : ‖iteratedFDeriv ℝ c.length g (f x)‖ ≤ A := by rw [hOne];exact hg1
      have hInner : (∏ i,‖iteratedFDeriv ℝ (c.partSize i) f x‖) ≤ U+D := by
        have ht := Finset.prod_le_prod₀ (s:=Finset.univ) (fun i _ => norm_nonneg (iteratedFDeriv ℝ (c.partSize i) f x))
          (fun i _ => hAll (c.partSize i) (c.partSize_pos i) (c.partSize_le i))
        simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,hOne,pow_one] using ht
      exact hBasic.trans ((mul_le_mul hOuter hInner (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hA).trans
        (by
          have hc0 : 0 ≤ C*(D+1)^n := by positivity
          nlinarith only [hc0]))
    · have hLength : 2 ≤ c.length := by have hp := c.length_pos (by omega);omega
      have hOuter := hgHigher c.length hLength c.length_le
      have hInner : (∏ i,‖iteratedFDeriv ℝ (c.partSize i) f x‖) ≤ (D+1)^n := by
        have hEach (i : Fin c.length) : ‖iteratedFDeriv ℝ (c.partSize i) f x‖ ≤ D+1 :=
          (hfLower (c.partSize i) (c.partSize_pos i) (orderedFinpartition_partSize_lt_of_length c hLength i)).trans (by linarith)
        have ht := Finset.prod_le_prod₀ (s:=Finset.univ) (fun i _ => norm_nonneg (iteratedFDeriv ℝ (c.partSize i) f x)) (fun i _ => hEach i)
        have hp : (D+1)^c.length ≤ (D+1)^n := pow_le_pow_right₀ hD1 c.length_le
        exact (show (∏ i,‖iteratedFDeriv ℝ (c.partSize i) f x‖) ≤ (D+1)^c.length by
          simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using ht).trans hp
      exact hBasic.trans ((mul_le_mul hOuter hInner (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hC).trans
        (by
          have had : 0 ≤ A*U+A*D := by positivity
          linarith only [had]))
  rw [iteratedFDeriv_comp hg hf (i:=n) (by simp),FormalMultilinearSeries.taylorComp]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun c _ => hTerm c)).trans_eq
    (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] <;> rfl))

end ShrinkingSpheres

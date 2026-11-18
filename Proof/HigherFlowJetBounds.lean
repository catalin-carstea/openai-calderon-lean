import Proof.CompositionHighestJetBound
import Mathlib.Analysis.ODE.Gronwall

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- A deliberately generous cumulative budget for finite jets of a flow.
    It depends only on the common spray-jet bound and the order. -/
def higherFlowJetBudget (S : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => higherFlowJetBudget S n +
    (1+(Fintype.card (OrderedFinpartition (n+1)):ℝ)*
      (S*higherFlowJetBudget S n+S*(higherFlowJetBudget S n+1)^(n+1)))*
      Real.exp (1+(Fintype.card (OrderedFinpartition (n+1)):ℝ)*S)

lemma one_le_higherFlowJetBudget (S : ℝ) (hS : 0 ≤ S) (n : ℕ) :
    1 ≤ higherFlowJetBudget S n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hB : 0 ≤ higherFlowJetBudget S n := zero_le_one.trans ih
    have hAdd : 0 ≤ (1+(Fintype.card (OrderedFinpartition (n+1)):ℝ)*
        (S*higherFlowJetBudget S n+S*(higherFlowJetBudget S n+1)^(n+1)))*
        Real.exp (1+(Fintype.card (OrderedFinpartition (n+1)):ℝ)*S) := by positivity
    simpa only [higherFlowJetBudget] using ih.trans (le_add_of_nonneg_right hAdd)

lemma higherFlowJetBudget_mono (S : ℝ) (hS : 0 ≤ S) : Monotone (higherFlowJetBudget S) := by
  apply monotone_nat_of_le_succ
  intro n
  have hB : 0 ≤ higherFlowJetBudget S n := zero_le_one.trans (one_le_higherFlowJetBudget S hS n)
  change higherFlowJetBudget S n ≤ higherFlowJetBudget S n+_
  apply le_add_of_nonneg_right
  positivity

theorem norm_flow_jet_le_of_lower_bounds
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (phi : ℝ → P → E) (g : E → E) (p : P) (n : ℕ) (hn : 1 ≤ n)
    (J : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin n => P) E)
    (S D : ℝ) (hS : 0 ≤ S) (hD : 0 ≤ D)
    (hphi : ∀ t ∈ Icc (0:ℝ) 1, ContDiffAt ℝ ∞ (phi t) p)
    (hg : ∀ t ∈ Icc (0:ℝ) 1, ContDiffAt ℝ ∞ g (phi t p))
    (hJet : ∀ t ∈ Icc (0:ℝ) 1, J t = iteratedFDeriv ℝ n (phi t) p)
    (hODE : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt J (iteratedFDeriv ℝ n (g ∘ phi t) p) t)
    (hInitial : ‖J 0‖ ≤ 1)
    (hSpray : ∀ t ∈ Icc (0:ℝ) 1, ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDeriv ℝ j g (phi t p)‖ ≤ S)
    (hLower : ∀ t ∈ Icc (0:ℝ) 1, ∀ j, 1 ≤ j → j < n →
      ‖iteratedFDeriv ℝ j (phi t) p‖ ≤ D)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖J t‖ ≤ (1+(Fintype.card (OrderedFinpartition n):ℝ)*(S*D+S*(D+1)^n))*
      Real.exp (1+(Fintype.card (OrderedFinpartition n):ℝ)*S) := by
  let b : ℝ := Fintype.card (OrderedFinpartition n)
  let A : ℝ := 1+b*S
  let delta : ℝ := b*(S*D+S*(D+1)^n)
  have hb : 0 ≤ b := Nat.cast_nonneg _
  have hA : 1 ≤ A := by
    have hbs : 0 ≤ b*S := mul_nonneg hb hS
    dsimp only [A]
    linarith only [hbs]
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hd : 0 ≤ delta := by dsimp only [delta]; positivity
  have hGrowth (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      ‖iteratedFDeriv ℝ n (g ∘ phi s) p‖ ≤ A*‖J s‖+delta := by
    have hh := norm_iteratedFDeriv_comp_highest_linear (phi s) g p (hphi s hs) (hg s hs)
      n hn S S D hS hS hD (hSpray s hs 1 (by omega) hn)
      (fun j hj hjn => hSpray s hs j (by omega) hjn) (hLower s hs)
    rw [← hJet s hs] at hh
    have hJ : 0 ≤ ‖J s‖ := norm_nonneg _
    dsimp only [A,delta,b] at *
    nlinarith only [hh,hJ]
  have hCont : ContinuousOn J (Icc (0:ℝ) 1) :=
    fun s hs => (hODE s hs).continuousAt.continuousWithinAt
  have hRight (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) :
      HasDerivWithinAt J (iteratedFDeriv ℝ n (g ∘ phi s) p) (Ici s) s :=
    (hODE s ⟨hs.1,hs.2.le⟩).hasDerivWithinAt
  have hh := norm_le_gronwallBound_of_norm_deriv_right_le hCont hRight hInitial
    (fun s hs => hGrowth s ⟨hs.1,hs.2.le⟩) t ht
  simp only [gronwallBound_of_K_ne_0 hApos.ne',sub_zero,one_mul] at hh
  have hExp : Real.exp (A*t) ≤ Real.exp A :=
    Real.exp_le_exp.mpr (mul_le_of_le_one_right hApos.le ht.2)
  have hExpSub : Real.exp (A*t)-1 ≤ Real.exp A := (sub_le_self _ zero_le_one).trans hExp
  have hForcing : delta/A*(Real.exp (A*t)-1) ≤ delta*Real.exp A :=
    (mul_le_mul_of_nonneg_left hExpSub (div_nonneg hd hApos.le)).trans
      (mul_le_mul_of_nonneg_right (div_le_self hd hA) (Real.exp_pos A).le)
  exact hh.trans ((add_le_add hExp hForcing).trans_eq (by ring))

/-- All finite flow jets are uniform once the spray jets and the exact
    differentiated flow equations are uniform. This is an ODE estimate,
    rather than compactness of a family of admitted geometries. -/
theorem flow_jets_le_higherFlowJetBudget
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (phi : ℝ → P → E) (g : E → E) (p : P)
    (J : (n : ℕ) → ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin n => P) E)
    (S : ℝ) (hS : 0 ≤ S)
    (hphi : ∀ t ∈ Icc (0:ℝ) 1, ContDiffAt ℝ ∞ (phi t) p)
    (hg : ∀ t ∈ Icc (0:ℝ) 1, ContDiffAt ℝ ∞ g (phi t p))
    (hJet : ∀ n t, t ∈ Icc (0:ℝ) 1 → J n t = iteratedFDeriv ℝ n (phi t) p)
    (hODE : ∀ n, 1 ≤ n → ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt (J n) (iteratedFDeriv ℝ n (g ∘ phi t) p) t)
    (hInitial : ∀ n, 1 ≤ n → ‖J n 0‖ ≤ 1)
    (N : ℕ)
    (hSpray : ∀ t ∈ Icc (0:ℝ) 1, ∀ j, 1 ≤ j → j ≤ N →
      ‖iteratedFDeriv ℝ j g (phi t p)‖ ≤ S) :
    ∀ n, 1 ≤ n → n ≤ N → ∀ t ∈ Icc (0:ℝ) 1, ‖J n t‖ ≤ higherFlowJetBudget S N := by
  induction N with
  | zero => intro n hn hnN; omega
  | succ N ih =>
    have hOld := ih (fun t ht j hj hjN => hSpray t ht j hj (by omega))
    intro n hn hnN t ht
    by_cases hnOld : n ≤ N
    · exact (hOld n hn hnOld t ht).trans (higherFlowJetBudget_mono S hS (Nat.le_succ N))
    · have he : n = N+1 := by omega
      subst n
      have hD : 0 ≤ higherFlowJetBudget S N := zero_le_one.trans (one_le_higherFlowJetBudget S hS N)
      have hLower (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (j : ℕ) (hj : 1 ≤ j) (hjn : j < N+1) :
          ‖iteratedFDeriv ℝ j (phi s) p‖ ≤ higherFlowJetBudget S N := by
        rw [← hJet j s hs]
        exact hOld j hj (by omega) s hs
      have hh := norm_flow_jet_le_of_lower_bounds phi g p (N+1) (by omega) (J (N+1))
        S (higherFlowJetBudget S N) hS hD hphi hg (hJet (N+1))
        (hODE (N+1) (by omega)) (hInitial (N+1) (by omega)) hSpray hLower ht
      exact hh.trans (by
        change _ ≤ higherFlowJetBudget S N+_
        exact le_add_of_nonneg_left hD)

end ShrinkingSpheres

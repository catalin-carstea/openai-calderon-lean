module

public import Proof.CalderonN.ProfileCovariantToChart

import Mathlib.Tactic

/-! The highest-order term in the covariant-coordinate expansion is
the corresponding ordinary derivative, with coefficient one. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN.ProfileCovariant

variable {dim : ℕ}

private theorem filter_flatMap_of_eq_nil {T S : Type*} (p : S → Bool) (L : List T)
    (F : T → List S) (h : ∀ t ∈ L,(F t).filter p = []) :
    (L.flatMap F).filter p = [] := by
  induction L with
  | nil => rfl
  | cons a l ih =>
      rw [List.flatMap_cons,List.filter_append,h a (by simp),List.nil_append]
      exact ih (fun t ht => h t (by simp [ht]))

theorem covariantCoordinateExpansion_top (Γ : CoordinateConnectionFamily dim)
    (n : ℕ) (I : Fin n → Fin dim) :
    (covariantCoordinateExpansion Γ n I).filter (fun t => decide (t.order=n)) =
      [⟨fun _ => 1,n,I⟩] := by
  induction n with
  | zero =>
      simp only [covariantCoordinateExpansion,List.filter_cons,List.filter_nil,decide_true,if_true]
      congr 2
      exact funext (fun i => Fin.elim0 i)
  | succ n ih =>
      rw [covariantCoordinateExpansion,List.filter_append]
      have hR : List.filter (fun t : CoordinateJetTerm dim => decide (t.order=n+1))
          ((List.ofFn (fun l : Fin n => l)).flatMap (fun l =>
            (List.ofFn (fun k : Fin dim => k)).flatMap (fun k =>
              (covariantCoordinateExpansion Γ n (Function.update (Fin.tail I) l k)).map
                (coordinateTermMultiply (fun z => -connectionCoordinateCoeff Γ (I 0) ((Fin.tail I) l) k z)))))
            = [] := by
        apply filter_flatMap_of_eq_nil
        intro l _
        apply filter_flatMap_of_eq_nil
        intro k _
        apply List.filter_eq_nil_iff.2
        intro t ht
        obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ht
        have hOrd := covariantCoordinateExpansion_order_le Γ n _ q hq
        have hne : q.order ≠ n+1 := by omega
        simp [coordinateTermMultiply,hne]
      rw [hR,List.append_nil]
      let L := covariantCoordinateExpansion Γ n (Fin.tail I)
      let G (t : CoordinateJetTerm dim) : CoordinateJetTerm dim :=
        ⟨t.coeff,t.order+1,Fin.cons (I 0) t.indices⟩
      have hFlat : ∀ L' : List (CoordinateJetTerm dim), (∀ t ∈ L',t.order ≤ n) →
          (L'.flatMap (coordinateTermDerivative (I 0))).filter (fun t => decide (t.order=n+1)) =
            (L'.filter (fun t => decide (t.order=n))).map G := by
        intro L' hL
        induction L' with
        | nil => rfl
        | cons t l ih =>
            have h1 := hL t (by simp)
            have h2 : t.order ≠ n+1 := by omega
            rw [List.flatMap_cons,List.filter_append,ih (fun s hs => hL s (by simp [hs]))]
            simp only [coordinateTermDerivative,List.filter_cons,List.filter_nil,h2,decide_false,if_false,
              Nat.succ_inj,Finset.mem_univ]
            by_cases ht : t.order=n
            · simp [ht,G]
            · simp [ht]
      change (L.flatMap (coordinateTermDerivative (I 0))).filter (fun t => decide (t.order=n+1)) = _
      rw [hFlat L (covariantCoordinateExpansion_order_le Γ n (Fin.tail I)),ih (Fin.tail I)]
      simp only [List.map_cons,List.map_nil,G]
      rw [Fin.cons_self_tail]

private theorem coordinateTermsValue_filter_partition (L : List (CoordinateJetTerm dim))
    (f : X dim → ℝ) (x : ℝ × X dim) (p : CoordinateJetTerm dim → Bool) :
    coordinateTermsValue L f x =
      coordinateTermsValue (L.filter p) f x+coordinateTermsValue (L.filter (fun t => !p t)) f x := by
  induction L with
  | nil => simp [coordinateTermsValue]
  | cons t l ih =>
      have ht : ∃ b : Bool,p t=b := ⟨p t,rfl⟩
      obtain ⟨b,hb⟩ := ht
      cases b <;> simp only [coordinateTermsValue,List.filter_cons,hb,Bool.not_false,Bool.not_true,
        Bool.false_eq_true,ite_true,ite_false,List.map_cons,List.sum_cons] at ih ⊢ <;>
        rw [ih] <;> ac_rfl

theorem covariantCoordinateJet_eq_partial_add_lower (Γ : CoordinateConnectionFamily dim)
    (hΓ : ∀ k i j,ContDiff ℝ ∞ (Γ k i j)) (f : X dim → ℝ) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (I : Fin n → Fin dim) (x : ℝ × X dim) :
    covariantCoordinateJet Γ f x.1 n x.2 I =
      coordinatePartialJet f n I x.2+
      coordinateTermsValue ((covariantCoordinateExpansion Γ n I).filter
        (fun t => !decide (t.order=n))) f x := by
  rw [covariantCoordinateJet_eq_expansion Γ hΓ f hf,
    coordinateTermsValue_filter_partition _ f x (fun t => decide (t.order=n)),
    covariantCoordinateExpansion_top]
  simp only [coordinateTermsValue,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    coordinateTermValue,one_mul]

end CalderonN.ProfileCovariant

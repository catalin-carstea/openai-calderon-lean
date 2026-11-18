/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.TauCeti.Analysis.PDE.EnergyForm.Linearity

 





















public section

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {X n : Type*} [Fintype n]

 
noncomputable def energyIntegrandLinear : (Matrix n n ℝ × EuclideanSpace ℝ n × ℝ) →L[ℝ]
      (ℝ × EuclideanSpace ℝ n) →L[ℝ] (ℝ × EuclideanSpace ℝ n) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => energyIntegrand p.1 p.2.1 p.2.2
      map_add' := by
        rintro ⟨A, b, c⟩ ⟨B, d, e⟩
        apply ContinuousLinearMap.ext
        intro U
        apply ContinuousLinearMap.ext
        intro V
        exact energyIntegrand_add_apply A B b d c e U V
      map_smul' := by
        rintro r ⟨A, b, c⟩
        apply ContinuousLinearMap.ext
        intro U
        apply ContinuousLinearMap.ext
        intro V
        exact energyIntegrand_smul_apply A b c r U V }

 
@[simp]
lemma energyIntegrandLinear_apply (A : Matrix n n ℝ) (b : EuclideanSpace ℝ n) (c : ℝ) :
    energyIntegrandLinear (n := n) (A, b, c) = energyIntegrand A b c :=
  by
    apply ContinuousLinearMap.ext
    rintro ⟨u, η⟩
    apply ContinuousLinearMap.ext
    rintro ⟨v, ξ⟩
    simp [energyIntegrandLinear]

 
lemma continuous_energyIntegrand :
    Continuous (fun p : Matrix n n ℝ × EuclideanSpace ℝ n × ℝ =>
      energyIntegrand p.1 p.2.1 p.2.2) :=
  (energyIntegrandLinear (n := n)).continuous.congr fun p =>
    energyIntegrandLinear_apply p.1 p.2.1 p.2.2

variable [TopologicalSpace X]

namespace Continuous

 

lemma energyIntegrand {a : X → Matrix n n ℝ} {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    Continuous (fun x => PDE.energyIntegrand (a x) (b x) (c x)) :=
  continuous_energyIntegrand.comp (ha.prodMk (hb.prodMk hc))

end Continuous

namespace ContinuousOn

 

lemma energyIntegrand {s : Set X} {a : X → Matrix n n ℝ} {b : X → EuclideanSpace ℝ n}
    {c : X → ℝ} (ha : ContinuousOn a s) (hb : ContinuousOn b s) (hc : ContinuousOn c s) :
    ContinuousOn (fun x => PDE.energyIntegrand (a x) (b x) (c x)) s :=
  continuous_energyIntegrand.comp_continuousOn (ha.prodMk (hb.prodMk hc))

end ContinuousOn

end PDE

end TauCeti

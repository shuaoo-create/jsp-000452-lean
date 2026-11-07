import CoreLanguage
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.SetTheory.Cardinal.Finite

namespace JSP452Audit.Padded
open SimpleGraph

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

/-- The two incidence families are distinguished even when the undirected
underlying edge is the same: a core stub and the opposite T-stub are distinct. -/
abbrev Spec.CoreLabelAt (T : Set V) (v : V) :=
  (P.G.neighborSet v ⊕ Fin (P.padding v)) ⊕
  (Fin (P.mandatoryCount v) ⊕ Fin (P.optionalCount v)) ⊕
  {w : P.G.neighborSet v // w.val ∈ T}

abbrev Spec.CoreLabels {S T : Set V} (C : P.CoreComponent S T) :=
  Σ u : C.supp, P.CoreLabelAt T u.val.val

private def originalPoint {S T : Set V} {C : P.CoreComponent S T} {v : V}
    (h : P.inOriginal C v) : C.supp :=
  ⟨⟨v,h.choose⟩,h.choose_spec⟩

omit [Fintype V] [DecidableRel P.G.Adj] in
private theorem original_of_point {S T : Set V} {C : P.CoreComponent S T}
    (u : C.supp) : P.inOriginal C u.val.val := ⟨u.val.property,u.property⟩

private def rawCoreLabel {S T : Set V} (C : P.CoreComponent S T) :
    P.CoreLabels C → {z : P.Vertex // P.onCore C z}
  | ⟨u,.inl (.inl w)⟩ => ⟨P.realStub u.val.val w.val w.property, Or.inl (original_of_point P u)⟩
  | ⟨u,.inl (.inr i)⟩ => ⟨P.extraStub u.val.val i, original_of_point P u⟩
  | ⟨u,.inr (.inl (.inl i))⟩ => ⟨P.mandatory ⟨u.val.val,i⟩,original_of_point P u⟩
  | ⟨u,.inr (.inl (.inr i))⟩ => ⟨P.optional ⟨u.val.val,i⟩,original_of_point P u⟩
  | ⟨u,.inr (.inr w)⟩ => ⟨P.realStub w.val.val u.val.val w.val.property.symm,
      Or.inr ⟨w.property,original_of_point P u⟩⟩

private noncomputable def indexCoreLabel {S T : Set V} (C : P.CoreComponent S T) :
    {z : P.Vertex // P.onCore C z} → P.CoreLabels C := by
  classical
  rintro ⟨⟨v,w | i⟩ | ((a | b) | g), core⟩
  · by_cases inside : P.inOriginal C v
    · exact ⟨originalPoint P inside,.inl (.inl w)⟩
    · have both := core.resolve_left inside
      exact ⟨originalPoint P both.2,.inr (.inr ⟨⟨v,w.property.symm⟩,both.1⟩)⟩
  · exact ⟨originalPoint P core,.inl (.inr i)⟩
  · exact ⟨originalPoint P core,.inr (.inl (.inl a.2))⟩
  · exact ⟨originalPoint P core,.inr (.inl (.inr b.2))⟩
  · exact core.elim

/-- Each point of the core has one label: its local owner, or the head of
its unique oriented T-to-core attaching edge. -/
noncomputable def Spec.coreLabelsEquiv {S T : Set V} (C : P.CoreComponent S T) :
    P.CoreLabels C ≃ {z : P.Vertex // P.onCore C z} where
  toFun := rawCoreLabel P C
  invFun := indexCoreLabel P C
  left_inv := by
    rintro ⟨u,(w | i) | ((m | o) | t)⟩
    · simp [rawCoreLabel,indexCoreLabel,Spec.realStub,original_of_point P u,originalPoint]
    · rfl
    · rfl
    · rfl
    · have out : ¬ P.inOriginal C t.val.val := fun h => (P.notST_of_inOriginal h).2 t.property
      simp [rawCoreLabel,indexCoreLabel,Spec.realStub,out,originalPoint]
  right_inv := by
    rintro ⟨⟨v,w | i⟩ | ((a | b) | g), core⟩
    · by_cases own : P.inOriginal C v <;> simp [indexCoreLabel,rawCoreLabel,own,originalPoint,Spec.realStub]
    · rfl
    · rfl
    · rfl
    · exact core.elim

/-- Retention changes only the proof carried by a core point. -/
def Spec.coreKeptEquiv {S T : Set V} (dis : Disjoint S T) (C : P.CoreComponent S T) :
    {z : P.Vertex // P.onCore C z} ≃ {z : P.CanonVertex S T // P.onCore C z.val} where
  toFun z := ⟨P.canonicalPoint z.val (P.onCore_kept dis z.property),z.property⟩
  invFun z := ⟨z.val.val,z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Number of T-to-C half-edges, counted once at their head in the core. -/
noncomputable def Spec.toCoreCount {S T : Set V} (C : P.CoreComponent S T) [Fintype C.supp] : ℕ :=
  ∑ u : C.supp, Nat.card {w : P.G.neighborSet u.val.val // w.val ∈ T}

private theorem local_slot_total (v : V) (cap : P.G.degree v ≤ P.A v + P.B v) :
    P.mandatoryCount v + P.optionalCount v = P.B v + P.padding v := by
  dsimp [Spec.mandatoryCount,Spec.optionalCount,Spec.padding]
  omega

theorem Spec.core_raw_card {S T : Set V} (C : P.CoreComponent S T) [Fintype C.supp]
    (cap : ∀ v, P.G.degree v ≤ P.A v + P.B v) :
    Nat.card {z : P.Vertex // P.onCore C z} =
      (∑ u : C.supp, (P.G.degree u.val.val + P.B u.val.val + 2*P.padding u.val.val)) +
      P.toCoreCount C := by
  classical
  let _ (u : C.supp) : Finite (P.CoreLabelAt T u.val.val) := by unfold Spec.CoreLabelAt; infer_instance
  rw [← Nat.card_congr (P.coreLabelsEquiv C)]
  change Nat.card (Σ u : C.supp, P.CoreLabelAt T u.val.val) = _
  rw [Nat.card_sigma, Spec.toCoreCount, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  let v := u.val.val
  have deg : Nat.card (P.G.neighborSet v) = P.G.degree v := by
    rw [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree]
  change Nat.card (P.CoreLabelAt T v) = _
  simp only [Spec.CoreLabelAt,Nat.card_sum,Nat.card_fin,deg]
  have tok := local_slot_total P v (cap v)
  dsimp only [v] at *
  omega

theorem Spec.core_kept_card {S T : Set V} (dis : Disjoint S T)
    (C : P.CoreComponent S T) [Fintype C.supp] (cap : ∀ v, P.G.degree v ≤ P.A v + P.B v) :
    Nat.card {z : P.CanonVertex S T // P.onCore C z.val} =
      (∑ u : C.supp, (P.G.degree u.val.val + P.B u.val.val + 2*P.padding u.val.val)) +
      P.toCoreCount C :=
  (Nat.card_congr (P.coreKeptEquiv dis C)).symm.trans (P.core_raw_card C cap)

theorem Spec.core_tight_odd_iff {S T : Set V} (C : P.CoreComponent S T) [Fintype C.supp]
    (cap : ∀ v, P.G.degree v ≤ P.A v + P.B v) (tight : P.coreTight C) :
    Odd (Nat.card {z : P.Vertex // P.onCore C z}) ↔
      Odd ((∑ u : C.supp, P.A u.val.val) + P.toCoreCount C) := by
  have split : (∑ u : C.supp, (P.G.degree u.val.val + P.B u.val.val + 2*P.padding u.val.val)) =
      (∑ u : C.supp, P.A u.val.val) + 2*∑ u : C.supp, (P.B u.val.val + P.padding u.val.val) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    have ht := tight u.val u.property
    have hc := cap u.val.val
    unfold Spec.optionalCount at ht
    omega
  rw [P.core_raw_card C cap,split]
  constructor <;> rintro ⟨w,hw⟩
  · refine ⟨w - ∑ u : C.supp, (P.B u.val.val + P.padding u.val.val),?_⟩
    omega
  · refine ⟨w + ∑ u : C.supp, (P.B u.val.val + P.padding u.val.val),?_⟩
    omega

#print axioms Spec.coreLabelsEquiv
#print axioms Spec.coreKeptEquiv
#print axioms Spec.core_raw_card
#print axioms Spec.core_kept_card
#print axioms Spec.core_tight_odd_iff
end JSP452Audit.Padded

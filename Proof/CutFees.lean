import CanonicalSingletons

namespace JSP452Audit.Padded
open SimpleGraph

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

/-- One index per adjacency crossing from T to S. -/
noncomputable def Spec.cutCrossTS (S T : Set V) : ℕ :=
  Nat.card ((v : T) × {w : P.G.neighborSet v.val // w.val ∈ S})

omit [DecidableRel P.G.Adj] in
theorem Spec.cutCrossTS_eq_sum (S T : Set V) [Fintype T] :
    P.cutCrossTS S T = ∑ v : T, Nat.card {w : P.G.neighborSet v.val // w.val ∈ S} :=
  Nat.card_sigma

/-- All removed stubs in S and all removed owned tokens in T, indexed at their owner. -/
abbrev Spec.RemovedIndex (S T : Set V) :=
  ((v : S) × (P.G.neighborSet v.val ⊕ Fin (P.padding v.val))) ⊕
  ((v : T) × (Fin (P.mandatoryCount v.val) ⊕ Fin (P.optionalCount v.val)))

noncomputable def Spec.removedIndexEquiv (S T : Set V) :
    P.RemovedIndex S T ≃ {z : P.Vertex // ¬P.keptBy S T z} where
  toFun
    | .inl ⟨v,b⟩ => ⟨.inl ⟨v.val,b⟩,fun kept => kept v.property⟩
    | .inr ⟨v,.inl i⟩ => ⟨P.mandatory ⟨v.val,i⟩,fun kept => kept v.property⟩
    | .inr ⟨v,.inr i⟩ => ⟨P.optional ⟨v.val,i⟩,fun kept => kept v.property⟩
  invFun
    | ⟨.inl ⟨v,b⟩,h⟩ => .inl ⟨⟨v,Classical.not_not.mp h⟩,b⟩
    | ⟨.inr (.inl (.inl ⟨v,i⟩)),h⟩ => .inr ⟨⟨v,Classical.not_not.mp h⟩,.inl i⟩
    | ⟨.inr (.inl (.inr ⟨v,i⟩)),h⟩ => .inr ⟨⟨v,Classical.not_not.mp h⟩,.inr i⟩
    | ⟨.inr (.inr _),h⟩ => (h trivial).elim
  left_inv := by rintro (⟨v,b⟩|⟨v,i|i⟩) <;> rfl
  right_inv := by rintro ⟨⟨v,b⟩|((⟨v,i⟩|⟨v,i⟩)|g),h⟩ <;> first | rfl | exact (h trivial).elim

theorem Spec.removed_canonical_count (S T : Set V) [Fintype S] [Fintype T] :
    Nat.card {z : P.Vertex // ¬P.keptBy S T z} =
      (∑ v : S, (P.G.degree v.val + P.padding v.val)) +
      (∑ v : T, (P.mandatoryCount v.val + P.optionalCount v.val)) := by
  rw [← Nat.card_congr (P.removedIndexEquiv S T)]
  simp only [Spec.RemovedIndex,Nat.card_sum,Nat.card_sigma,Nat.card_fin]
  congr 1
  exact Finset.sum_congr rfl fun v _ => by
    rw [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree]

/-- Local singleton fees minus removed vertices leave exactly the T-to-S edge
term minus the two original degree bounds. Natural equality avoids subtraction. -/
theorem Spec.canonical_cut_fees (S T : Set V) [Fintype S] [Fintype T]
    (caps : ∀ v, P.G.degree v ≤ P.A v + P.B v) :
    Nat.card (P.SingletonIndex S T) + (∑ v : S, P.A v.val) + (∑ v : T, P.B v.val) =
      Nat.card {z : P.Vertex // ¬P.keptBy S T z} + P.cutCrossTS S T := by
  have old (v : S) :
      P.mandatoryCount v.val + P.A v.val = P.G.degree v.val + P.padding v.val := by
    unfold Spec.mandatoryCount Spec.padding
    omega
  have new (v : T) :
      P.padding v.val + P.B v.val = P.mandatoryCount v.val + P.optionalCount v.val := by
    have bound := caps v.val
    unfold Spec.mandatoryCount Spec.optionalCount Spec.padding
    omega
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset S)) rfl (fun v _ => old v)
  have ht := Finset.sum_congr (s₁ := (Finset.univ : Finset T)) rfl (fun v _ => new v)
  rw [P.singletonIndex_count S T,P.removed_canonical_count S T,P.cutCrossTS_eq_sum S T]
  simp only [Finset.sum_add_distrib] at hs ht ⊢
  omega

theorem Spec.canonical_cut_fees_explicit (S T : Set V) [Fintype S] [Fintype T]
    (caps : ∀ v, P.G.degree v ≤ P.A v + P.B v) :
    Nat.card (P.SingletonIndex S T) + (∑ v : S, P.A v.val) + (∑ v : T, P.B v.val) =
      Nat.card {z : P.Vertex // ¬P.keptBy S T z} +
        ∑ v : T, Nat.card {w : P.G.neighborSet v.val // w.val ∈ S} := by
  rw [← P.cutCrossTS_eq_sum S T]
  exact P.canonical_cut_fees S T caps

#print axioms Spec.removedIndexEquiv
#print axioms Spec.removed_canonical_count
#print axioms Spec.canonical_cut_fees
#print axioms Spec.canonical_cut_fees_explicit
end JSP452Audit.Padded

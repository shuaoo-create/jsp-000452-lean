import BarrierMatchingDecomposition
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*}
/-- An assignment records actual possible host edges from every root to
different residual components. The edge endpoint is chosen on realization. -/
structure RootAllocation (G : SimpleGraph X) (S : Set X) where
  place : ↥S ↪ (G.induce Sᶜ).ConnectedComponent
  link : ∀ a : S, ∃ z : (place a).supp, G.Adj a.val z.val.val

def allFullComponent (G : SimpleGraph X) (S : Set X) (D : ℕ)
    (c : (G.induce Sᶜ).ConnectedComponent) : Prop :=
  ∀ z : c.supp, Nat.card (G.neighborSet z.val.val)=D

def freeFull (G : SimpleGraph X) (S : Set X) (D : ℕ) (A : RootAllocation G S) :
    Set (G.induce Sᶜ).ConnectedComponent :=
  {c | c∉Set.range A.place ∧ allFullComponent G S D c}

/-- Always use a low-degree exposed vertex if an unassigned component offers one. -/
theorem choose_allocation_holes (G : SimpleGraph X) (S : Set X) (A : RootAllocation G S) (D : ℕ) :
    ∃ pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp,
      (∀ a : S, G.Adj a.val (pick (A.place a)).val.val) ∧
      ∀ c, c∉Set.range A.place →
        (Nat.card (G.neighborSet (pick c).val.val)=D ↔ allFullComponent G S D c) := by
  classical
  have chooseOne (c : (G.induce Sᶜ).ConnectedComponent) :
      ∃ u : c.supp, (∀ a : S, A.place a=c → G.Adj a.val u.val.val) ∧
        (c∉Set.range A.place → (Nat.card (G.neighborSet u.val.val)=D ↔ allFullComponent G S D c)) := by
    by_cases used : c∈Set.range A.place
    · obtain ⟨a,rfl⟩ := used
      obtain ⟨u,edge⟩ := A.link a
      refine ⟨u,fun b eq => ?_,fun no => (no ⟨a,rfl⟩).elim⟩
      exact A.place.injective eq ▸ edge
    · have no (a : S) (eq : A.place a=c) : False := used ⟨a,eq⟩
      by_cases all : allFullComponent G S D c
      · let u : c.supp := Classical.choice c.nonempty_supp.to_subtype
        exact ⟨u,fun a eq => (no a eq).elim,fun _ => ⟨fun _ => all,fun _ => all u⟩⟩
      · change ¬∀ z : c.supp, Nat.card (G.neighborSet z.val.val)=D at all
        obtain ⟨u,low⟩ := Classical.not_forall.mp all
        exact ⟨u,fun a eq => (no a eq).elim,fun _ => ⟨fun high => (low high).elim,fun full => full u⟩⟩
  exact ⟨fun c => (chooseOne c).choose,fun a => (chooseOne (A.place a)).choose_spec.1 a rfl,
    fun c => (chooseOne c).choose_spec.2⟩
#print axioms choose_allocation_holes
end JSP452Audit.StarHost
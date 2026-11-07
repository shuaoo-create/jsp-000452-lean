import RetainedBoundary
import PaddedGraph

namespace JSP452Audit.Padded
open SimpleGraph

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

/-- Retained components meeting the optional/global clique. -/
def Spec.retainedPoolComponents (W : Finset P.Vertex) :
    Set (P.graph.induce (W : Set P.Vertex)).ConnectedComponent :=
  {c | ∃ (t : P.Token) (ht : (Sum.inr t : P.Vertex) ∈ W), P.inPool t ∧
    (P.graph.induce (W : Set P.Vertex)).connectedComponentMk ⟨.inr t,ht⟩ = c}

theorem Spec.retainedPool_ncard_le_one (W : Finset P.Vertex) :
    (P.retainedPoolComponents W).ncard ≤ 1 := by
  classical
  apply (Set.ncard_le_one (s := _)).mpr
  rintro _ ⟨t,ht,pt,rfl⟩ _ ⟨u,hu,pu,rfl⟩
  by_cases e : t = u
  · subst u; rfl
  · apply ConnectedComponent.sound
    apply SimpleGraph.Adj.reachable
    exact ⟨pt,pu,e⟩

/-- A global-token neighbor can only be another pool token. -/
theorem Spec.global_retained_le_one (W : Finset P.Vertex)
    (i : Fin (if P.extra then 1 else 0)) :
    (retainedNeighborComponents P.graph W (P.globalToken i)).ncard ≤ 1 := by
  apply le_trans (Set.ncard_le_ncard (t := P.retainedPoolComponents W) ?_) (P.retainedPool_ncard_le_one W)
  rintro _ ⟨⟨s | t,h⟩,edge,rfl⟩
  · exact (P.not_stub_adj_global s i edge.symm).elim
  · exact ⟨t,h,edge.2.1,rfl⟩

/-- Uniqueness of the other end of a cross-stub edge. -/
theorem Spec.cross_partner_unique {s a b : P.Stub} (ha : P.cross s a) (hb : P.cross s b) : a = b := by
  obtain ⟨v, u | i⟩ := s <;> obtain ⟨w, a | j⟩ := a <;> obtain ⟨z,b | k⟩ := b
  all_goals first | exact False.elim ha | exact False.elim hb | skip
  obtain ⟨h₁,h₂⟩ := ha
  obtain ⟨h₃,h₄⟩ := hb
  have hown : z = w := h₄.trans h₂.symm
  cases hown
  have ab : a = b := Subtype.ext (h₁.symm.trans h₃)
  cases ab; rfl

private def crossComponents (W : Finset P.Vertex) (s : P.Stub) :
    Set (P.graph.induce (W : Set P.Vertex)).ConnectedComponent :=
  {c | ∃ (r : P.Stub) (hr : (Sum.inl r : P.Vertex) ∈ W), P.cross s r ∧
    (P.graph.induce (W : Set P.Vertex)).connectedComponentMk ⟨.inl r,hr⟩ = c}

private def ownedComponents (W : Finset P.Vertex) (v : V) :
    Set (P.graph.induce (W : Set P.Vertex)).ConnectedComponent :=
  {c | ∃ (t : P.Token) (ht : (Sum.inr t : P.Vertex) ∈ W), P.ownedAt t v ∧
    (P.graph.induce (W : Set P.Vertex)).connectedComponentMk ⟨.inr t,ht⟩ = c}

private theorem crossComponents_le_one (W : Finset P.Vertex) (s : P.Stub) :
    (crossComponents P W s).ncard ≤ 1 := by
  apply (Set.ncard_le_one (s := _)).mpr
  rintro _ ⟨a,ha,e₁,rfl⟩ _ ⟨b,hb,e₂,rfl⟩
  have := P.cross_partner_unique e₁ e₂
  subst b; rfl

private theorem stub_boundary (W : Finset P.Vertex) (s : P.Stub) :
    retainedNeighborComponents P.graph W (.inl s) =
      crossComponents P W s ∪ ownedComponents P W s.1 := by
  ext c
  constructor
  · rintro ⟨⟨a | t,h⟩,edge,eq⟩
    · exact Or.inl ⟨a,h,edge,eq⟩
    · exact Or.inr ⟨t,h,edge,eq⟩
  · rintro (⟨a,h,edge,eq⟩ | ⟨t,h,edge,eq⟩)
    · exact ⟨⟨.inl a,h⟩,edge,eq⟩
    · exact ⟨⟨.inr t,h⟩,edge,eq⟩

/-- Without a surviving local token only the unique opposite stub can contribute. -/
theorem Spec.stub_retained_no_token_le_one (W : Finset P.Vertex) (s : P.Stub)
    (none : ∀ t : P.Token, P.ownedAt t s.1 → (Sum.inr t : P.Vertex) ∉ W) :
    (retainedNeighborComponents P.graph W (.inl s)).ncard ≤ 1 := by
  rw [stub_boundary]
  have empty : ownedComponents P W s.1 = ∅ := Set.eq_empty_iff_forall_notMem.mpr (by
    rintro _ ⟨t,ht,own,_⟩
    exact none t own ht)
  rw [empty,Set.union_empty]
  exact crossComponents_le_one P W s

/-- Any retained stub in this block joins all retained local tokens by a
two-edge path. The unique opposite stub contributes at most one further component. -/
theorem Spec.stub_retained_with_local_stub_le_two (W : Finset P.Vertex) (s u : P.Stub)
    (same : u.1 = s.1) (anchor : (Sum.inl u : P.Vertex) ∈ W) :
    (retainedNeighborComponents P.graph W (.inl s)).ncard ≤ 2 := by
  rw [stub_boundary]
  have owned : (ownedComponents P W s.1).ncard ≤ 1 := by
    apply (Set.ncard_le_one (s := _)).mpr
    rintro _ ⟨t,ht,ot,rfl⟩ _ ⟨v,hv,ov,rfl⟩
    let Y := P.graph.induce (W : Set P.Vertex)
    let z : ↥(W : Set P.Vertex) := ⟨.inl u,anchor⟩
    have left : Y.Adj ⟨.inr t,ht⟩ z := by change P.ownedAt t u.1; rwa [same]
    have right : Y.Adj z ⟨.inr v,hv⟩ := by change P.ownedAt v u.1; rwa [same]
    exact ConnectedComponent.sound (left.reachable.trans right.reachable)
  have add := Set.ncard_union_le (crossComponents P W s) (ownedComponents P W s.1)
  have cross := crossComponents_le_one P W s
  omega

/-- A token with a local owner has only that owner. -/
theorem Spec.ownedAt_unique {t : P.Token} {v w : V} (hv : P.ownedAt t v)
    (hw : P.ownedAt t w) : v = w := by
  obtain (a | b) | g := t
  · exact hv.symm.trans hw
  · exact hv.symm.trans hw
  · exact hv.elim

private def stubComponents (W : Finset P.Vertex) (v : V) :
    Set (P.graph.induce (W : Set P.Vertex)).ConnectedComponent :=
  {c | ∃ (s : P.Stub) (hs : (Sum.inl s : P.Vertex) ∈ W), s.1 = v ∧
    (P.graph.induce (W : Set P.Vertex)).connectedComponentMk ⟨.inl s,hs⟩ = c}

private theorem token_boundary_subset (W : Finset P.Vertex) (t : P.Token) (v : V)
    (own : P.ownedAt t v) :
    retainedNeighborComponents P.graph W (.inr t) ⊆ stubComponents P W v ∪ P.retainedPoolComponents W := by
  rintro _ ⟨⟨s | u,hw⟩,edge,rfl⟩
  · exact Or.inl ⟨s,hw,P.ownedAt_unique edge own,rfl⟩
  · exact Or.inr ⟨u,hw,edge.2.1,rfl⟩

/-- If the local block retains no stubs, activating an owned token can only
touch the pool clique. This also applies to a mandatory token. -/
theorem Spec.token_retained_no_stub_le_one (W : Finset P.Vertex) (t : P.Token) (v : V)
    (own : P.ownedAt t v)
    (none : ∀ s : P.Stub, s.1 = v → (Sum.inl s : P.Vertex) ∉ W) :
    (retainedNeighborComponents P.graph W (.inr t)).ncard ≤ 1 := by
  have empty : stubComponents P W v = ∅ := Set.eq_empty_iff_forall_notMem.mpr (by
    rintro _ ⟨s,hs,hs',_⟩; exact none s hs' hs)
  have sub := token_boundary_subset P W t v own
  rw [empty,Set.empty_union] at sub
  exact (Set.ncard_le_ncard sub).trans (P.retainedPool_ncard_le_one W)

/-- All surviving stubs of v use the retained token u as a common neighbor;
the clique contributes at most one other component to a token at v. -/
theorem Spec.token_retained_with_local_token_le_two (W : Finset P.Vertex)
    (t u : P.Token) (v : V) (own : P.ownedAt t v) (other : P.ownedAt u v)
    (anchor : (Sum.inr u : P.Vertex) ∈ W) :
    (retainedNeighborComponents P.graph W (.inr t)).ncard ≤ 2 := by
  have stubs : (stubComponents P W v).ncard ≤ 1 := by
    apply (Set.ncard_le_one (s := _)).mpr
    rintro _ ⟨a,ha,oa,rfl⟩ _ ⟨b,hb,ob,rfl⟩
    let Y := P.graph.induce (W : Set P.Vertex)
    let z : ↥(W : Set P.Vertex) := ⟨.inr u,anchor⟩
    have left : Y.Adj ⟨.inl a,ha⟩ z := by change P.ownedAt u a.1; rwa [oa]
    have right : Y.Adj z ⟨.inl b,hb⟩ := by change P.ownedAt u b.1; rwa [ob]
    exact ConnectedComponent.sound (left.reachable.trans right.reachable)
  have sub := Set.ncard_le_ncard (token_boundary_subset P W t v own)
  have a := Set.ncard_union_le (stubComponents P W v) (P.retainedPoolComponents W)
  have pool := P.retainedPool_ncard_le_one W
  omega

#print axioms Spec.ownedAt_unique
#print axioms Spec.token_retained_no_stub_le_one
#print axioms Spec.token_retained_with_local_token_le_two
#print axioms Spec.retainedPool_ncard_le_one
#print axioms Spec.global_retained_le_one
#print axioms Spec.cross_partner_unique
#print axioms Spec.stub_retained_no_token_le_one
#print axioms Spec.stub_retained_with_local_stub_le_two
end JSP452Audit.Padded

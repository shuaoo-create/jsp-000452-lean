import CoreLanguage
namespace JSP452Audit.Padded
open SimpleGraph

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

/-- Components incident to at least one retained optional/global token.
    Every such token lies in the same clique. -/
def Spec.canonPoolComponents (S T : Set V) :
    Set (P.canonGraph S T).ConnectedComponent :=
  {c | ∃ (z : P.CanonVertex S T) (a : P.Token), z.val=.inr a ∧
    P.inPool a ∧ (P.canonGraph S T).connectedComponentMk z=c}

theorem Spec.canonPool_at_most_one (S T : Set V) :
    (P.canonPoolComponents S T).ncard ≤ 1 := by
  apply (Set.ncard_le_one (s := P.canonPoolComponents S T)).mpr
  rintro _ ⟨⟨_,ka⟩,a,rfl,ha,rfl⟩ _ ⟨⟨_,kb⟩,b,rfl,hb,rfl⟩
  by_cases eq : a=b
  · subst b; rfl
  · apply ConnectedComponent.sound
    exact SimpleGraph.Adj.reachable (show P.graph.Adj (.inr a) (.inr b) from ⟨ha,hb,eq⟩)

omit [Fintype V] [DecidableRel P.G.Adj] in
private theorem hasOriginal {S T : Set V} (v : V) (hs : v∉S) (ht : v∉T) :
    ∃ C : P.CoreComponent S T, P.inOriginal C v := by
  let u : P.CorePoint S T := ⟨v,fun h => h.elim hs ht⟩
  exact ⟨(P.coreGraph S T).connectedComponentMk u,u.property,rfl⟩

/-- No odd component disappears between the geometric descriptions.
    The T--T case is explicitly excluded by its verified two-point support. -/
theorem Spec.canonical_odd_covered {S T : Set V} (dis : Disjoint S T)
    (c : (P.canonGraph S T).ConnectedComponent) (odd : Odd c.supp.ncard) :
    (∃ z : P.CanonVertex S T, P.singletonLabel S T z.val ∧ z ∈ c.supp) ∨
    (∃ (C : P.CoreComponent S T) (z : P.CanonVertex S T), P.onCore C z.val ∧ z∈c.supp) ∨
    c ∈ P.canonPoolComponents S T := by
  classical
  obtain ⟨z,mem⟩ := c.nonempty_supp
  rcases z with ⟨⟨v,w | j⟩ | ((a | b) | g),kept⟩
  · have ns : v ∉ S := (P.mem_canonicalKept S T _).mp kept
    by_cases ht : v ∈ T
    · by_cases ws : w.val ∈ S
      · exact Or.inl ⟨⟨_,kept⟩,⟨ht,ws⟩,mem⟩
      · by_cases wt : w.val ∈ T
        · have eq : (P.canonGraph S T).connectedComponentMk (P.canonicalTStub dis ht w.property) = c := mem
          have count := P.canonical_TT_ncard dis ht wt w.property
          rw [eq] at count
          have := Nat.odd_iff.mp odd
          omega
        · obtain ⟨C,h⟩ := hasOriginal P w.val ws wt
          exact Or.inr (Or.inl ⟨C,⟨_,kept⟩,Or.inr ⟨ht,h⟩,mem⟩)
    · obtain ⟨C,h⟩ := hasOriginal P v ns ht
      exact Or.inr (Or.inl ⟨C,⟨_,kept⟩,Or.inl h,mem⟩)
  · have ns : v ∉ S := (P.mem_canonicalKept S T _).mp kept
    by_cases ht : v ∈ T
    · exact Or.inl ⟨⟨_,kept⟩,ht,mem⟩
    · obtain ⟨C,h⟩ := hasOriginal P v ns ht
      exact Or.inr (Or.inl ⟨C,⟨_,kept⟩,h,mem⟩)
  · have nt : a.1 ∉ T := (P.mem_canonicalKept S T _).mp kept
    by_cases hs : a.1 ∈ S
    · exact Or.inl ⟨⟨_,kept⟩,hs,mem⟩
    · obtain ⟨C,h⟩ := hasOriginal P a.1 hs nt
      exact Or.inr (Or.inl ⟨C,⟨_,kept⟩,h,mem⟩)
  · exact Or.inr (Or.inr ⟨⟨_,kept⟩,.inl (.inr b),rfl,trivial,mem⟩)
  · exact Or.inr (Or.inr ⟨⟨_,kept⟩,.inr g,rfl,trivial,mem⟩)

#print axioms Spec.canonical_odd_covered
end JSP452Audit.Padded

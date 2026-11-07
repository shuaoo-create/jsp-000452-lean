import CoreLanguage

namespace JSP452Audit.Padded
open SimpleGraph
variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

omit [Fintype V] [DecidableRel P.G.Adj] in
private theorem original_neighbor {S T : Set V} {C : P.CoreComponent S T} {v w : V}
    (own : P.inOriginal C v) (e : P.G.Adj v w) (ws : w ∉ S) (wt : w ∉ T) :
    P.inOriginal C w := by
  obtain ⟨hv,mem⟩ := own
  have hw : w ∈ ((S ∪ T)ᶜ : Set V) := fun h => h.elim ws wt
  have adj : (P.coreGraph S T).Adj ⟨v,hv⟩ ⟨w,hw⟩ := e
  exact ⟨hw,(C.mem_supp_congr_adj adj).mp mem⟩

private theorem token_over {S T : Set V} {C : P.CoreComponent S T} {v : V}
    (own : P.inOriginal C v) (t : P.Token) (atV : P.ownedAt t v) :
    P.onCore C (.inr t) := by
  rcases t with (a | b) | g
  · change a.1 = v at atV
    change P.inOriginal C a.1
    rwa [atV]
  · change b.1 = v at atV
    change P.inOriginal C b.1
    rwa [atV]
  · exact atV.elim

private theorem stub_over {S T : Set V} {C : P.CoreComponent S T}
    (s : P.Stub) (own : P.inOriginal C s.1) : P.onCore C (.inl s) := by
  rcases s with ⟨v,w | i⟩
  · exact Or.inl own
  · exact own

/-- In a tight original component no local optional token exists. Thus its
entire retained fiber, including the T-stubs directed into it, is edge-closed. -/
theorem Spec.coreTight_closed {S T : Set V} {C : P.CoreComponent S T} (tight : P.coreTight C)
    {z w : P.CanonVertex S T} (core : P.onCore C z.val) (adj : (P.canonGraph S T).Adj z w) :
    P.onCore C w.val := by
  rcases z with ⟨⟨v,u | i⟩ | ((a | b) | g),hz⟩
  · rcases core with own | ⟨ht,other⟩
    · rcases w with ⟨⟨v',u' | i'⟩ | t,hw⟩
      · have rev : v' = u.val := adj.2
        have back : u'.val = v := adj.1.symm
        by_cases ht' : v' ∈ T
        · exact Or.inr ⟨ht',back ▸ own⟩
        · have kept := (P.mem_canonicalKept S T _).mp hw
          exact Or.inl (original_neighbor P own (rev ▸ u.property) kept ht')
      · exact adj.elim
      · exact token_over P own t adj
    · have opposite := P.canonical_real_neighbor u.property ht w adj
      rw [opposite]
      exact Or.inl other
  · rcases w with ⟨s | t,hw⟩
    · rcases s with ⟨v',u' | i'⟩ <;> exact adj.elim
    · exact token_over P core t adj
  · rcases w with ⟨s | t,hw⟩
    · have eq : a.1 = s.1 := adj
      exact stub_over P s (eq ▸ core)
    · exact adj.1.elim
  · obtain ⟨hv,member⟩ := core
    have zero := tight ⟨b.1,hv⟩ member
    have existsIndex := b.2.isLt
    change P.optionalCount b.1 = 0 at zero
    omega
  · exact core.elim

/-- A non-tight component has an actual retained optional token in the pool,
with an original owner in the component. This is a witness in the canonical graph. -/
theorem Spec.exists_core_optional_of_not_tight {S T : Set V} (C : P.CoreComponent S T)
    (loose : ¬ P.coreTight C) :
    ∃ (a : P.Optional) (z : P.CanonVertex S T), P.inOriginal C a.1 ∧
      z.val = P.optional a ∧ P.onCore C z.val ∧ P.inPool (.inl (.inr a)) := by
  classical
  unfold Spec.coreTight at loose
  push Not at loose
  obtain ⟨u,mem,hpos⟩ := loose
  let a : P.Optional := ⟨u.val,⟨0,Nat.pos_of_ne_zero hpos⟩⟩
  have own : P.inOriginal C a.1 := ⟨u.property,mem⟩
  have kept : P.keptBy S T (P.optional a) := (P.notST_of_inOriginal own).2
  exact ⟨a,P.canonicalPoint _ kept,own,rfl,own,True.intro⟩

#print axioms Spec.coreTight_closed
#print axioms Spec.exists_core_optional_of_not_tight
end JSP452Audit.Padded

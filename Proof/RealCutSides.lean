import PreferredUnionCrossing

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem neighbor_from_connected_side (G : SimpleGraph X) (conn : G.Preconnected)
    (u : X) (A : Set X) (inside : A.Nonempty) (outside : u ∉ A)
    (closed : ∀ a ∈ A, ∀ v, G.Adj a v → v = u ∨ v ∈ A) :
    ∃ a ∈ A, G.Adj u a := by
  by_contra! none
  have stays {v w : X} (path : G.Walk v w) : v ∈ A → w ∈ A := by
    induction path with
    | nil => exact id
    | cons edge _ ih =>
      intro hv
      apply ih
      rcases closed _ hv _ edge with h | h
      · exact False.elim (none _ hv (h ▸ edge.symm))
      · exact h
  obtain ⟨v,hv⟩ := inside
  obtain ⟨path⟩ := conn v u
  exact outside (stays path hv)

/-- The two genuine sides after a separating deletion are nonempty cliques.
The removed vertex has a neighbor on each side in the original graph. -/
theorem split_cut_into_two_cliques (G : SimpleGraph X) (conn : G.Preconnected)
    (small : NoIndependentTriple G) (u : X) (cut : ¬ (G.induce {v | v ≠ u}).Preconnected) :
    ∃ A B : Set X, A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      A ∪ B = {v | v ≠ u} ∧ G.IsClique A ∧ G.IsClique B ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) ∧
      (∃ a ∈ A, G.Adj u a) ∧ (∃ b ∈ B, G.Adj u b) := by
  classical
  let K := G.induce {v | v ≠ u}
  change ¬ ∀ x y, K.Reachable x y at cut
  push Not at cut
  obtain ⟨x,y,apart⟩ := cut
  let A : Set X := {v | ∃ h : v ≠ u, K.Reachable x ⟨v,h⟩}
  let B : Set X := {v | v ≠ u ∧ v ∉ A}
  have xa : x.val ∈ A := ⟨x.property,Reachable.refl _⟩
  have yb : y.val ∈ B := ⟨y.property,fun h => apart h.choose_spec⟩
  have separate (a : X) (ha : a ∈ A) (b : X) (hb : b ∈ B) : ¬ G.Adj a b := by
    obtain ⟨an,reach⟩ := ha
    intro edge
    exact hb.2 ⟨hb.1,reach.trans (show K.Adj ⟨a,an⟩ ⟨b,hb.1⟩ from edge).reachable⟩
  have dis : Disjoint A B := Set.disjoint_left.mpr (fun _ ha hb => hb.2 ha)
  have cover : A ∪ B = {v | v ≠ u} := by
    ext v
    constructor
    · rintro (ha|hb)
      · exact ha.choose
      · exact hb.1
    · intro hv
      by_cases ha : v ∈ A
      · exact Or.inl ha
      · exact Or.inr ⟨hv,ha⟩
  have clique (S T : Set X) (d : Disjoint S T) (other : T.Nonempty)
      (sep : ∀ a ∈ S, ∀ b ∈ T, ¬ G.Adj a b) : G.IsClique S := by
    obtain ⟨v,hv⟩ := other
    intro a ha b hb ne
    have diffA : a ≠ v := fun eq => Set.disjoint_left.mp d ha (eq.symm ▸ hv)
    have diffB : b ≠ v := fun eq => Set.disjoint_left.mp d hb (eq.symm ▸ hv)
    exact (small a b v ne diffA diffB).resolve_right
      (fun h => h.elim (sep a ha v hv) (sep b hb v hv))
  have closedA (a : X) (ha : a ∈ A) (v : X) (edge : G.Adj a v) : v = u ∨ v ∈ A := by
    by_contra! h
    exact separate a ha v ⟨h.1,h.2⟩ edge
  have closedB (b : X) (hb : b ∈ B) (v : X) (edge : G.Adj b v) : v = u ∨ v ∈ B := by
    by_cases eq : v=u
    · exact Or.inl eq
    · exact Or.inr ⟨eq,fun ha => separate v ha b hb edge.symm⟩
  exact ⟨A,B,⟨_,xa⟩,⟨_,yb⟩,dis,cover,clique A B dis ⟨_,yb⟩ separate,
    clique B A dis.symm ⟨_,xa⟩ (fun b hb a ha e => separate a ha b hb e.symm),
    separate,neighbor_from_connected_side G conn u A ⟨_,xa⟩ (fun h => h.choose rfl) closedA,
    neighbor_from_connected_side G conn u B ⟨_,yb⟩ (fun h => h.1 rfl) closedB⟩

#print axioms split_cut_into_two_cliques
end JSP452Audit.StarHost

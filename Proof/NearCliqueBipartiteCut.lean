import BipartiteFullDegree
import OnePreferredPart
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Edges internal to a side can be omitted provided no vertex attaining d
is incident to one of them. The matching is returned in the original graph. -/
theorem remainder_via_bipartite_cut (Q : SimpleGraph X) (L : Set X) (d : ℕ) (pos : 0<d)
    (cap : ∀x,Nat.card (Q.neighborSet x)≤d)
    (full : ∀x,Nat.card (Q.neighborSet x)=d → ∀y,Q.Adj x y → (x∈L ↔ y∉L)) :
    admits_matching_remainder Q d := by
  classical
  let H : SimpleGraph X := {
    Adj := fun a b => Q.Adj a b ∧ (a∈L ↔ b∉L)
    symm := ⟨fun _ _ h => ⟨h.1.symm,by have eq := h.2;tauto⟩⟩
    loopless := ⟨fun v edge => edge.1.ne rfl⟩ }
  have hcap (x:X) : Nat.card (H.neighborSet x)≤d := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_le_ncard (show H.neighborSet x⊆Q.neighborSet x from fun _ h => h.1)).trans
      ((Nat.card_coe_set_eq _).symm.le.trans (cap x))
  obtain ⟨M,hm,all⟩ := bipartite_full_degree_matching H L d pos hcap (fun _ _ e => e.2)
  let J : Q.Subgraph := {
    verts := M.verts
    Adj := M.Adj
    adj_sub := fun h => (M.adj_sub h).1
    edge_vert := M.edge_vert
    symm := M.symm }
  apply admits_remainder_of_full_cover Q d pos cap J (show J.IsMatching from hm)
  intro x top
  apply all x
  have same : H.neighborSet x=Q.neighborSet x := by
    ext y
    exact ⟨fun h => h.1,fun edge => ⟨edge,full x top y edge⟩⟩
  rw [same,top]

/-- If at most one internal edge is missing, deleting two labels can force
each remaining vertex to lose both of them as neighbours. -/
theorem two_clique_deletions (Q : SimpleGraph X) (B : Set X) (three : 3≤B.ncard)
    (miss : (Q.induce B)ᶜ.edgeSet.ncard≤1) :
    ∃a∈B,∃b∈B,a≠b ∧ ∀v∈B,v≠a → v≠b → Q.Adj v a ∧ Q.Adj v b := by
  classical
  let G := Q.induce B
  by_cases all : G.IsClique Set.univ
  · obtain ⟨a,b,ha,hb,ne⟩ := (Set.one_lt_ncard_iff (Set.toFinite B)).mp (by omega)
    refine ⟨a,ha,b,hb,ne,?_⟩
    intro v hv va vb
    exact ⟨all (Set.mem_univ (⟨v,hv⟩:B)) (Set.mem_univ (⟨a,ha⟩:B)) (fun eq => va (congrArg Subtype.val eq)),
      all (Set.mem_univ (⟨v,hv⟩:B)) (Set.mem_univ (⟨b,hb⟩:B)) (fun eq => vb (congrArg Subtype.val eq))⟩
  obtain ⟨a,b,ne,nonedge⟩ : ∃a b:B,a≠b ∧ ¬G.Adj a b := by
    by_contra! no
    exact all (fun {a} _ {b} _ ab => no a b ab)
  have missing : s(a,b) ∈ Gᶜ.edgeSet := ⟨ne,nonedge⟩
  refine ⟨a.val,a.property,b.val,b.property,(fun eq => ne (Subtype.ext eq)),?_⟩
  intro v hv va vb
  let u : B := ⟨v,hv⟩
  have ua : u≠a := fun eq => va (congrArg Subtype.val eq)
  have ub : u≠b := fun eq => vb (congrArg Subtype.val eq)
  have yes (t:B) (ut:u≠t) : G.Adj u t := by
    by_contra no
    have he : s(u,t)∈Gᶜ.edgeSet := ⟨ut,no⟩
    have eq := (Set.ncard_le_one (Set.toFinite _)).mp miss _ he _ missing
    rcases Sym2.eq_iff.mp eq with ⟨h,_⟩|⟨h,_⟩
    · exact ua h
    · exact ub h
  exact ⟨yes a ua,yes b ub⟩

#print axioms remainder_via_bipartite_cut
#print axioms two_clique_deletions
end JSP452Audit.StarHost

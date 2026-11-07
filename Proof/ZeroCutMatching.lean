import ZeroOriginalLabels
import CliquePairs
import IndependentLayerPrice
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Realize a matching covering an even clique and two disjoint genuine
edges outside it. Empty clique permitted. -/
theorem cover_even_clique_and_two_edges (H : SimpleGraph X) (C : Set X) (cl : H.IsClique C)
    (even : Even C.ncard) (a b i j : X) (ai : H.Adj a i) (bj : H.Adj b j)
    (outside : ∀x,x∈({a,i,b,j} : Set X) → x∉C)
    (apart : Disjoint ({a,i} : Set X) ({b,j} : Set X)) :
    ∃M : H.Subgraph,M.IsMatching ∧ C⊆M.verts ∧ a∈M.verts ∧ b∈M.verts := by
  classical
  let e : C ↪ X := ⟨Subtype.val,Subtype.val_injective⟩
  obtain ⟨P,mP,supp⟩ := JSP452Audit.Padded.existsMatchingOnEvenClique H e
    (fun {u v} ne => cl u.property v.property (fun eq => ne (Subtype.ext eq)))
    (by rwa [Nat.card_coe_set_eq])
  have pc : P.verts=C := supp.trans (by ext x; exact ⟨fun ⟨y,eq⟩ => eq ▸ y.property,
    fun hx => ⟨⟨x,hx⟩,rfl⟩⟩)
  let L := H.subgraphOfAdj ai
  let R := H.subgraphOfAdj bj
  have l : L.verts={a,i} := rfl
  have r : R.verts={b,j} := rfl
  have mlr := JSP452Audit.Padded.matching_sup_of_disjoint_verts H (Subgraph.IsMatching.subgraphOfAdj ai)
    (Subgraph.IsMatching.subgraphOfAdj bj) apart
  have sep : Disjoint P.verts (L⊔R).verts := by
    rw [pc,Subgraph.verts_sup,l,r]
    apply Set.disjoint_left.mpr
    rintro x cx ((eq|eq)|(eq|eq))
    · exact outside x (Or.inl eq) cx
    · exact outside x (Or.inr (Or.inl (Set.mem_singleton_iff.mp eq))) cx
    · exact outside x (Or.inr (Or.inr (Or.inl eq))) cx
    · exact outside x (Or.inr (Or.inr (Or.inr eq))) cx
  refine ⟨P⊔(L⊔R),JSP452Audit.Padded.matching_sup_of_disjoint_verts H mP mlr sep,?_,?_,?_⟩
  · intro x hx; exact Or.inl (pc ▸ hx)
  · exact Or.inr (Or.inl (show a∈L.verts from Or.inl rfl))
  · exact Or.inr (Or.inr (show b∈R.verts from Or.inl rfl))

/-- At most D−1 full degree, all full vertices on the even clique or one
of the two retained holes, yields an actual remainder certificate. -/
theorem admits_remainder_clique_two_edges (H : SimpleGraph X) (D : ℕ) (large : 2≤D) (C : Set X)
    (cl : H.IsClique C) (even : Even C.ncard) (a b i j : X)
    (ai : H.Adj a i) (bj : H.Adj b j)
    (out : ∀x,x∈({a,i,b,j} : Set X) → x∉C)
    (apart : Disjoint ({a,i} : Set X) ({b,j} : Set X))
    (cap : ∀x,Nat.card (H.neighborSet x)≤D-1)
    (full : ∀x,Nat.card (H.neighborSet x)=D-1 → x∈C ∨ x=a ∨ x=b) :
    admits_matching_remainder H (D-1) := by
  obtain ⟨M,hm,clique,aa,bb⟩ := cover_even_clique_and_two_edges H C cl even a b i j ai bj out apart
  apply admits_remainder_of_full_cover H (D-1) (by omega) cap M hm
  intro x hx
  rcases full x hx with inc|eq|eq
  · exact clique inc
  · exact eq ▸ aa
  · exact eq ▸ bb

#print axioms admits_remainder_clique_two_edges
end JSP452Audit.StarHost

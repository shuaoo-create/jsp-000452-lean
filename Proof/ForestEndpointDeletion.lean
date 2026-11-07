import StrictClosedUnionEndpointPair
import TightDeletesRank
namespace JSP452Audit.StarHost
open SimpleGraph

def ForestMatchingEndpoint {X : Type*} {s : ℕ} (G : SimpleGraph X) (n : Fin s→ℕ) (q : ℕ) : Prop :=
  ∀R:SimpleGraph X,R≤G → (forest n).IsContained R ∨ q≤matchingEdges (G \ R)

theorem endpoint_survives_cover {X : Type*} [Finite X] {s q : ℕ} (G : SimpleGraph X)
    (n : Fin s→ℕ) (pn : ∀i,1≤n i) (endpt : ForestMatchingEndpoint G n q)
    (A : Set X) (budget : A.ncard<q) : (forest n).IsContained (G.induce Aᶜ) := by
  let R : SimpleGraph X := {
    Adj x y := G.Adj x y ∧ x∉A ∧ y∉A
    symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
    loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩ }
  have bound := matchingEdges_le_cover_card (G \ R) A (by
    intro x y e
    by_contra! h
    exact e.2 ⟨e.1,h.1,h.2⟩)
  obtain ⟨f⟩ := (endpt R (fun _ _ h => h.1)).resolve_right (by omega)
  have inside (z:Vertices n) : f z∉A := by
    obtain ⟨w,edge⟩ := forest_has_neighbor n pn z
    exact (f.toHom.map_rel' edge).2.1
  let send (z:Vertices n) : ↥(Aᶜ : Set X) := ⟨f z,inside z⟩
  refine ⟨{ toHom := {toFun := send, map_rel' := fun e => (f.toHom.map_rel' e).1}
            injective' := ?_ }⟩
  exact fun _ _ eq => f.injective (congrArg Subtype.val eq)

theorem tight_endpoint_barrier_lt {X : Type*} [Finite X] {s q d : ℕ} (G : SimpleGraph X)
    (n : Fin s→ℕ) (pn : ∀i,1≤n i) (endpt : ForestMatchingEndpoint G n q)
    (pos : 0<d) (hq : 0<q) (account : matchingEdges G+d+1=s+q)
    (S : Set X) (tight : IsTightBarrier G S) : S.ncard<q-1 := by
  by_contra! enough
  obtain ⟨A,sub,card⟩ := Set.exists_subset_card_eq enough
  have copy := endpoint_survives_cover G n pn endpt A (by omega)
  have need := forest_copy_matching _ n pn copy
  rw [Fintype.card_fin] at need
  have split := tight_deletes_rank G S A tight sub
  omega

#print axioms endpoint_survives_cover
#print axioms tight_endpoint_barrier_lt
end JSP452Audit.StarHost

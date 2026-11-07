import SavingComponentColoring
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem rank_component_sides (G : SimpleGraph X) (S : Set X)
    (closed : ∀x∈S,∀y∈Sᶜ,¬G.Adj x y) :
    matchingEdges G=matchingEdges (G.induce S)+matchingEdges (G.induce Sᶜ) := by
  have split := rank_split_regions G Set.univ S Sᶜ (Set.union_compl_self _) disjoint_compl_right closed
  rw [rank_eq_of_graph_iso (induceUnivIso G)] at split
  exact split

/-- Blue keeps exactly the edges of component c. Red keeps all other
edges of the actual host. Their matching numbers add without slack. -/
theorem component_split_forcing_ranks (G : SimpleGraph X) (c : G.ConnectedComponent) :
    ∃R : SimpleGraph X,R≤G ∧ matchingEdges R + matchingEdges c.toSimpleGraph=matchingEdges G ∧
      matchingEdges (G \ R)=matchingEdges c.toSimpleGraph := by
  let S := c.supp
  let R : SimpleGraph X := {
    Adj x y := G.Adj x y ∧ x∉S ∧ y∉S
    symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
    loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩ }
  have sub : R≤G := fun _ _ h => h.1
  have sep : ∀x∈S,∀y∈Sᶜ,¬G.Adj x y := fun _ hx _ hy e => hy ((c.mem_supp_congr_adj e).mp hx)
  have total := rank_component_sides G S sep
  have red := rank_component_sides R S (fun x hx y hy e => sep x hx y hy (sub e))
  have blue := rank_component_sides (G \ R) S (fun x hx y hy e => sep x hx y hy e.1)
  have r0 : R.induce S=⊥ := by
    ext x y; exact ⟨fun e => (e.2.1 x.property).elim,False.elim⟩
  have r1 : R.induce Sᶜ=G.induce Sᶜ := by
    ext x y; exact ⟨fun e => e.1,fun e => ⟨e,x.property,y.property⟩⟩
  have b0 : (G \ R).induce Sᶜ=⊥ := by
    ext x y; exact ⟨fun e => (e.2 ⟨e.1,x.property,y.property⟩).elim,False.elim⟩
  have b1 : (G \ R).induce S=G.induce S := by
    ext x y; exact ⟨fun e => e.1,fun e => ⟨e,fun r => r.2.1 x.property⟩⟩
  rw [r0,r1,matchingEdges_bot,Nat.zero_add] at red
  rw [b0,b1,matchingEdges_bot,Nat.add_zero] at blue
  change matchingEdges G=matchingEdges c.toSimpleGraph+matchingEdges (G.induce Sᶜ) at total
  exact ⟨R,sub,by omega,blue⟩

#print axioms component_split_forcing_ranks
end JSP452Audit.StarHost
